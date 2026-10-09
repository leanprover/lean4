// Lean compiler output
// Module: Std.Time.Zoned.Database.TzIf
// Imports: public import Init.Data.Range.Polymorphic.Iterators public import Std.Internal.Parsec import Init.Data.Int.Repr import Init.Data.ByteArray.Extra
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
uint64_t l_ByteArray_toUInt64BE_x21(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_string_length(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint32_t lean_uint8_to_uint32(uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value),LEAN_SCALAR_PTR_LITERAL(28, 95, 20, 85, 38, 160, 131, 29)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Time"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value),LEAN_SCALAR_PTR_LITERAL(220, 100, 176, 159, 117, 208, 208, 196)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Zoned"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6_value),LEAN_SCALAR_PTR_LITERAL(200, 191, 191, 47, 25, 58, 152, 177)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Database"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8_value),LEAN_SCALAR_PTR_LITERAL(92, 215, 123, 77, 185, 77, 182, 197)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "TzIf"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10_value),LEAN_SCALAR_PTR_LITERAL(4, 250, 62, 135, 116, 169, 36, 133)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(101, 92, 86, 180, 111, 227, 221, 239)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 48, 118, 165, 130, 15, 30, 223)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value),LEAN_SCALAR_PTR_LITERAL(110, 166, 16, 217, 58, 209, 201, 72)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TimeZone"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15_value),LEAN_SCALAR_PTR_LITERAL(245, 8, 144, 26, 147, 201, 147, 186)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "TZif"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17_value),LEAN_SCALAR_PTR_LITERAL(193, 81, 66, 63, 91, 97, 26, 75)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "termInt32"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19_value),LEAN_SCALAR_PTR_LITERAL(18, 219, 24, 74, 184, 233, 139, 159)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23_value;
LEAN_EXPORT const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "termInt64"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 39, 164, 189, 100, 116, 221, 108)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4_value;
LEAN_EXPORT const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_TZif_instReprHeader_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isutcnt"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isstdcnt"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "leapcnt"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "timecnt"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "typecnt"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "charcnt"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_TZif_instReprHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_TZif_instReprHeader_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instReprHeader = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 32, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedHeader_default = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedHeader = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "gmtOffset"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isDst"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "abbreviationIndex"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "transitionTime"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "correction"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1_value;
static const lean_string_object l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3;
static lean_once_cell_t l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4;
static const lean_ctor_object l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6_value;
static const lean_string_object l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(lean_object*);
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "transitionTimes"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "transitionIndices"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "localTimeTypes"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "abbreviations"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leapSeconds"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "stdWallIndicators"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "utLocalIndicators"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0_value;
static const lean_array_object l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV1 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_value;
static const lean_string_object l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toTZifV1"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "footer"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV2 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "v1"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4;
static const lean_string_object l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "v2"};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_TZif_instReprTZif___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_TZif_instReprTZif_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_TZif_instReprTZif___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instReprTZif = (const lean_object*)&l_Std_Time_TimeZone_TZif_instReprTZif___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZif_default = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZif = (const lean_object*)&l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1;
LEAN_EXPORT uint32_t l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Time.Zoned.Database.TzIf"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Std.Time.Zoned.Database.TzIf.0.Std.Time.TimeZone.TZif.toUInt32"};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "assertion violation: bs.size == 4\n  "};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3;
LEAN_EXPORT uint32_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___boxed(lean_object*);
static lean_once_cell_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu64(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(lean_object*);
static lean_once_cell_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes___boxed(lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "condition not satisfied"};
static const lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(lean_object*, lean_object*);
static const lean_array_object l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_parse(lean_object*);
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0));
v___x_56_ = l_String_toRawSubstring_x27(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1(lean_object* v_x_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20));
v___x_74_ = l_Lean_Syntax_isOfKind(v_x_70_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_box(1);
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v_a_72_);
return v___x_76_;
}
else
{
lean_object* v_quotContext_77_; lean_object* v_currMacroScope_78_; lean_object* v_ref_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_quotContext_77_ = lean_ctor_get(v_a_71_, 1);
v_currMacroScope_78_ = lean_ctor_get(v_a_71_, 2);
v_ref_79_ = lean_ctor_get(v_a_71_, 5);
v___x_80_ = 0;
v___x_81_ = l_Lean_SourceInfo_fromRef(v_ref_79_, v___x_80_);
v___x_82_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1);
v___x_83_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2));
lean_inc(v_currMacroScope_78_);
lean_inc(v_quotContext_77_);
v___x_84_ = l_Lean_addMacroScope(v_quotContext_77_, v___x_83_, v_currMacroScope_78_);
v___x_85_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6));
v___x_86_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_86_, 0, v___x_81_);
lean_ctor_set(v___x_86_, 1, v___x_82_);
lean_ctor_set(v___x_86_, 2, v___x_84_);
lean_ctor_set(v___x_86_, 3, v___x_85_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_a_72_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___boxed(lean_object* v_x_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1(v_x_88_, v_a_89_, v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1(lean_object* v_x_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1));
lean_inc(v_x_95_);
v___x_99_ = l_Lean_Syntax_isOfKind(v_x_95_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_x_95_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_a_97_);
return v___x_101_;
}
else
{
lean_object* v_ref_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_ref_102_ = l_Lean_replaceRef(v_x_95_, v_a_96_);
lean_dec(v_x_95_);
v___x_103_ = 0;
v___x_104_ = l_Lean_SourceInfo_fromRef(v_ref_102_, v___x_103_);
lean_dec(v_ref_102_);
v___x_105_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20));
v___x_106_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21));
lean_inc(v___x_104_);
v___x_107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_104_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = l_Lean_Syntax_node1(v___x_104_, v___x_105_, v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_a_97_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___boxed(lean_object* v_x_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1(v_x_110_, v_a_111_, v_a_112_);
lean_dec(v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1(lean_object* v_x_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1));
v___x_130_ = l_Lean_Syntax_isOfKind(v_x_126_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_box(1);
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v_a_128_);
return v___x_132_;
}
else
{
lean_object* v_quotContext_133_; lean_object* v_currMacroScope_134_; lean_object* v_ref_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_quotContext_133_ = lean_ctor_get(v_a_127_, 1);
v_currMacroScope_134_ = lean_ctor_get(v_a_127_, 2);
v_ref_135_ = lean_ctor_get(v_a_127_, 5);
v___x_136_ = 0;
v___x_137_ = l_Lean_SourceInfo_fromRef(v_ref_135_, v___x_136_);
v___x_138_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1);
v___x_139_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2));
lean_inc(v_currMacroScope_134_);
lean_inc(v_quotContext_133_);
v___x_140_ = l_Lean_addMacroScope(v_quotContext_133_, v___x_139_, v_currMacroScope_134_);
v___x_141_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6));
v___x_142_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_142_, 0, v___x_137_);
lean_ctor_set(v___x_142_, 1, v___x_138_);
lean_ctor_set(v___x_142_, 2, v___x_140_);
lean_ctor_set(v___x_142_, 3, v___x_141_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_a_128_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1___boxed(lean_object* v_x_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1(v_x_144_, v_a_145_, v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2(lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1));
lean_inc(v_x_148_);
v___x_152_ = l_Lean_Syntax_isOfKind(v_x_148_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_x_148_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_a_150_);
return v___x_154_;
}
else
{
lean_object* v_ref_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_ref_155_ = l_Lean_replaceRef(v_x_148_, v_a_149_);
lean_dec(v_x_148_);
v___x_156_ = 0;
v___x_157_ = l_Lean_SourceInfo_fromRef(v_ref_155_, v___x_156_);
lean_dec(v_ref_155_);
v___x_158_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1));
v___x_159_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2));
lean_inc(v___x_157_);
v___x_160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_157_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = l_Lean_Syntax_node1(v___x_157_, v___x_158_, v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_a_150_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2___boxed(lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2(v_x_163_, v_a_164_, v_a_165_);
lean_dec(v_a_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_TZif_instReprHeader_repr_spec__0(lean_object* v_a_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_nat_to_int(v_a_167_);
return v___x_168_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(11u);
v___x_183_ = lean_nat_to_int(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(12u);
v___x_194_ = lean_nat_to_int(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0));
v___x_209_ = lean_string_length(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24);
v___x_211_ = lean_nat_to_int(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(lean_object* v_x_216_){
_start:
{
uint8_t v_version_217_; uint32_t v_isutcnt_218_; uint32_t v_isstdcnt_219_; uint32_t v_leapcnt_220_; uint32_t v_timecnt_221_; uint32_t v_typecnt_222_; uint32_t v_charcnt_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_version_217_ = lean_ctor_get_uint8(v_x_216_, 24);
v_isutcnt_218_ = lean_ctor_get_uint32(v_x_216_, 0);
v_isstdcnt_219_ = lean_ctor_get_uint32(v_x_216_, 4);
v_leapcnt_220_ = lean_ctor_get_uint32(v_x_216_, 8);
v_timecnt_221_ = lean_ctor_get_uint32(v_x_216_, 12);
v_typecnt_222_ = lean_ctor_get_uint32(v_x_216_, 16);
v_charcnt_223_ = lean_ctor_get_uint32(v_x_216_, 20);
v___x_224_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_225_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6));
v___x_226_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7);
v___x_227_ = lean_uint8_to_nat(v_version_217_);
v___x_228_ = l_Nat_reprFast(v___x_227_);
v___x_229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
v___x_230_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_226_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = 0;
v___x_232_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*1, v___x_231_);
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_225_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_box(1);
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11));
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_224_);
v___x_241_ = lean_uint32_to_nat(v_isutcnt_218_);
v___x_242_ = l_Nat_reprFast(v___x_241_);
v___x_243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_226_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_231_);
v___x_246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_240_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_234_);
v___x_248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_236_);
v___x_249_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13));
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_224_);
v___x_252_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14);
v___x_253_ = lean_uint32_to_nat(v_isstdcnt_219_);
v___x_254_ = l_Nat_reprFast(v___x_253_);
v___x_255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
v___x_256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_252_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*1, v___x_231_);
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_251_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_234_);
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_236_);
v___x_261_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16));
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_224_);
v___x_264_ = lean_uint32_to_nat(v_leapcnt_220_);
v___x_265_ = l_Nat_reprFast(v___x_264_);
v___x_266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
v___x_267_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_226_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1, v___x_231_);
v___x_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_263_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_234_);
v___x_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_236_);
v___x_272_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18));
v___x_273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_224_);
v___x_275_ = lean_uint32_to_nat(v_timecnt_221_);
v___x_276_ = l_Nat_reprFast(v___x_275_);
v___x_277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
v___x_278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_226_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*1, v___x_231_);
v___x_280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_274_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_234_);
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_236_);
v___x_283_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20));
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_224_);
v___x_286_ = lean_uint32_to_nat(v_typecnt_222_);
v___x_287_ = l_Nat_reprFast(v___x_286_);
v___x_288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
v___x_289_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_226_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*1, v___x_231_);
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_285_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_234_);
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_236_);
v___x_294_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22));
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_224_);
v___x_297_ = lean_uint32_to_nat(v_charcnt_223_);
v___x_298_ = l_Nat_reprFast(v___x_297_);
v___x_299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
v___x_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_226_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*1, v___x_231_);
v___x_302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_296_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_304_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_302_);
v___x_306_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_303_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*1, v___x_231_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___boxed(lean_object* v_x_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_x_310_);
lean_dec_ref(v_x_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr(lean_object* v_x_312_, lean_object* v_prec_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_x_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___boxed(lean_object* v_x_315_, lean_object* v_prec_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr(v_x_315_, v_prec_316_);
lean_dec(v_prec_316_);
lean_dec_ref(v_x_315_);
return v_res_317_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(13u);
v___x_335_ = lean_nat_to_int(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(9u);
v___x_340_ = lean_nat_to_int(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(21u);
v___x_345_ = lean_nat_to_int(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_nat_to_int(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(lean_object* v_x_348_){
_start:
{
lean_object* v_gmtOffset_349_; uint8_t v_isDst_350_; uint8_t v_abbreviationIndex_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___y_356_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_gmtOffset_349_ = lean_ctor_get(v_x_348_, 0);
v_isDst_350_ = lean_ctor_get_uint8(v_x_348_, sizeof(void*)*1);
v_abbreviationIndex_351_ = lean_ctor_get_uint8(v_x_348_, sizeof(void*)*1 + 1);
v___x_352_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_353_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3));
v___x_354_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4);
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_394_ = lean_int_dec_lt(v_gmtOffset_349_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = l_Int_repr(v_gmtOffset_349_);
v___x_396_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
v___y_356_ = v___x_396_;
goto v___jp_355_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = l_Int_repr(v_gmtOffset_349_);
v___x_398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = l_Repr_addAppParen(v___x_398_, v___x_392_);
v___y_356_ = v___x_399_;
goto v___jp_355_;
}
v___jp_355_:
{
lean_object* v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_357_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_354_);
lean_ctor_set(v___x_357_, 1, v___y_356_);
v___x_358_ = 0;
v___x_359_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*1, v___x_358_);
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_353_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_box(1);
v___x_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6));
v___x_366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_352_);
v___x_368_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7);
v___x_369_ = l_Bool_repr___redArg(v_isDst_350_);
v___x_370_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_358_);
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_367_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_361_);
v___x_374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_363_);
v___x_375_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9));
v___x_376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_352_);
v___x_378_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10);
v___x_379_ = lean_uint8_to_nat(v_abbreviationIndex_351_);
v___x_380_ = l_Nat_reprFast(v___x_379_);
v___x_381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_378_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*1, v___x_358_);
v___x_384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_377_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_386_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_384_);
v___x_388_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_385_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*1, v___x_358_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___boxed(lean_object* v_x_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_x_400_);
lean_dec_ref(v_x_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(lean_object* v_x_402_, lean_object* v_prec_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_x_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___boxed(lean_object* v_x_405_, lean_object* v_prec_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(v_x_405_, v_prec_406_);
lean_dec(v_prec_406_);
lean_dec_ref(v_x_405_);
return v_res_407_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0(void){
_start:
{
uint8_t v___x_410_; uint8_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_410_ = 0;
v___x_411_ = 0;
v___x_412_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_413_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*1, v___x_411_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*1 + 1, v___x_410_);
return v___x_413_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default(void){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0);
return v___x_414_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType(void){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default;
return v___x_415_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_unsigned_to_nat(18u);
v___x_426_ = lean_nat_to_int(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(14u);
v___x_431_ = lean_nat_to_int(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(lean_object* v_x_432_){
_start:
{
lean_object* v_transitionTime_433_; lean_object* v_correction_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_488_; 
v_transitionTime_433_ = lean_ctor_get(v_x_432_, 0);
v_correction_434_ = lean_ctor_get(v_x_432_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_488_ == 0)
{
v___x_436_ = v_x_432_;
v_isShared_437_ = v_isSharedCheck_488_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_correction_434_);
lean_inc(v_transitionTime_433_);
lean_dec(v_x_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_488_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___y_439_; lean_object* v___y_440_; uint8_t v___y_441_; lean_object* v___y_442_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___y_459_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_455_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_456_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3));
v___x_457_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_482_ = lean_int_dec_lt(v_transitionTime_433_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = l_Int_repr(v_transitionTime_433_);
lean_dec(v_transitionTime_433_);
v___x_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
v___y_459_ = v___x_484_;
goto v___jp_458_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = l_Int_repr(v_transitionTime_433_);
lean_dec(v_transitionTime_433_);
v___x_486_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
v___x_487_ = l_Repr_addAppParen(v___x_486_, v___x_480_);
v___y_459_ = v___x_487_;
goto v___jp_458_;
}
v___jp_438_:
{
lean_object* v___x_444_; 
lean_inc(v___y_440_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 4);
lean_ctor_set(v___x_436_, 1, v___y_442_);
lean_ctor_set(v___x_436_, 0, v___y_440_);
v___x_444_ = v___x_436_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___y_440_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___y_442_);
v___x_444_ = v_reuseFailAlloc_454_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_445_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1, v___y_441_);
v___x_446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_446_, 0, v___y_439_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_448_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_446_);
v___x_450_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_447_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*1, v___y_441_);
return v___x_453_;
}
}
v___jp_458_:
{
lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_460_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_457_);
lean_ctor_set(v___x_460_, 1, v___y_459_);
v___x_461_ = 0;
v___x_462_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*1, v___x_461_);
v___x_463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_456_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = lean_box(1);
v___x_467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6));
v___x_469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_455_);
v___x_471_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_474_ = lean_int_dec_lt(v_correction_434_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = l_Int_repr(v_correction_434_);
lean_dec(v_correction_434_);
v___x_476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
v___y_439_ = v___x_470_;
v___y_440_ = v___x_471_;
v___y_441_ = v___x_461_;
v___y_442_ = v___x_476_;
goto v___jp_438_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = l_Int_repr(v_correction_434_);
lean_dec(v_correction_434_);
v___x_478_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
v___x_479_ = l_Repr_addAppParen(v___x_478_, v___x_472_);
v___y_439_ = v___x_470_;
v___y_440_ = v___x_471_;
v___y_441_ = v___x_461_;
v___y_442_ = v___x_479_;
goto v___jp_438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr(lean_object* v_x_489_, lean_object* v_prec_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_x_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___boxed(lean_object* v_x_492_, lean_object* v_prec_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr(v_x_492_, v_prec_493_);
lean_dec(v_prec_493_);
return v_res_494_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default(void){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0);
return v___x_499_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond(void){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default;
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
lean_dec(v_x_501_);
return v_x_502_;
}
else
{
lean_object* v_head_504_; lean_object* v_tail_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_516_; 
v_head_504_ = lean_ctor_get(v_x_503_, 0);
v_tail_505_ = lean_ctor_get(v_x_503_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_503_);
if (v_isSharedCheck_516_ == 0)
{
v___x_507_ = v_x_503_;
v_isShared_508_ = v_isSharedCheck_516_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_tail_505_);
lean_inc(v_head_504_);
lean_dec(v_x_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_516_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
lean_inc(v_x_501_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 5);
lean_ctor_set(v___x_507_, 1, v_x_501_);
lean_ctor_set(v___x_507_, 0, v_x_502_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_x_502_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_x_501_);
v___x_510_ = v_reuseFailAlloc_515_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_unbox(v_head_504_);
lean_dec(v_head_504_);
v___x_512_ = l_Bool_repr___redArg(v___x_511_);
v___x_513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_510_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v_x_502_ = v___x_513_;
v_x_503_ = v_tail_505_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16(lean_object* v_x_517_, lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
lean_dec(v_x_517_);
return v_x_518_;
}
else
{
lean_object* v_head_520_; lean_object* v_tail_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_532_; 
v_head_520_ = lean_ctor_get(v_x_519_, 0);
v_tail_521_ = lean_ctor_get(v_x_519_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v_x_519_);
if (v_isSharedCheck_532_ == 0)
{
v___x_523_ = v_x_519_;
v_isShared_524_ = v_isSharedCheck_532_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_tail_521_);
lean_inc(v_head_520_);
lean_dec(v_x_519_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_532_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
lean_inc(v_x_517_);
if (v_isShared_524_ == 0)
{
lean_ctor_set_tag(v___x_523_, 5);
lean_ctor_set(v___x_523_, 1, v_x_517_);
lean_ctor_set(v___x_523_, 0, v_x_518_);
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_x_518_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_x_517_);
v___x_526_ = v_reuseFailAlloc_531_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_527_ = lean_unbox(v_head_520_);
lean_dec(v_head_520_);
v___x_528_ = l_Bool_repr___redArg(v___x_527_);
v___x_529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_526_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(v_x_517_, v___x_529_, v_tail_521_);
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
lean_object* v___x_535_; 
lean_dec(v_x_534_);
v___x_535_ = lean_box(0);
return v___x_535_;
}
else
{
lean_object* v_tail_536_; 
v_tail_536_ = lean_ctor_get(v_x_533_, 1);
if (lean_obj_tag(v_tail_536_) == 0)
{
lean_object* v_head_537_; uint8_t v___x_538_; lean_object* v___x_539_; 
lean_dec(v_x_534_);
v_head_537_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_head_537_);
lean_dec_ref_known(v_x_533_, 2);
v___x_538_ = lean_unbox(v_head_537_);
lean_dec(v_head_537_);
v___x_539_ = l_Bool_repr___redArg(v___x_538_);
return v___x_539_;
}
else
{
lean_object* v_head_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_inc(v_tail_536_);
v_head_540_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_head_540_);
lean_dec_ref_known(v_x_533_, 2);
v___x_541_ = lean_unbox(v_head_540_);
lean_dec(v_head_540_);
v___x_542_ = l_Bool_repr___redArg(v___x_541_);
v___x_543_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16(v_x_534_, v___x_542_, v_tail_536_);
return v___x_543_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0));
v___x_550_ = lean_string_length(v___x_549_);
return v___x_550_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3);
v___x_552_ = lean_nat_to_int(v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(lean_object* v_xs_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_561_ = lean_array_get_size(v_xs_560_);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_nat_dec_eq(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_564_ = lean_array_to_list(v_xs_560_);
v___x_565_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_566_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(v___x_564_, v___x_565_);
v___x_567_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_568_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_566_);
v___x_570_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_567_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Std_Format_fill(v___x_572_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; 
lean_dec_ref(v_xs_560_);
v___x_574_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(lean_object* v___y_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = l_String_quote(v___y_575_);
v___x_577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_x_580_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
lean_dec(v_x_578_);
return v_x_579_;
}
else
{
lean_object* v_head_581_; lean_object* v_tail_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_593_; 
v_head_581_ = lean_ctor_get(v_x_580_, 0);
v_tail_582_ = lean_ctor_get(v_x_580_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_593_ == 0)
{
v___x_584_ = v_x_580_;
v_isShared_585_ = v_isSharedCheck_593_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_tail_582_);
lean_inc(v_head_581_);
lean_dec(v_x_580_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_593_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
lean_inc(v_x_578_);
if (v_isShared_585_ == 0)
{
lean_ctor_set_tag(v___x_584_, 5);
lean_ctor_set(v___x_584_, 1, v_x_578_);
lean_ctor_set(v___x_584_, 0, v_x_579_);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_x_579_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_x_578_);
v___x_587_ = v_reuseFailAlloc_592_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = l_String_quote(v_head_581_);
v___x_589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_587_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v_x_579_ = v___x_590_;
v_x_580_ = v_tail_582_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10(lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
lean_dec(v_x_594_);
return v_x_595_;
}
else
{
lean_object* v_head_597_; lean_object* v_tail_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_609_; 
v_head_597_ = lean_ctor_get(v_x_596_, 0);
v_tail_598_ = lean_ctor_get(v_x_596_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_596_);
if (v_isSharedCheck_609_ == 0)
{
v___x_600_ = v_x_596_;
v_isShared_601_ = v_isSharedCheck_609_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_tail_598_);
lean_inc(v_head_597_);
lean_dec(v_x_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_609_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
lean_inc(v_x_594_);
if (v_isShared_601_ == 0)
{
lean_ctor_set_tag(v___x_600_, 5);
lean_ctor_set(v___x_600_, 1, v_x_594_);
lean_ctor_set(v___x_600_, 0, v_x_595_);
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_x_595_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_x_594_);
v___x_603_ = v_reuseFailAlloc_608_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_604_ = l_String_quote(v_head_597_);
v___x_605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_603_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(v_x_594_, v___x_606_, v_tail_598_);
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
if (lean_obj_tag(v_x_610_) == 0)
{
lean_object* v___x_612_; 
lean_dec(v_x_611_);
v___x_612_ = lean_box(0);
return v___x_612_;
}
else
{
lean_object* v_tail_613_; 
v_tail_613_ = lean_ctor_get(v_x_610_, 1);
if (lean_obj_tag(v_tail_613_) == 0)
{
lean_object* v_head_614_; lean_object* v___x_615_; 
lean_dec(v_x_611_);
v_head_614_ = lean_ctor_get(v_x_610_, 0);
lean_inc(v_head_614_);
lean_dec_ref_known(v_x_610_, 2);
v___x_615_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(v_head_614_);
return v___x_615_;
}
else
{
lean_object* v_head_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_inc(v_tail_613_);
v_head_616_ = lean_ctor_get(v_x_610_, 0);
lean_inc(v_head_616_);
lean_dec_ref_known(v_x_610_, 2);
v___x_617_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(v_head_616_);
v___x_618_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10(v_x_611_, v___x_617_, v_tail_613_);
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(lean_object* v_xs_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_array_get_size(v_xs_619_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_nat_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_623_ = lean_array_to_list(v_xs_619_);
v___x_624_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_625_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(v___x_623_, v___x_624_);
v___x_626_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_627_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_625_);
v___x_629_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_626_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Std_Format_fill(v___x_631_);
return v___x_632_;
}
else
{
lean_object* v___x_633_; 
lean_dec_ref(v_xs_619_);
v___x_633_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_dec(v_x_634_);
return v_x_635_;
}
else
{
lean_object* v_head_637_; lean_object* v_tail_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_651_; 
v_head_637_ = lean_ctor_get(v_x_636_, 0);
v_tail_638_ = lean_ctor_get(v_x_636_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_636_);
if (v_isSharedCheck_651_ == 0)
{
v___x_640_ = v_x_636_;
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_tail_638_);
lean_inc(v_head_637_);
lean_dec(v_x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
lean_inc(v_x_634_);
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 5);
lean_ctor_set(v___x_640_, 1, v_x_634_);
lean_ctor_set(v___x_640_, 0, v_x_635_);
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_x_635_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_x_634_);
v___x_643_ = v_reuseFailAlloc_650_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_644_ = lean_unbox(v_head_637_);
lean_dec(v_head_637_);
v___x_645_ = lean_uint8_to_nat(v___x_644_);
v___x_646_ = l_Nat_reprFast(v___x_645_);
v___x_647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
v___x_648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_643_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v_x_635_ = v___x_648_;
v_x_636_ = v_tail_638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_dec(v_x_652_);
return v_x_653_;
}
else
{
lean_object* v_head_655_; lean_object* v_tail_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_669_; 
v_head_655_ = lean_ctor_get(v_x_654_, 0);
v_tail_656_ = lean_ctor_get(v_x_654_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_669_ == 0)
{
v___x_658_ = v_x_654_;
v_isShared_659_ = v_isSharedCheck_669_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_tail_656_);
lean_inc(v_head_655_);
lean_dec(v_x_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_669_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
lean_inc(v_x_652_);
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 5);
lean_ctor_set(v___x_658_, 1, v_x_652_);
lean_ctor_set(v___x_658_, 0, v_x_653_);
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_x_653_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_x_652_);
v___x_661_ = v_reuseFailAlloc_668_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_662_ = lean_unbox(v_head_655_);
lean_dec(v_head_655_);
v___x_663_ = lean_uint8_to_nat(v___x_662_);
v___x_664_ = l_Nat_reprFast(v___x_663_);
v___x_665_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
v___x_666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_661_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(v_x_652_, v___x_666_, v_tail_656_);
return v___x_667_;
}
}
}
}
}
lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(uint8_t v___y_670_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_uint8_to_nat(v___y_670_);
v___x_672_ = l_Nat_reprFast(v___x_671_);
v___x_673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT void l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_670_ = stack[0].m_num;
lean_object* v_res_674_;
v_res_674_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___y_670_);
stack->m_obj
 = v_res_674_;
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0___boxed(lean_object* v___y_675_){
_start:
{
uint8_t v___y_2172__boxed_676_; lean_object* v_res_677_; 
v___y_2172__boxed_676_ = lean_unbox(v___y_675_);
v_res_677_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___y_2172__boxed_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
lean_object* v___x_680_; 
lean_dec(v_x_679_);
v___x_680_ = lean_box(0);
return v___x_680_;
}
else
{
lean_object* v_tail_681_; 
v_tail_681_ = lean_ctor_get(v_x_678_, 1);
if (lean_obj_tag(v_tail_681_) == 0)
{
lean_object* v_head_682_; uint8_t v___x_683_; lean_object* v___x_684_; 
lean_dec(v_x_679_);
v_head_682_ = lean_ctor_get(v_x_678_, 0);
lean_inc(v_head_682_);
lean_dec_ref_known(v_x_678_, 2);
v___x_683_ = lean_unbox(v_head_682_);
lean_dec(v_head_682_);
v___x_684_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_683_);
return v___x_684_;
}
else
{
lean_object* v_head_685_; uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_inc(v_tail_681_);
v_head_685_ = lean_ctor_get(v_x_678_, 0);
lean_inc(v_head_685_);
lean_dec_ref_known(v_x_678_, 2);
v___x_686_ = lean_unbox(v_head_685_);
lean_dec(v_head_685_);
v___x_687_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_686_);
v___x_688_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(v_x_679_, v___x_687_, v_tail_681_);
return v___x_688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(lean_object* v_xs_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_array_get_size(v_xs_689_);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_nat_dec_eq(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_693_ = lean_array_to_list(v_xs_689_);
v___x_694_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_695_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(v___x_693_, v___x_694_);
v___x_696_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_697_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_695_);
v___x_699_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_696_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_Std_Format_fill(v___x_701_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; 
lean_dec_ref(v_xs_689_);
v___x_703_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_x_706_) == 0)
{
lean_dec(v_x_704_);
return v_x_705_;
}
else
{
lean_object* v_head_707_; lean_object* v_tail_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_727_; 
v_head_707_ = lean_ctor_get(v_x_706_, 0);
v_tail_708_ = lean_ctor_get(v_x_706_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_x_706_);
if (v_isSharedCheck_727_ == 0)
{
v___x_710_ = v_x_706_;
v_isShared_711_ = v_isSharedCheck_727_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_tail_708_);
lean_inc(v_head_707_);
lean_dec(v_x_706_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_727_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
lean_inc(v_x_704_);
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 5);
lean_ctor_set(v___x_710_, 1, v_x_704_);
lean_ctor_set(v___x_710_, 0, v_x_705_);
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_x_705_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_x_704_);
v___x_713_ = v_reuseFailAlloc_726_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_716_ = lean_int_dec_lt(v_head_707_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = l_Int_repr(v_head_707_);
lean_dec(v_head_707_);
v___x_718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
v___x_719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_713_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v_x_705_ = v___x_719_;
v_x_706_ = v_tail_708_;
goto _start;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_721_ = l_Int_repr(v_head_707_);
lean_dec(v_head_707_);
v___x_722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___x_723_ = l_Repr_addAppParen(v___x_722_, v___x_714_);
v___x_724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_713_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v_x_705_ = v___x_724_;
v_x_706_ = v_tail_708_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
if (lean_obj_tag(v_x_730_) == 0)
{
lean_dec(v_x_728_);
return v_x_729_;
}
else
{
lean_object* v_head_731_; lean_object* v_tail_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_751_; 
v_head_731_ = lean_ctor_get(v_x_730_, 0);
v_tail_732_ = lean_ctor_get(v_x_730_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x_730_);
if (v_isSharedCheck_751_ == 0)
{
v___x_734_ = v_x_730_;
v_isShared_735_ = v_isSharedCheck_751_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_tail_732_);
lean_inc(v_head_731_);
lean_dec(v_x_730_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_751_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
lean_inc(v_x_728_);
if (v_isShared_735_ == 0)
{
lean_ctor_set_tag(v___x_734_, 5);
lean_ctor_set(v___x_734_, 1, v_x_728_);
lean_ctor_set(v___x_734_, 0, v_x_729_);
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_x_729_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_x_728_);
v___x_737_ = v_reuseFailAlloc_750_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_740_ = lean_int_dec_lt(v_head_731_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_741_ = l_Int_repr(v_head_731_);
lean_dec(v_head_731_);
v___x_742_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
v___x_743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_737_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_728_, v___x_743_, v_tail_732_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_745_ = l_Int_repr(v_head_731_);
lean_dec(v_head_731_);
v___x_746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
v___x_747_ = l_Repr_addAppParen(v___x_746_, v___x_738_);
v___x_748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_737_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_728_, v___x_748_, v_tail_732_);
return v___x_749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(lean_object* v___y_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_755_ = lean_int_dec_lt(v___y_752_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = l_Int_repr(v___y_752_);
v___x_757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_758_ = l_Int_repr(v___y_752_);
v___x_759_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
v___x_760_ = l_Repr_addAppParen(v___x_759_, v___x_753_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0___boxed(lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v___y_761_);
lean_dec(v___y_761_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
lean_object* v___x_765_; 
lean_dec(v_x_764_);
v___x_765_ = lean_box(0);
return v___x_765_;
}
else
{
lean_object* v_tail_766_; 
v_tail_766_ = lean_ctor_get(v_x_763_, 1);
if (lean_obj_tag(v_tail_766_) == 0)
{
lean_object* v_head_767_; lean_object* v___x_768_; 
lean_dec(v_x_764_);
v_head_767_ = lean_ctor_get(v_x_763_, 0);
lean_inc(v_head_767_);
lean_dec_ref_known(v_x_763_, 2);
v___x_768_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_767_);
lean_dec(v_head_767_);
return v___x_768_;
}
else
{
lean_object* v_head_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_inc(v_tail_766_);
v_head_769_ = lean_ctor_get(v_x_763_, 0);
lean_inc(v_head_769_);
lean_dec_ref_known(v_x_763_, 2);
v___x_770_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_769_);
lean_dec(v_head_769_);
v___x_771_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(v_x_764_, v___x_770_, v_tail_766_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(lean_object* v_xs_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_array_get_size(v_xs_772_);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_nat_dec_eq(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_776_ = lean_array_to_list(v_xs_772_);
v___x_777_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_778_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(v___x_776_, v___x_777_);
v___x_779_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_780_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_778_);
v___x_782_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_779_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Std_Format_fill(v___x_784_);
return v___x_785_;
}
else
{
lean_object* v___x_786_; 
lean_dec_ref(v_xs_772_);
v___x_786_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
if (lean_obj_tag(v_x_789_) == 0)
{
lean_dec(v_x_787_);
return v_x_788_;
}
else
{
lean_object* v_head_790_; lean_object* v_tail_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_801_; 
v_head_790_ = lean_ctor_get(v_x_789_, 0);
v_tail_791_ = lean_ctor_get(v_x_789_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_x_789_);
if (v_isSharedCheck_801_ == 0)
{
v___x_793_ = v_x_789_;
v_isShared_794_ = v_isSharedCheck_801_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_tail_791_);
lean_inc(v_head_790_);
lean_dec(v_x_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_801_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
lean_inc(v_x_787_);
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 5);
lean_ctor_set(v___x_793_, 1, v_x_787_);
lean_ctor_set(v___x_793_, 0, v_x_788_);
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_x_788_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_x_787_);
v___x_796_ = v_reuseFailAlloc_800_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_790_);
lean_dec(v_head_790_);
v___x_798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v_x_788_ = v___x_798_;
v_x_789_ = v_tail_791_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
if (lean_obj_tag(v_x_804_) == 0)
{
lean_dec(v_x_802_);
return v_x_803_;
}
else
{
lean_object* v_head_805_; lean_object* v_tail_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_816_; 
v_head_805_ = lean_ctor_get(v_x_804_, 0);
v_tail_806_ = lean_ctor_get(v_x_804_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v_x_804_);
if (v_isSharedCheck_816_ == 0)
{
v___x_808_ = v_x_804_;
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_tail_806_);
lean_inc(v_head_805_);
lean_dec(v_x_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
lean_inc(v_x_802_);
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 5);
lean_ctor_set(v___x_808_, 1, v_x_802_);
lean_ctor_set(v___x_808_, 0, v_x_803_);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_x_803_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_x_802_);
v___x_811_ = v_reuseFailAlloc_815_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_805_);
lean_dec(v_head_805_);
v___x_813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(v_x_802_, v___x_813_, v_tail_806_);
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
if (lean_obj_tag(v_x_817_) == 0)
{
lean_object* v___x_819_; 
lean_dec(v_x_818_);
v___x_819_ = lean_box(0);
return v___x_819_;
}
else
{
lean_object* v_tail_820_; 
v_tail_820_ = lean_ctor_get(v_x_817_, 1);
if (lean_obj_tag(v_tail_820_) == 0)
{
lean_object* v_head_821_; lean_object* v___x_822_; 
lean_dec(v_x_818_);
v_head_821_ = lean_ctor_get(v_x_817_, 0);
lean_inc(v_head_821_);
lean_dec_ref_known(v_x_817_, 2);
v___x_822_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_821_);
lean_dec(v_head_821_);
return v___x_822_;
}
else
{
lean_object* v_head_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_inc(v_tail_820_);
v_head_823_ = lean_ctor_get(v_x_817_, 0);
lean_inc(v_head_823_);
lean_dec_ref_known(v_x_817_, 2);
v___x_824_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_823_);
lean_dec(v_head_823_);
v___x_825_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(v_x_818_, v___x_824_, v_tail_820_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(lean_object* v_xs_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_827_ = lean_array_get_size(v_xs_826_);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_nat_dec_eq(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_830_ = lean_array_to_list(v_xs_826_);
v___x_831_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_832_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(v___x_830_, v___x_831_);
v___x_833_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_834_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_832_);
v___x_836_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_833_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = l_Std_Format_fill(v___x_838_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; 
lean_dec_ref(v_xs_826_);
v___x_840_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
if (lean_obj_tag(v_x_843_) == 0)
{
lean_dec(v_x_841_);
return v_x_842_;
}
else
{
lean_object* v_head_844_; lean_object* v_tail_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_855_; 
v_head_844_ = lean_ctor_get(v_x_843_, 0);
v_tail_845_ = lean_ctor_get(v_x_843_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_x_843_);
if (v_isSharedCheck_855_ == 0)
{
v___x_847_ = v_x_843_;
v_isShared_848_ = v_isSharedCheck_855_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_tail_845_);
lean_inc(v_head_844_);
lean_dec(v_x_843_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_855_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
lean_inc(v_x_841_);
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 5);
lean_ctor_set(v___x_847_, 1, v_x_841_);
lean_ctor_set(v___x_847_, 0, v_x_842_);
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_x_842_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_x_841_);
v___x_850_ = v_reuseFailAlloc_854_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_844_);
v___x_852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v_x_842_ = v___x_852_;
v_x_843_ = v_tail_845_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
if (lean_obj_tag(v_x_858_) == 0)
{
lean_dec(v_x_856_);
return v_x_857_;
}
else
{
lean_object* v_head_859_; lean_object* v_tail_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_870_; 
v_head_859_ = lean_ctor_get(v_x_858_, 0);
v_tail_860_ = lean_ctor_get(v_x_858_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_x_858_);
if (v_isSharedCheck_870_ == 0)
{
v___x_862_ = v_x_858_;
v_isShared_863_ = v_isSharedCheck_870_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_tail_860_);
lean_inc(v_head_859_);
lean_dec(v_x_858_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_870_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
lean_inc(v_x_856_);
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 5);
lean_ctor_set(v___x_862_, 1, v_x_856_);
lean_ctor_set(v___x_862_, 0, v_x_857_);
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_x_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_x_856_);
v___x_865_ = v_reuseFailAlloc_869_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_859_);
v___x_867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(v_x_856_, v___x_867_, v_tail_860_);
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_object* v___x_873_; 
lean_dec(v_x_872_);
v___x_873_ = lean_box(0);
return v___x_873_;
}
else
{
lean_object* v_tail_874_; 
v_tail_874_ = lean_ctor_get(v_x_871_, 1);
if (lean_obj_tag(v_tail_874_) == 0)
{
lean_object* v_head_875_; lean_object* v___x_876_; 
lean_dec(v_x_872_);
v_head_875_ = lean_ctor_get(v_x_871_, 0);
lean_inc(v_head_875_);
lean_dec_ref_known(v_x_871_, 2);
v___x_876_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_875_);
return v___x_876_;
}
else
{
lean_object* v_head_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_inc(v_tail_874_);
v_head_877_ = lean_ctor_get(v_x_871_, 0);
lean_inc(v_head_877_);
lean_dec_ref_known(v_x_871_, 2);
v___x_878_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_877_);
v___x_879_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(v_x_872_, v___x_878_, v_tail_874_);
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(lean_object* v_xs_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_881_ = lean_array_get_size(v_xs_880_);
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_nat_dec_eq(v___x_881_, v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_884_ = lean_array_to_list(v_xs_880_);
v___x_885_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_886_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(v___x_884_, v___x_885_);
v___x_887_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_888_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_886_);
v___x_890_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_887_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Std_Format_fill(v___x_892_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
lean_dec_ref(v_xs_880_);
v___x_894_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_894_;
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(10u);
v___x_905_ = lean_nat_to_int(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_unsigned_to_nat(19u);
v___x_910_ = lean_nat_to_int(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(17u);
v___x_921_ = lean_nat_to_int(v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_unsigned_to_nat(15u);
v___x_926_ = lean_nat_to_int(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(lean_object* v_x_933_){
_start:
{
lean_object* v_header_934_; lean_object* v_transitionTimes_935_; lean_object* v_transitionIndices_936_; lean_object* v_localTimeTypes_937_; lean_object* v_abbreviations_938_; lean_object* v_leapSeconds_939_; lean_object* v_stdWallIndicators_940_; lean_object* v_utLocalIndicators_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_header_934_ = lean_ctor_get(v_x_933_, 0);
lean_inc_ref(v_header_934_);
v_transitionTimes_935_ = lean_ctor_get(v_x_933_, 1);
lean_inc_ref(v_transitionTimes_935_);
v_transitionIndices_936_ = lean_ctor_get(v_x_933_, 2);
lean_inc_ref(v_transitionIndices_936_);
v_localTimeTypes_937_ = lean_ctor_get(v_x_933_, 3);
lean_inc_ref(v_localTimeTypes_937_);
v_abbreviations_938_ = lean_ctor_get(v_x_933_, 4);
lean_inc_ref(v_abbreviations_938_);
v_leapSeconds_939_ = lean_ctor_get(v_x_933_, 5);
lean_inc_ref(v_leapSeconds_939_);
v_stdWallIndicators_940_ = lean_ctor_get(v_x_933_, 6);
lean_inc_ref(v_stdWallIndicators_940_);
v_utLocalIndicators_941_ = lean_ctor_get(v_x_933_, 7);
lean_inc_ref(v_utLocalIndicators_941_);
lean_dec_ref(v_x_933_);
v___x_942_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_943_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3));
v___x_944_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4);
v___x_945_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_header_934_);
lean_dec_ref(v_header_934_);
v___x_946_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = 0;
v___x_948_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*1, v___x_947_);
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_943_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_box(1);
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6));
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_942_);
v___x_957_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7);
v___x_958_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(v_transitionTimes_935_);
v___x_959_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set_uint8(v___x_960_, sizeof(void*)*1, v___x_947_);
v___x_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_956_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v___x_950_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___x_952_);
v___x_964_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9));
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_942_);
v___x_967_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10);
v___x_968_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(v_transitionIndices_936_);
v___x_969_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*1, v___x_947_);
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_966_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_950_);
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_952_);
v___x_974_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11));
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_942_);
v___x_977_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4);
v___x_978_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(v_localTimeTypes_937_);
v___x_979_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*1, v___x_947_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_976_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_950_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_952_);
v___x_984_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13));
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_942_);
v___x_987_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14);
v___x_988_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(v_abbreviations_938_);
v___x_989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*1, v___x_947_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_986_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_950_);
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_952_);
v___x_994_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16));
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_942_);
v___x_997_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17);
v___x_998_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(v_leapSeconds_939_);
v___x_999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*1, v___x_947_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_996_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_950_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_952_);
v___x_1004_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19));
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_942_);
v___x_1007_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(v_stdWallIndicators_940_);
v___x_1008_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_967_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*1, v___x_947_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1006_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_950_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_952_);
v___x_1013_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21));
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_942_);
v___x_1016_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(v_utLocalIndicators_941_);
v___x_1017_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_967_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*1, v___x_947_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1015_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1021_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_1019_);
v___x_1023_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1020_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set_uint8(v___x_1026_, sizeof(void*)*1, v___x_947_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(lean_object* v_x_1027_, lean_object* v_prec_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_x_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___boxed(lean_object* v_x_1030_, lean_object* v_prec_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(v_x_1030_, v_prec_1031_);
lean_dec(v_prec_1031_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
if (lean_obj_tag(v_x_1048_) == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1));
return v___x_1050_;
}
else
{
lean_object* v_val_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1062_; 
v_val_1051_ = lean_ctor_get(v_x_1048_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_x_1048_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1053_ = v_x_1048_;
v_isShared_1054_ = v_isSharedCheck_1062_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_val_1051_);
lean_dec(v_x_1048_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1062_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1055_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3));
v___x_1056_ = l_String_quote(v_val_1051_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 3);
lean_ctor_set(v___x_1053_, 0, v___x_1056_);
v___x_1058_ = v___x_1053_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1055_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Repr_addAppParen(v___x_1059_, v_x_1049_);
return v___x_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___boxed(lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(v_x_1063_, v_x_1064_);
lean_dec(v_x_1064_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(lean_object* v_x_1078_){
_start:
{
lean_object* v_toTZifV1_1079_; lean_object* v_footer_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1114_; 
v_toTZifV1_1079_ = lean_ctor_get(v_x_1078_, 0);
v_footer_1080_ = lean_ctor_get(v_x_1078_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_x_1078_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1082_ = v_x_1078_;
v_isShared_1083_ = v_isSharedCheck_1114_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_footer_1080_);
lean_inc(v_toTZifV1_1079_);
lean_dec(v_x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1114_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1084_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_1085_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3));
v___x_1086_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_toTZifV1_1079_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 4);
lean_ctor_set(v___x_1082_, 1, v___x_1088_);
lean_ctor_set(v___x_1082_, 0, v___x_1086_);
v___x_1090_ = v___x_1082_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1091_ = 0;
v___x_1092_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*1, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1085_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_box(1);
v___x_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5));
v___x_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v___x_1084_);
v___x_1101_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4);
v___x_1102_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(v_footer_1080_, v___x_1087_);
v___x_1103_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*1, v___x_1091_);
v___x_1105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1100_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1107_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v___x_1105_);
v___x_1109_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1106_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*1, v___x_1091_);
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(lean_object* v_x_1115_, lean_object* v_prec_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_x_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___boxed(lean_object* v_x_1118_, lean_object* v_prec_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(v_x_1118_, v_prec_1119_);
lean_dec(v_prec_1119_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
if (lean_obj_tag(v_x_1128_) == 0)
{
lean_object* v___x_1130_; 
v___x_1130_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1));
return v___x_1130_;
}
else
{
lean_object* v_val_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_val_1131_ = lean_ctor_get(v_x_1128_, 0);
lean_inc(v_val_1131_);
lean_dec_ref_known(v_x_1128_, 1);
v___x_1132_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3));
v___x_1133_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_val_1131_);
v___x_1134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Repr_addAppParen(v___x_1134_, v_x_1129_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0___boxed(lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(v_x_1136_, v_x_1137_);
lean_dec(v_x_1137_);
return v_res_1138_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_unsigned_to_nat(6u);
v___x_1149_ = lean_nat_to_int(v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(lean_object* v_x_1153_){
_start:
{
lean_object* v_v1_1154_; lean_object* v_v2_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1188_; 
v_v1_1154_ = lean_ctor_get(v_x_1153_, 0);
v_v2_1155_ = lean_ctor_get(v_x_1153_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_x_1153_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1157_ = v_x_1153_;
v_isShared_1158_ = v_isSharedCheck_1188_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_v2_1155_);
lean_inc(v_v1_1154_);
lean_dec(v_x_1153_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1188_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1159_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_1160_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3));
v___x_1161_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4);
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_v1_1154_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set_tag(v___x_1157_, 4);
lean_ctor_set(v___x_1157_, 1, v___x_1163_);
lean_ctor_set(v___x_1157_, 0, v___x_1161_);
v___x_1165_ = v___x_1157_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1166_ = 0;
v___x_1167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*1, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1160_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_1170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_box(1);
v___x_1172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6));
v___x_1174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v___x_1159_);
v___x_1176_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(v_v2_1155_, v___x_1162_);
v___x_1177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1161_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*1, v___x_1166_);
v___x_1179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1175_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1181_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v___x_1179_);
v___x_1183_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1180_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*1, v___x_1166_);
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr(lean_object* v_x_1189_, lean_object* v_prec_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(v_x_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___boxed(lean_object* v_x_1192_, lean_object* v_prec_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr(v_x_1192_, v_prec_1193_);
lean_dec(v_prec_1193_);
return v_res_1194_;
}
}
static lean_object* _init_l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = 0;
v___x_1203_ = lean_box_uint32(v___x_1202_);
return v___x_1203_;
}
}
uint32_t l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(lean_object* v_msg_1204_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; uint32_t v___x_1207_; 
v___x_1205_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1;
v___x_1206_ = lean_panic_fn_borrowed(v___x_1205_, v_msg_1204_);
v___x_1207_ = lean_unbox_uint32(v___x_1206_);
lean_dec(v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1204_ = stack[0].m_obj;
uint32_t v_res_1208_;
v_res_1208_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v_msg_1204_);
stack->m_num = v_res_1208_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed(lean_object* v_msg_1209_){
_start:
{
uint32_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v_msg_1209_);
v_r_1211_ = lean_box_uint32(v_res_1210_);
return v_r_1211_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1215_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2));
v___x_1216_ = lean_unsigned_to_nat(2u);
v___x_1217_ = lean_unsigned_to_nat(183u);
v___x_1218_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1));
v___x_1219_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0));
v___x_1220_ = l_mkPanicMessageWithDecl(v___x_1219_, v___x_1218_, v___x_1217_, v___x_1216_, v___x_1215_);
return v___x_1220_;
}
}
uint32_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(lean_object* v_bs_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1222_ = lean_byte_array_size(v_bs_1221_);
v___x_1223_ = lean_unsigned_to_nat(4u);
v___x_1224_ = lean_nat_dec_eq(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; uint32_t v___x_1226_; 
v___x_1225_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3);
v___x_1226_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v___x_1225_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; uint8_t v___x_1228_; uint32_t v___x_1229_; uint32_t v___x_1230_; uint32_t v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; uint32_t v___x_1234_; uint32_t v___x_1235_; uint32_t v___x_1236_; uint32_t v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; uint32_t v___x_1240_; uint32_t v___x_1241_; uint32_t v___x_1242_; uint32_t v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; uint32_t v___x_1246_; uint32_t v___x_1247_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_byte_array_get(v_bs_1221_, v___x_1227_);
v___x_1229_ = lean_uint8_to_uint32(v___x_1228_);
v___x_1230_ = 24;
v___x_1231_ = lean_uint32_shift_left(v___x_1229_, v___x_1230_);
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_byte_array_get(v_bs_1221_, v___x_1232_);
v___x_1234_ = lean_uint8_to_uint32(v___x_1233_);
v___x_1235_ = 16;
v___x_1236_ = lean_uint32_shift_left(v___x_1234_, v___x_1235_);
v___x_1237_ = lean_uint32_lor(v___x_1231_, v___x_1236_);
v___x_1238_ = lean_unsigned_to_nat(2u);
v___x_1239_ = lean_byte_array_get(v_bs_1221_, v___x_1238_);
v___x_1240_ = lean_uint8_to_uint32(v___x_1239_);
v___x_1241_ = 8;
v___x_1242_ = lean_uint32_shift_left(v___x_1240_, v___x_1241_);
v___x_1243_ = lean_uint32_lor(v___x_1237_, v___x_1242_);
v___x_1244_ = lean_unsigned_to_nat(3u);
v___x_1245_ = lean_byte_array_get(v_bs_1221_, v___x_1244_);
v___x_1246_ = lean_uint8_to_uint32(v___x_1245_);
v___x_1247_ = lean_uint32_lor(v___x_1243_, v___x_1246_);
return v___x_1247_;
}
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_1221_ = stack[0].m_obj;
uint32_t v_res_1248_;
v_res_1248_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_1221_);
stack->m_num = v_res_1248_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___boxed(lean_object* v_bs_1249_){
_start:
{
uint32_t v_res_1250_; lean_object* v_r_1251_; 
v_res_1250_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_1249_);
lean_dec_ref(v_bs_1249_);
v_r_1251_ = lean_box_uint32(v_res_1250_);
return v_r_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(lean_object* v_bs_1252_){
_start:
{
uint32_t v___x_1253_; lean_object* v_n_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1253_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_1252_);
v_n_1254_ = lean_uint32_to_nat(v___x_1253_);
v___x_1255_ = lean_unsigned_to_nat(2147483648u);
v___x_1256_ = lean_nat_dec_lt(v_n_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_cstr_to_nat("4294967296");
v___x_1258_ = lean_nat_sub(v___x_1257_, v_n_1254_);
lean_dec(v_n_1254_);
v___x_1259_ = l_Int_negOfNat(v___x_1258_);
lean_dec(v___x_1258_);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_nat_to_int(v_n_1254_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___boxed(lean_object* v_bs_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(v_bs_1261_);
lean_dec_ref(v_bs_1261_);
return v_res_1262_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0(void){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_cstr_to_nat("9223372036854775808");
return v___x_1263_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1(void){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(lean_object* v_bs_1265_){
_start:
{
uint64_t v___x_1266_; lean_object* v_n_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1266_ = l_ByteArray_toUInt64BE_x21(v_bs_1265_);
v_n_1267_ = lean_uint64_to_nat(v___x_1266_);
v___x_1268_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0);
v___x_1269_ = lean_nat_dec_lt(v_n_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1);
v___x_1271_ = lean_nat_sub(v___x_1270_, v_n_1267_);
lean_dec(v_n_1267_);
v___x_1272_ = l_Int_negOfNat(v___x_1271_);
lean_dec(v___x_1271_);
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_nat_to_int(v_n_1267_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___boxed(lean_object* v_bs_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(v_bs_1274_);
lean_dec_ref(v_bs_1274_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(lean_object* v_upperBound_1276_, lean_object* v_p_1277_, lean_object* v_a_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_nat_dec_lt(v_a_1278_, v_upperBound_1276_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_a_1278_);
lean_dec_ref(v_p_1277_);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___y_1280_);
lean_ctor_set(v___x_1282_, 1, v_b_1279_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; 
lean_inc_ref(v_p_1277_);
v___x_1283_ = lean_apply_1(v_p_1277_, v___y_1280_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_pos_1284_; lean_object* v_res_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_pos_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_pos_1284_);
v_res_1285_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_res_1285_);
lean_dec_ref_known(v___x_1283_, 2);
v___x_1286_ = lean_array_push(v_b_1279_, v_res_1285_);
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_nat_add(v_a_1278_, v___x_1287_);
lean_dec(v_a_1278_);
v_a_1278_ = v___x_1288_;
v_b_1279_ = v___x_1286_;
v___y_1280_ = v_pos_1284_;
goto _start;
}
else
{
lean_object* v_pos_1290_; lean_object* v_err_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_b_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_p_1277_);
v_pos_1290_ = lean_ctor_get(v___x_1283_, 0);
v_err_1291_ = lean_ctor_get(v___x_1283_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1283_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_err_1291_);
lean_inc(v_pos_1290_);
lean_dec(v___x_1283_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_pos_1290_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_err_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg___boxed(lean_object* v_upperBound_1299_, lean_object* v_p_1300_, lean_object* v_a_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_1299_, v_p_1300_, v_a_1301_, v_b_1302_, v___y_1303_);
lean_dec(v_upperBound_1299_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(lean_object* v_n_1307_, lean_object* v_p_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v_result_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_unsigned_to_nat(0u);
v_result_1311_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0));
v___x_1312_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_n_1307_, v_p_1308_, v___x_1310_, v_result_1311_, v_a_1309_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___boxed(lean_object* v_n_1313_, lean_object* v_p_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v_n_1313_, v_p_1314_, v_a_1315_);
lean_dec(v_n_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(lean_object* v_00_u03b1_1317_, lean_object* v_n_1318_, lean_object* v_p_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v_n_1318_, v_p_1319_, v_a_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___boxed(lean_object* v_00_u03b1_1322_, lean_object* v_n_1323_, lean_object* v_p_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(v_00_u03b1_1322_, v_n_1323_, v_p_1324_, v_a_1325_);
lean_dec(v_n_1323_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(lean_object* v_00_u03b1_1327_, lean_object* v_upperBound_1328_, lean_object* v_p_1329_, lean_object* v_inst_1330_, lean_object* v_R_1331_, lean_object* v_a_1332_, lean_object* v_b_1333_, lean_object* v_c_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_1328_, v_p_1329_, v_a_1332_, v_b_1333_, v___y_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_upperBound_1338_, lean_object* v_p_1339_, lean_object* v_inst_1340_, lean_object* v_R_1341_, lean_object* v_a_1342_, lean_object* v_b_1343_, lean_object* v_c_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(v_00_u03b1_1337_, v_upperBound_1338_, v_p_1339_, v_inst_1340_, v_R_1341_, v_a_1342_, v_b_1343_, v_c_1344_, v___y_1345_);
lean_dec(v_upperBound_1338_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu64(lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_unsigned_to_nat(8u);
v___x_1349_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1348_, v_a_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_pos_1350_; lean_object* v_res_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1361_; 
v_pos_1350_ = lean_ctor_get(v___x_1349_, 0);
v_res_1351_ = lean_ctor_get(v___x_1349_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1353_ = v___x_1349_;
v_isShared_1354_ = v_isSharedCheck_1361_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_res_1351_);
lean_inc(v_pos_1350_);
lean_dec(v___x_1349_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1361_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; uint64_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1355_ = l_ByteSlice_toByteArray(v_res_1351_);
v___x_1356_ = l_ByteArray_toUInt64LE_x21(v___x_1355_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = lean_box_uint64(v___x_1356_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1357_);
v___x_1359_ = v___x_1353_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_pos_1350_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_pos_1362_; lean_object* v_err_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
v_pos_1362_ = lean_ctor_get(v___x_1349_, 0);
v_err_1363_ = lean_ctor_get(v___x_1349_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1349_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_err_1363_);
lean_inc(v_pos_1362_);
lean_dec(v___x_1349_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_pos_1362_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_err_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64(lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_unsigned_to_nat(8u);
v___x_1373_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1372_, v_a_1371_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_pos_1374_; lean_object* v_res_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1384_; 
v_pos_1374_ = lean_ctor_get(v___x_1373_, 0);
v_res_1375_ = lean_ctor_get(v___x_1373_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1377_ = v___x_1373_;
v_isShared_1378_ = v_isSharedCheck_1384_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_res_1375_);
lean_inc(v_pos_1374_);
lean_dec(v___x_1373_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1384_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = l_ByteSlice_toByteArray(v_res_1375_);
v___x_1380_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(v___x_1379_);
lean_dec_ref(v___x_1379_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v___x_1380_);
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_pos_1374_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
lean_object* v_pos_1385_; lean_object* v_err_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
v_pos_1385_ = lean_ctor_get(v___x_1373_, 0);
v_err_1386_ = lean_ctor_get(v___x_1373_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1373_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_err_1386_);
lean_inc(v_pos_1385_);
lean_dec(v___x_1373_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_pos_1385_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_err_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_unsigned_to_nat(4u);
v___x_1396_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1395_, v_a_1394_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_pos_1397_; lean_object* v_res_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1408_; 
v_pos_1397_ = lean_ctor_get(v___x_1396_, 0);
v_res_1398_ = lean_ctor_get(v___x_1396_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1400_ = v___x_1396_;
v_isShared_1401_ = v_isSharedCheck_1408_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_res_1398_);
lean_inc(v_pos_1397_);
lean_dec(v___x_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1408_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; uint32_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1402_ = l_ByteSlice_toByteArray(v_res_1398_);
v___x_1403_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v___x_1402_);
lean_dec_ref(v___x_1402_);
v___x_1404_ = lean_box_uint32(v___x_1403_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v___x_1404_);
v___x_1406_ = v___x_1400_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_pos_1397_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
else
{
lean_object* v_pos_1409_; lean_object* v_err_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_pos_1409_ = lean_ctor_get(v___x_1396_, 0);
v_err_1410_ = lean_ctor_get(v___x_1396_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1396_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_err_1410_);
lean_inc(v_pos_1409_);
lean_dec(v___x_1396_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_pos_1409_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_err_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(lean_object* v_a_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_unsigned_to_nat(4u);
v___x_1420_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1419_, v_a_1418_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_pos_1421_; lean_object* v_res_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1431_; 
v_pos_1421_ = lean_ctor_get(v___x_1420_, 0);
v_res_1422_ = lean_ctor_get(v___x_1420_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1424_ = v___x_1420_;
v_isShared_1425_ = v_isSharedCheck_1431_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_res_1422_);
lean_inc(v_pos_1421_);
lean_dec(v___x_1420_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1431_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1426_ = l_ByteSlice_toByteArray(v_res_1422_);
v___x_1427_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(v___x_1426_);
lean_dec_ref(v___x_1426_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 1, v___x_1427_);
v___x_1429_ = v___x_1424_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_pos_1421_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
lean_object* v_pos_1432_; lean_object* v_err_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_pos_1432_ = lean_ctor_get(v___x_1420_, 0);
v_err_1433_ = lean_ctor_get(v___x_1420_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1420_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_err_1433_);
lean_inc(v_pos_1432_);
lean_dec(v___x_1420_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_pos_1432_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_err_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(lean_object* v_a_1441_){
_start:
{
lean_object* v_array_1442_; lean_object* v_idx_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_array_1442_ = lean_ctor_get(v_a_1441_, 0);
v_idx_1443_ = lean_ctor_get(v_a_1441_, 1);
v___x_1444_ = lean_byte_array_size(v_array_1442_);
v___x_1445_ = lean_nat_dec_lt(v_idx_1443_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_box(0);
v___x_1447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1447_, 0, v_a_1441_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
return v___x_1447_;
}
else
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1459_; 
lean_inc(v_idx_1443_);
lean_inc_ref(v_array_1442_);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_a_1441_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; lean_object* v_unused_1461_; 
v_unused_1460_ = lean_ctor_get(v_a_1441_, 1);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_a_1441_, 0);
lean_dec(v_unused_1461_);
v___x_1449_ = v_a_1441_;
v_isShared_1450_ = v_isSharedCheck_1459_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v_a_1441_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1459_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
uint8_t v_c_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_it_x27_1455_; 
v_c_1451_ = lean_byte_array_fget(v_array_1442_, v_idx_1443_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_idx_1443_, v___x_1452_);
lean_dec(v_idx_1443_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 1, v___x_1453_);
v_it_x27_1455_ = v___x_1449_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_array_1442_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v___x_1453_);
v_it_x27_1455_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_box(v_c_1451_);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_it_x27_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
return v___x_1457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_a_1462_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_pos_1464_; lean_object* v_res_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1482_; 
v_pos_1464_ = lean_ctor_get(v___x_1463_, 0);
v_res_1465_ = lean_ctor_get(v___x_1463_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1467_ = v___x_1463_;
v_isShared_1468_ = v_isSharedCheck_1482_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_res_1465_);
lean_inc(v_pos_1464_);
lean_dec(v___x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1482_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
uint8_t v___x_1469_; uint8_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = 0;
v___x_1470_ = lean_unbox(v_res_1465_);
lean_dec(v_res_1465_);
v___x_1471_ = lean_uint8_dec_eq(v___x_1470_, v___x_1469_);
if (v___x_1471_ == 0)
{
uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1472_ = 1;
v___x_1473_ = lean_box(v___x_1472_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v___x_1473_);
v___x_1475_ = v___x_1467_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_pos_1464_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
else
{
uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1477_ = 0;
v___x_1478_ = lean_box(v___x_1477_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v___x_1478_);
v___x_1480_ = v___x_1467_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_pos_1464_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_object* v_pos_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1491_; 
v_pos_1483_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v___x_1463_, 1);
lean_dec(v_unused_1492_);
v___x_1485_ = v___x_1463_;
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_pos_1483_);
lean_dec(v___x_1463_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1487_ = lean_box(0);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1487_);
v___x_1489_ = v___x_1485_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_pos_1483_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0(void){
_start:
{
lean_object* v___x_1493_; lean_object* v_utf8_1494_; 
v___x_1493_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17));
v_utf8_1494_ = lean_string_to_utf8(v___x_1493_);
return v_utf8_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(lean_object* v_a_1495_){
_start:
{
lean_object* v_utf8_1496_; lean_object* v___x_1497_; 
v_utf8_1496_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0);
v___x_1497_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1496_, v_a_1495_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_pos_1498_; lean_object* v___x_1499_; 
v_pos_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_pos_1498_);
lean_dec_ref_known(v___x_1497_, 2);
v___x_1499_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_pos_1498_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_pos_1500_; lean_object* v_res_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_pos_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_pos_1500_);
v_res_1501_ = lean_ctor_get(v___x_1499_, 1);
lean_inc(v_res_1501_);
lean_dec_ref_known(v___x_1499_, 2);
v___x_1502_ = lean_unsigned_to_nat(15u);
v___x_1503_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1502_, v_pos_1500_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_pos_1504_; lean_object* v___x_1505_; 
v_pos_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_pos_1504_);
lean_dec_ref_known(v___x_1503_, 2);
v___x_1505_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1504_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_pos_1506_; lean_object* v_res_1507_; lean_object* v___x_1508_; 
v_pos_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_pos_1506_);
v_res_1507_ = lean_ctor_get(v___x_1505_, 1);
lean_inc(v_res_1507_);
lean_dec_ref_known(v___x_1505_, 2);
v___x_1508_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1506_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_pos_1509_; lean_object* v_res_1510_; lean_object* v___x_1511_; 
v_pos_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_pos_1509_);
v_res_1510_ = lean_ctor_get(v___x_1508_, 1);
lean_inc(v_res_1510_);
lean_dec_ref_known(v___x_1508_, 2);
v___x_1511_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1509_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_pos_1512_; lean_object* v_res_1513_; lean_object* v___x_1514_; 
v_pos_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_pos_1512_);
v_res_1513_ = lean_ctor_get(v___x_1511_, 1);
lean_inc(v_res_1513_);
lean_dec_ref_known(v___x_1511_, 2);
v___x_1514_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1512_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_pos_1515_; lean_object* v_res_1516_; lean_object* v___x_1517_; 
v_pos_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_pos_1515_);
v_res_1516_ = lean_ctor_get(v___x_1514_, 1);
lean_inc(v_res_1516_);
lean_dec_ref_known(v___x_1514_, 2);
v___x_1517_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1515_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_pos_1518_; lean_object* v_res_1519_; lean_object* v___x_1520_; 
v_pos_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_pos_1518_);
v_res_1519_ = lean_ctor_get(v___x_1517_, 1);
lean_inc(v_res_1519_);
lean_dec_ref_known(v___x_1517_, 2);
v___x_1520_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1518_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_pos_1521_; lean_object* v_res_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1537_; 
v_pos_1521_ = lean_ctor_get(v___x_1520_, 0);
v_res_1522_ = lean_ctor_get(v___x_1520_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1524_ = v___x_1520_;
v_isShared_1525_ = v_isSharedCheck_1537_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_res_1522_);
lean_inc(v_pos_1521_);
lean_dec(v___x_1520_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1537_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; uint8_t v___x_1527_; uint32_t v___x_1528_; uint32_t v___x_1529_; uint32_t v___x_1530_; uint32_t v___x_1531_; uint32_t v___x_1532_; uint32_t v___x_1533_; lean_object* v___x_1535_; 
v___x_1526_ = lean_alloc_ctor(0, 0, 25);
v___x_1527_ = lean_unbox(v_res_1501_);
lean_dec(v_res_1501_);
lean_ctor_set_uint8(v___x_1526_, 24, v___x_1527_);
v___x_1528_ = lean_unbox_uint32(v_res_1507_);
lean_dec(v_res_1507_);
lean_ctor_set_uint32(v___x_1526_, 0, v___x_1528_);
v___x_1529_ = lean_unbox_uint32(v_res_1510_);
lean_dec(v_res_1510_);
lean_ctor_set_uint32(v___x_1526_, 4, v___x_1529_);
v___x_1530_ = lean_unbox_uint32(v_res_1513_);
lean_dec(v_res_1513_);
lean_ctor_set_uint32(v___x_1526_, 8, v___x_1530_);
v___x_1531_ = lean_unbox_uint32(v_res_1516_);
lean_dec(v_res_1516_);
lean_ctor_set_uint32(v___x_1526_, 12, v___x_1531_);
v___x_1532_ = lean_unbox_uint32(v_res_1519_);
lean_dec(v_res_1519_);
lean_ctor_set_uint32(v___x_1526_, 16, v___x_1532_);
v___x_1533_ = lean_unbox_uint32(v_res_1522_);
lean_dec(v_res_1522_);
lean_ctor_set_uint32(v___x_1526_, 20, v___x_1533_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 1, v___x_1526_);
v___x_1535_ = v___x_1524_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_pos_1521_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v___x_1526_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
lean_object* v_pos_1538_; lean_object* v_err_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_res_1519_);
lean_dec(v_res_1516_);
lean_dec(v_res_1513_);
lean_dec(v_res_1510_);
lean_dec(v_res_1507_);
lean_dec(v_res_1501_);
v_pos_1538_ = lean_ctor_get(v___x_1520_, 0);
v_err_1539_ = lean_ctor_get(v___x_1520_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1520_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_err_1539_);
lean_inc(v_pos_1538_);
lean_dec(v___x_1520_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_pos_1538_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_err_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_pos_1547_; lean_object* v_err_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_res_1516_);
lean_dec(v_res_1513_);
lean_dec(v_res_1510_);
lean_dec(v_res_1507_);
lean_dec(v_res_1501_);
v_pos_1547_ = lean_ctor_get(v___x_1517_, 0);
v_err_1548_ = lean_ctor_get(v___x_1517_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1517_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_err_1548_);
lean_inc(v_pos_1547_);
lean_dec(v___x_1517_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_pos_1547_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_err_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v_pos_1556_; lean_object* v_err_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_res_1513_);
lean_dec(v_res_1510_);
lean_dec(v_res_1507_);
lean_dec(v_res_1501_);
v_pos_1556_ = lean_ctor_get(v___x_1514_, 0);
v_err_1557_ = lean_ctor_get(v___x_1514_, 1);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1514_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_err_1557_);
lean_inc(v_pos_1556_);
lean_dec(v___x_1514_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_pos_1556_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_err_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_pos_1565_; lean_object* v_err_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_res_1510_);
lean_dec(v_res_1507_);
lean_dec(v_res_1501_);
v_pos_1565_ = lean_ctor_get(v___x_1511_, 0);
v_err_1566_ = lean_ctor_get(v___x_1511_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1511_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_err_1566_);
lean_inc(v_pos_1565_);
lean_dec(v___x_1511_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_pos_1565_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_err_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
lean_object* v_pos_1574_; lean_object* v_err_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_res_1507_);
lean_dec(v_res_1501_);
v_pos_1574_ = lean_ctor_get(v___x_1508_, 0);
v_err_1575_ = lean_ctor_get(v___x_1508_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1508_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_err_1575_);
lean_inc(v_pos_1574_);
lean_dec(v___x_1508_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_pos_1574_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_err_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_pos_1583_; lean_object* v_err_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v_res_1501_);
v_pos_1583_ = lean_ctor_get(v___x_1505_, 0);
v_err_1584_ = lean_ctor_get(v___x_1505_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1505_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_err_1584_);
lean_inc(v_pos_1583_);
lean_dec(v___x_1505_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_pos_1583_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_err_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_pos_1592_; lean_object* v_err_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_res_1501_);
v_pos_1592_ = lean_ctor_get(v___x_1503_, 0);
v_err_1593_ = lean_ctor_get(v___x_1503_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1503_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_err_1593_);
lean_inc(v_pos_1592_);
lean_dec(v___x_1503_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_pos_1592_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_err_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v_pos_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1609_; 
v_pos_1601_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v___x_1499_, 1);
lean_dec(v_unused_1610_);
v___x_1603_ = v___x_1499_;
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_pos_1601_);
lean_dec(v___x_1499_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_box(0);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1605_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_pos_1601_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v_pos_1611_; lean_object* v_err_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_pos_1611_ = lean_ctor_get(v___x_1497_, 0);
v_err_1612_ = lean_ctor_get(v___x_1497_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1497_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_err_1612_);
lean_inc(v_pos_1611_);
lean_dec(v___x_1497_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_pos_1611_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_err_1612_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType(lean_object* v_a_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(v_a_1620_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_pos_1622_; lean_object* v_res_1623_; lean_object* v___x_1624_; 
v_pos_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_pos_1622_);
v_res_1623_ = lean_ctor_get(v___x_1621_, 1);
lean_inc(v_res_1623_);
lean_dec_ref_known(v___x_1621_, 2);
v___x_1624_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(v_pos_1622_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_pos_1625_; lean_object* v_res_1626_; lean_object* v___x_1627_; 
v_pos_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_pos_1625_);
v_res_1626_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_res_1626_);
lean_dec_ref_known(v___x_1624_, 2);
v___x_1627_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_pos_1625_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_pos_1628_; lean_object* v_res_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1639_; 
v_pos_1628_ = lean_ctor_get(v___x_1627_, 0);
v_res_1629_ = lean_ctor_get(v___x_1627_, 1);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1631_ = v___x_1627_;
v_isShared_1632_ = v_isSharedCheck_1639_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_res_1629_);
lean_inc(v_pos_1628_);
lean_dec(v___x_1627_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1639_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; uint8_t v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1637_; 
v___x_1633_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1633_, 0, v_res_1623_);
v___x_1634_ = lean_unbox(v_res_1626_);
lean_dec(v_res_1626_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*1, v___x_1634_);
v___x_1635_ = lean_unbox(v_res_1629_);
lean_dec(v_res_1629_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*1 + 1, v___x_1635_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 1, v___x_1633_);
v___x_1637_ = v___x_1631_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_pos_1628_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v___x_1633_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
else
{
lean_object* v_pos_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_res_1626_);
lean_dec(v_res_1623_);
v_pos_1640_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; 
v_unused_1649_ = lean_ctor_get(v___x_1627_, 1);
lean_dec(v_unused_1649_);
v___x_1642_ = v___x_1627_;
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_pos_1640_);
lean_dec(v___x_1627_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_box(0);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___x_1644_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_pos_1640_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
lean_object* v_pos_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_res_1623_);
v_pos_1650_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v___x_1624_, 1);
lean_dec(v_unused_1659_);
v___x_1652_ = v___x_1624_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_pos_1650_);
lean_dec(v___x_1624_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_box(0);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v___x_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_pos_1650_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_pos_1660_; lean_object* v_err_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_pos_1660_ = lean_ctor_get(v___x_1621_, 0);
v_err_1661_ = lean_ctor_get(v___x_1621_, 1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1621_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_err_1661_);
lean_inc(v_pos_1660_);
lean_dec(v___x_1621_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_pos_1660_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_err_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond(lean_object* v_p_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_apply_1(v_p_1669_, v_a_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_pos_1672_; lean_object* v_res_1673_; lean_object* v___x_1674_; 
v_pos_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_pos_1672_);
v_res_1673_ = lean_ctor_get(v___x_1671_, 1);
lean_inc(v_res_1673_);
lean_dec_ref_known(v___x_1671_, 2);
v___x_1674_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(v_pos_1672_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_pos_1675_; lean_object* v_res_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1684_; 
v_pos_1675_ = lean_ctor_get(v___x_1674_, 0);
v_res_1676_ = lean_ctor_get(v___x_1674_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1678_ = v___x_1674_;
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_res_1676_);
lean_inc(v_pos_1675_);
lean_dec(v___x_1674_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v_res_1673_);
lean_ctor_set(v___x_1680_, 1, v_res_1676_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v___x_1680_);
v___x_1682_ = v___x_1678_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_pos_1675_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
else
{
lean_object* v_pos_1685_; lean_object* v_err_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_res_1673_);
v_pos_1685_ = lean_ctor_get(v___x_1674_, 0);
v_err_1686_ = lean_ctor_get(v___x_1674_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1674_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_err_1686_);
lean_inc(v_pos_1685_);
lean_dec(v___x_1674_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_pos_1685_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_err_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_object* v_pos_1694_; lean_object* v_err_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_pos_1694_ = lean_ctor_get(v___x_1671_, 0);
v_err_1695_ = lean_ctor_get(v___x_1671_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1671_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_err_1695_);
lean_inc(v_pos_1694_);
lean_dec(v___x_1671_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_pos_1694_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_err_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(lean_object* v_size_1703_, uint32_t v_n_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_uint32_to_nat(v_n_1704_);
v___x_1707_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1706_, v_size_1703_, v_a_1705_);
lean_dec(v___x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes_0interp(lean_interpreter_value* stack)
{
lean_object* v_size_1703_ = stack[0].m_obj;
uint32_t v_n_1704_ = stack[1].m_num;
lean_object* v_a_1705_ = stack[2].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v_size_1703_, v_n_1704_, v_a_1705_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes___boxed(lean_object* v_size_1709_, lean_object* v_n_1710_, lean_object* v_a_1711_){
_start:
{
uint32_t v_n_boxed_1712_; lean_object* v_res_1713_; 
v_n_boxed_1712_ = lean_unbox_uint32(v_n_1710_);
lean_dec(v_n_1710_);
v_res_1713_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v_size_1709_, v_n_boxed_1712_, v_a_1711_);
return v_res_1713_;
}
}
lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(uint32_t v_n_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = lean_uint32_to_nat(v_n_1714_);
v___x_1717_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8), 1, 0);
v___x_1718_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1716_, v___x_1717_, v_a_1715_);
lean_dec(v___x_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_1714_ = stack[0].m_num;
lean_object* v_a_1715_ = stack[1].m_obj;
lean_object* v_res_1719_;
v_res_1719_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_n_1714_, v_a_1715_);
stack->m_obj
 = v_res_1719_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices___boxed(lean_object* v_n_1720_, lean_object* v_a_1721_){
_start:
{
uint32_t v_n_boxed_1722_; lean_object* v_res_1723_; 
v_n_boxed_1722_ = lean_unbox_uint32(v_n_1720_);
lean_dec(v_n_1720_);
v_res_1723_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_n_boxed_1722_, v_a_1721_);
return v_res_1723_;
}
}
lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(uint32_t v_n_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = lean_uint32_to_nat(v_n_1724_);
v___x_1727_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType), 1, 0);
v___x_1728_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1726_, v___x_1727_, v_a_1725_);
lean_dec(v___x_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_1724_ = stack[0].m_num;
lean_object* v_a_1725_ = stack[1].m_obj;
lean_object* v_res_1729_;
v_res_1729_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_n_1724_, v_a_1725_);
stack->m_obj
 = v_res_1729_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes___boxed(lean_object* v_n_1730_, lean_object* v_a_1731_){
_start:
{
uint32_t v_n_boxed_1732_; lean_object* v_res_1733_; 
v_n_boxed_1732_ = lean_unbox_uint32(v_n_1730_);
lean_dec(v_n_1730_);
v_res_1733_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_n_boxed_1732_, v_a_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(lean_object* v_upperBound_1735_, lean_object* v_res_1736_, lean_object* v_a_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_nat_dec_lt(v_a_1737_, v_upperBound_1735_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_dec(v_a_1737_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___y_1739_);
lean_ctor_set(v___x_1741_, 1, v_b_1738_);
return v___x_1741_;
}
else
{
lean_object* v_fst_1742_; lean_object* v_snd_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1767_; 
v_fst_1742_ = lean_ctor_get(v_b_1738_, 0);
v_snd_1743_ = lean_ctor_get(v_b_1738_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_b_1738_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1745_ = v_b_1738_;
v_isShared_1746_ = v_isSharedCheck_1767_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_snd_1743_);
lean_inc(v_fst_1742_);
lean_dec(v_b_1738_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1767_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1747_ = 0;
v___x_1748_ = lean_box(v___x_1747_);
v___x_1749_ = lean_array_get(v___x_1748_, v_res_1736_, v_a_1737_);
lean_dec(v___x_1748_);
v___x_1750_ = lean_unbox(v___x_1749_);
v___x_1751_ = lean_uint8_dec_eq(v___x_1750_, v___x_1747_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; uint32_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1752_ = lean_unbox(v___x_1749_);
lean_dec(v___x_1749_);
v___x_1753_ = lean_uint8_to_uint32(v___x_1752_);
v___x_1754_ = lean_string_push(v_snd_1743_, v___x_1753_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v___x_1754_);
v___x_1756_ = v___x_1745_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_fst_1742_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_unsigned_to_nat(1u);
v___x_1758_ = lean_nat_add(v_a_1737_, v___x_1757_);
lean_dec(v_a_1737_);
v_a_1737_ = v___x_1758_;
v_b_1738_ = v___x_1756_;
goto _start;
}
}
else
{
lean_object* v_current_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_dec(v___x_1749_);
lean_dec(v_a_1737_);
v_current_1761_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0));
v___x_1762_ = lean_array_push(v_fst_1742_, v_snd_1743_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_current_1761_);
lean_ctor_set(v___x_1745_, 0, v___x_1762_);
v___x_1764_ = v___x_1745_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_current_1761_);
v___x_1764_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___y_1739_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
return v___x_1765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___boxed(lean_object* v_upperBound_1768_, lean_object* v_res_1769_, lean_object* v_a_1770_, lean_object* v_b_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_1768_, v_res_1769_, v_a_1770_, v_b_1771_, v___y_1772_);
lean_dec_ref(v_res_1769_);
lean_dec(v_upperBound_1768_);
return v_res_1773_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(lean_object* v___x_1774_, lean_object* v_res_1775_, lean_object* v_as_1776_, size_t v_sz_1777_, size_t v_i_1778_, lean_object* v_b_1779_, lean_object* v___y_1780_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_usize_dec_lt(v_i_1778_, v_sz_1777_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___y_1780_);
lean_ctor_set(v___x_1782_, 1, v_b_1779_);
return v___x_1782_;
}
else
{
lean_object* v_a_1783_; uint8_t v_abbreviationIndex_1784_; lean_object* v_fst_1785_; lean_object* v_snd_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1809_; 
v_a_1783_ = lean_array_uget_borrowed(v_as_1776_, v_i_1778_);
v_abbreviationIndex_1784_ = lean_ctor_get_uint8(v_a_1783_, sizeof(void*)*1 + 1);
v_fst_1785_ = lean_ctor_get(v_b_1779_, 0);
v_snd_1786_ = lean_ctor_get(v_b_1779_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_b_1779_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1788_ = v_b_1779_;
v_isShared_1789_ = v_isSharedCheck_1809_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_snd_1786_);
lean_inc(v_fst_1785_);
lean_dec(v_b_1779_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1809_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1790_ = lean_uint8_to_nat(v_abbreviationIndex_1784_);
if (v_isShared_1789_ == 0)
{
v___x_1792_ = v___x_1788_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_fst_1785_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_snd_1786_);
v___x_1792_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v___x_1774_, v_res_1775_, v___x_1790_, v___x_1792_, v___y_1780_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_res_1794_; lean_object* v_pos_1795_; lean_object* v_fst_1796_; lean_object* v_snd_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1807_; 
v_res_1794_ = lean_ctor_get(v___x_1793_, 1);
lean_inc(v_res_1794_);
v_pos_1795_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_pos_1795_);
lean_dec_ref_known(v___x_1793_, 2);
v_fst_1796_ = lean_ctor_get(v_res_1794_, 0);
v_snd_1797_ = lean_ctor_get(v_res_1794_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_res_1794_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1799_ = v_res_1794_;
v_isShared_1800_ = v_isSharedCheck_1807_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_snd_1797_);
lean_inc(v_fst_1796_);
lean_dec(v_res_1794_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1807_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_fst_1796_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_snd_1797_);
v___x_1802_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
size_t v___x_1803_; size_t v___x_1804_; 
v___x_1803_ = ((size_t)1ULL);
v___x_1804_ = lean_usize_add(v_i_1778_, v___x_1803_);
v_i_1778_ = v___x_1804_;
v_b_1779_ = v___x_1802_;
v___y_1780_ = v_pos_1795_;
goto _start;
}
}
}
else
{
return v___x_1793_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1774_ = stack[0].m_obj;
lean_object* v_res_1775_ = stack[1].m_obj;
lean_object* v_as_1776_ = stack[2].m_obj;
size_t v_sz_1777_ = stack[3].m_num;
size_t v_i_1778_ = stack[4].m_num;
lean_object* v_b_1779_ = stack[5].m_obj;
lean_object* v___y_1780_ = stack[6].m_obj;
lean_object* v_res_1810_;
v_res_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_1774_, v_res_1775_, v_as_1776_, v_sz_1777_, v_i_1778_, v_b_1779_, v___y_1780_);
stack->m_obj
 = v_res_1810_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1___boxed(lean_object* v___x_1811_, lean_object* v_res_1812_, lean_object* v_as_1813_, lean_object* v_sz_1814_, lean_object* v_i_1815_, lean_object* v_b_1816_, lean_object* v___y_1817_){
_start:
{
size_t v_sz_boxed_1818_; size_t v_i_boxed_1819_; lean_object* v_res_1820_; 
v_sz_boxed_1818_ = lean_unbox_usize(v_sz_1814_);
lean_dec(v_sz_1814_);
v_i_boxed_1819_ = lean_unbox_usize(v_i_1815_);
lean_dec(v_i_1815_);
v_res_1820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_1811_, v_res_1812_, v_as_1813_, v_sz_boxed_1818_, v_i_boxed_1819_, v_b_1816_, v___y_1817_);
lean_dec_ref(v_as_1813_);
lean_dec_ref(v_res_1812_);
lean_dec(v___x_1811_);
return v_res_1820_;
}
}
lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(lean_object* v_times_1826_, uint32_t v_n_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = lean_uint32_to_nat(v_n_1827_);
v___x_1830_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8), 1, 0);
v___x_1831_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1829_, v___x_1830_, v_a_1828_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_pos_1832_; lean_object* v_res_1833_; lean_object* v___x_1834_; size_t v_sz_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v_pos_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_pos_1832_);
v_res_1833_ = lean_ctor_get(v___x_1831_, 1);
lean_inc(v_res_1833_);
lean_dec_ref_known(v___x_1831_, 2);
v___x_1834_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1));
v_sz_1835_ = lean_array_size(v_times_1826_);
v___x_1836_ = ((size_t)0ULL);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_1829_, v_res_1833_, v_times_1826_, v_sz_1835_, v___x_1836_, v___x_1834_, v_pos_1832_);
lean_dec(v_res_1833_);
lean_dec(v___x_1829_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_res_1838_; lean_object* v_pos_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1847_; 
v_res_1838_ = lean_ctor_get(v___x_1837_, 1);
v_pos_1839_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1841_ = v___x_1837_;
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_res_1838_);
lean_inc(v_pos_1839_);
lean_dec(v___x_1837_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_fst_1843_; lean_object* v___x_1845_; 
v_fst_1843_ = lean_ctor_get(v_res_1838_, 0);
lean_inc(v_fst_1843_);
lean_dec(v_res_1838_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v_fst_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_pos_1839_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_fst_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_object* v_pos_1848_; lean_object* v_err_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_pos_1848_ = lean_ctor_get(v___x_1837_, 0);
v_err_1849_ = lean_ctor_get(v___x_1837_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1837_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_err_1849_);
lean_inc(v_pos_1848_);
lean_dec(v___x_1837_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_pos_1848_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_err_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v_pos_1857_; lean_object* v_err_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v___x_1829_);
v_pos_1857_ = lean_ctor_get(v___x_1831_, 0);
v_err_1858_ = lean_ctor_get(v___x_1831_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1831_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_err_1858_);
lean_inc(v_pos_1857_);
lean_dec(v___x_1831_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_pos_1857_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_err_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_0interp(lean_interpreter_value* stack)
{
lean_object* v_times_1826_ = stack[0].m_obj;
uint32_t v_n_1827_ = stack[1].m_num;
lean_object* v_a_1828_ = stack[2].m_obj;
lean_object* v_res_1866_;
v_res_1866_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_times_1826_, v_n_1827_, v_a_1828_);
stack->m_obj
 = v_res_1866_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___boxed(lean_object* v_times_1867_, lean_object* v_n_1868_, lean_object* v_a_1869_){
_start:
{
uint32_t v_n_boxed_1870_; lean_object* v_res_1871_; 
v_n_boxed_1870_ = lean_unbox_uint32(v_n_1868_);
lean_dec(v_n_1868_);
v_res_1871_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_times_1867_, v_n_boxed_1870_, v_a_1869_);
lean_dec_ref(v_times_1867_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(lean_object* v_upperBound_1872_, lean_object* v_res_1873_, lean_object* v_inst_1874_, lean_object* v_R_1875_, lean_object* v_a_1876_, lean_object* v_b_1877_, lean_object* v_c_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_1872_, v_res_1873_, v_a_1876_, v_b_1877_, v___y_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___boxed(lean_object* v_upperBound_1881_, lean_object* v_res_1882_, lean_object* v_inst_1883_, lean_object* v_R_1884_, lean_object* v_a_1885_, lean_object* v_b_1886_, lean_object* v_c_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(v_upperBound_1881_, v_res_1882_, v_inst_1883_, v_R_1884_, v_a_1885_, v_b_1886_, v_c_1887_, v___y_1888_);
lean_dec_ref(v_res_1882_);
lean_dec(v_upperBound_1881_);
return v_res_1889_;
}
}
lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(lean_object* v_size_1890_, uint32_t v_n_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_uint32_to_nat(v_n_1891_);
v___x_1894_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond), 2, 1);
lean_closure_set(v___x_1894_, 0, v_size_1890_);
v___x_1895_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1893_, v___x_1894_, v_a_1892_);
lean_dec(v___x_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds_0interp(lean_interpreter_value* stack)
{
lean_object* v_size_1890_ = stack[0].m_obj;
uint32_t v_n_1891_ = stack[1].m_num;
lean_object* v_a_1892_ = stack[2].m_obj;
lean_object* v_res_1896_;
v_res_1896_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v_size_1890_, v_n_1891_, v_a_1892_);
stack->m_obj
 = v_res_1896_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds___boxed(lean_object* v_size_1897_, lean_object* v_n_1898_, lean_object* v_a_1899_){
_start:
{
uint32_t v_n_boxed_1900_; lean_object* v_res_1901_; 
v_n_boxed_1900_ = lean_unbox_uint32(v_n_1898_);
lean_dec(v_n_1898_);
v_res_1901_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v_size_1897_, v_n_boxed_1900_, v_a_1899_);
return v_res_1901_;
}
}
lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(uint32_t v_n_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_uint32_to_nat(v_n_1902_);
v___x_1905_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool), 1, 0);
v___x_1906_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1904_, v___x_1905_, v_a_1903_);
lean_dec(v___x_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_1902_ = stack[0].m_num;
lean_object* v_a_1903_ = stack[1].m_obj;
lean_object* v_res_1907_;
v_res_1907_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_n_1902_, v_a_1903_);
stack->m_obj
 = v_res_1907_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators___boxed(lean_object* v_n_1908_, lean_object* v_a_1909_){
_start:
{
uint32_t v_n_boxed_1910_; lean_object* v_res_1911_; 
v_n_boxed_1910_ = lean_unbox_uint32(v_n_1908_);
lean_dec(v_n_1908_);
v_res_1911_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_n_boxed_1910_, v_a_1909_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(lean_object* v_a_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(v_a_1912_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_res_1914_; lean_object* v_pos_1915_; uint32_t v_isutcnt_1916_; uint32_t v_isstdcnt_1917_; uint32_t v_leapcnt_1918_; uint32_t v_timecnt_1919_; uint32_t v_typecnt_1920_; uint32_t v_charcnt_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_res_1914_ = lean_ctor_get(v___x_1913_, 1);
lean_inc(v_res_1914_);
v_pos_1915_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_pos_1915_);
lean_dec_ref_known(v___x_1913_, 2);
v_isutcnt_1916_ = lean_ctor_get_uint32(v_res_1914_, 0);
v_isstdcnt_1917_ = lean_ctor_get_uint32(v_res_1914_, 4);
v_leapcnt_1918_ = lean_ctor_get_uint32(v_res_1914_, 8);
v_timecnt_1919_ = lean_ctor_get_uint32(v_res_1914_, 12);
v_typecnt_1920_ = lean_ctor_get_uint32(v_res_1914_, 16);
v_charcnt_1921_ = lean_ctor_get_uint32(v_res_1914_, 20);
v___x_1922_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32), 1, 0);
lean_inc_ref(v___x_1922_);
v___x_1923_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_1922_, v_timecnt_1919_, v_pos_1915_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_pos_1924_; lean_object* v_res_1925_; lean_object* v___x_1926_; 
v_pos_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_pos_1924_);
v_res_1925_ = lean_ctor_get(v___x_1923_, 1);
lean_inc(v_res_1925_);
lean_dec_ref_known(v___x_1923_, 2);
v___x_1926_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_1919_, v_pos_1924_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_pos_1927_; lean_object* v_res_1928_; lean_object* v___x_1929_; 
v_pos_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_pos_1927_);
v_res_1928_ = lean_ctor_get(v___x_1926_, 1);
lean_inc(v_res_1928_);
lean_dec_ref_known(v___x_1926_, 2);
v___x_1929_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_1920_, v_pos_1927_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_pos_1930_; lean_object* v_res_1931_; lean_object* v___x_1932_; 
v_pos_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_pos_1930_);
v_res_1931_ = lean_ctor_get(v___x_1929_, 1);
lean_inc(v_res_1931_);
lean_dec_ref_known(v___x_1929_, 2);
v___x_1932_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_1931_, v_charcnt_1921_, v_pos_1930_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_pos_1933_; lean_object* v_res_1934_; lean_object* v___x_1935_; 
v_pos_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_pos_1933_);
v_res_1934_ = lean_ctor_get(v___x_1932_, 1);
lean_inc(v_res_1934_);
lean_dec_ref_known(v___x_1932_, 2);
v___x_1935_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_1922_, v_leapcnt_1918_, v_pos_1933_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_pos_1936_; lean_object* v_res_1937_; lean_object* v___x_1938_; 
v_pos_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_pos_1936_);
v_res_1937_ = lean_ctor_get(v___x_1935_, 1);
lean_inc(v_res_1937_);
lean_dec_ref_known(v___x_1935_, 2);
v___x_1938_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_1917_, v_pos_1936_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_pos_1939_; lean_object* v_res_1940_; lean_object* v___x_1941_; 
v_pos_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_pos_1939_);
v_res_1940_ = lean_ctor_get(v___x_1938_, 1);
lean_inc(v_res_1940_);
lean_dec_ref_known(v___x_1938_, 2);
v___x_1941_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_1916_, v_pos_1939_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_pos_1942_; lean_object* v_res_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1951_; 
v_pos_1942_ = lean_ctor_get(v___x_1941_, 0);
v_res_1943_ = lean_ctor_get(v___x_1941_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1945_ = v___x_1941_;
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_res_1943_);
lean_inc(v_pos_1942_);
lean_dec(v___x_1941_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1947_, 0, v_res_1914_);
lean_ctor_set(v___x_1947_, 1, v_res_1925_);
lean_ctor_set(v___x_1947_, 2, v_res_1928_);
lean_ctor_set(v___x_1947_, 3, v_res_1931_);
lean_ctor_set(v___x_1947_, 4, v_res_1934_);
lean_ctor_set(v___x_1947_, 5, v_res_1937_);
lean_ctor_set(v___x_1947_, 6, v_res_1940_);
lean_ctor_set(v___x_1947_, 7, v_res_1943_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1947_);
v___x_1949_ = v___x_1945_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_pos_1942_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
else
{
lean_object* v_pos_1952_; lean_object* v_err_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_res_1940_);
lean_dec(v_res_1937_);
lean_dec(v_res_1934_);
lean_dec(v_res_1931_);
lean_dec(v_res_1928_);
lean_dec(v_res_1925_);
lean_dec(v_res_1914_);
v_pos_1952_ = lean_ctor_get(v___x_1941_, 0);
v_err_1953_ = lean_ctor_get(v___x_1941_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1941_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_err_1953_);
lean_inc(v_pos_1952_);
lean_dec(v___x_1941_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_pos_1952_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_err_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_pos_1961_; lean_object* v_err_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_res_1937_);
lean_dec(v_res_1934_);
lean_dec(v_res_1931_);
lean_dec(v_res_1928_);
lean_dec(v_res_1925_);
lean_dec(v_res_1914_);
v_pos_1961_ = lean_ctor_get(v___x_1938_, 0);
v_err_1962_ = lean_ctor_get(v___x_1938_, 1);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1938_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_err_1962_);
lean_inc(v_pos_1961_);
lean_dec(v___x_1938_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_pos_1961_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_err_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_pos_1970_; lean_object* v_err_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v_res_1934_);
lean_dec(v_res_1931_);
lean_dec(v_res_1928_);
lean_dec(v_res_1925_);
lean_dec(v_res_1914_);
v_pos_1970_ = lean_ctor_get(v___x_1935_, 0);
v_err_1971_ = lean_ctor_get(v___x_1935_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1935_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_err_1971_);
lean_inc(v_pos_1970_);
lean_dec(v___x_1935_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_pos_1970_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_err_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v_pos_1979_; lean_object* v_err_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_res_1931_);
lean_dec(v_res_1928_);
lean_dec(v_res_1925_);
lean_dec_ref(v___x_1922_);
lean_dec(v_res_1914_);
v_pos_1979_ = lean_ctor_get(v___x_1932_, 0);
v_err_1980_ = lean_ctor_get(v___x_1932_, 1);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1932_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_err_1980_);
lean_inc(v_pos_1979_);
lean_dec(v___x_1932_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_pos_1979_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_err_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_pos_1988_; lean_object* v_err_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_res_1928_);
lean_dec(v_res_1925_);
lean_dec_ref(v___x_1922_);
lean_dec(v_res_1914_);
v_pos_1988_ = lean_ctor_get(v___x_1929_, 0);
v_err_1989_ = lean_ctor_get(v___x_1929_, 1);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1929_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_err_1989_);
lean_inc(v_pos_1988_);
lean_dec(v___x_1929_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_pos_1988_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_err_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_pos_1997_; lean_object* v_err_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec(v_res_1925_);
lean_dec_ref(v___x_1922_);
lean_dec(v_res_1914_);
v_pos_1997_ = lean_ctor_get(v___x_1926_, 0);
v_err_1998_ = lean_ctor_get(v___x_1926_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1926_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_err_1998_);
lean_inc(v_pos_1997_);
lean_dec(v___x_1926_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_pos_1997_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_err_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
else
{
lean_object* v_pos_2006_; lean_object* v_err_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec_ref(v___x_1922_);
lean_dec(v_res_1914_);
v_pos_2006_ = lean_ctor_get(v___x_1923_, 0);
v_err_2007_ = lean_ctor_get(v___x_1923_, 1);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1923_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_err_2007_);
lean_inc(v_pos_2006_);
lean_dec(v___x_1923_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_pos_2006_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_err_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v_pos_2015_; lean_object* v_err_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_pos_2015_ = lean_ctor_get(v___x_1913_, 0);
v_err_2016_ = lean_ctor_get(v___x_1913_, 1);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1913_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_err_2016_);
lean_inc(v_pos_2015_);
lean_dec(v___x_1913_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_pos_2015_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_err_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(lean_object* v_as_2024_, size_t v_sz_2025_, size_t v_i_2026_, lean_object* v_b_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_usize_dec_lt(v_i_2026_, v_sz_2025_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___y_2028_);
lean_ctor_set(v___x_2030_, 1, v_b_2027_);
return v___x_2030_;
}
else
{
lean_object* v_a_2031_; uint8_t v___x_2032_; uint32_t v___x_2033_; lean_object* v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; 
v_a_2031_ = lean_array_uget_borrowed(v_as_2024_, v_i_2026_);
v___x_2032_ = lean_unbox(v_a_2031_);
v___x_2033_ = lean_uint8_to_uint32(v___x_2032_);
v___x_2034_ = lean_string_push(v_b_2027_, v___x_2033_);
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_add(v_i_2026_, v___x_2035_);
v_i_2026_ = v___x_2036_;
v_b_2027_ = v___x_2034_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2024_ = stack[0].m_obj;
size_t v_sz_2025_ = stack[1].m_num;
size_t v_i_2026_ = stack[2].m_num;
lean_object* v_b_2027_ = stack[3].m_obj;
lean_object* v___y_2028_ = stack[4].m_obj;
lean_object* v_res_2038_;
v_res_2038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_as_2024_, v_sz_2025_, v_i_2026_, v_b_2027_, v___y_2028_);
stack->m_obj
 = v_res_2038_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1___boxed(lean_object* v_as_2039_, lean_object* v_sz_2040_, lean_object* v_i_2041_, lean_object* v_b_2042_, lean_object* v___y_2043_){
_start:
{
size_t v_sz_boxed_2044_; size_t v_i_boxed_2045_; lean_object* v_res_2046_; 
v_sz_boxed_2044_ = lean_unbox_usize(v_sz_2040_);
lean_dec(v_sz_2040_);
v_i_boxed_2045_ = lean_unbox_usize(v_i_2041_);
lean_dec(v_i_2041_);
v_res_2046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_as_2039_, v_sz_boxed_2044_, v_i_boxed_2045_, v_b_2042_, v___y_2043_);
lean_dec_ref(v_as_2039_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(lean_object* v_acc_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_array_2052_; lean_object* v_idx_2053_; lean_object* v_pos_2055_; lean_object* v_idx_2056_; lean_object* v_err_2057_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_array_2052_ = lean_ctor_get(v_a_2051_, 0);
v_idx_2053_ = lean_ctor_get(v_a_2051_, 1);
lean_inc(v_idx_2053_);
v___x_2063_ = lean_byte_array_size(v_array_2052_);
v___x_2064_ = lean_nat_dec_lt(v_idx_2053_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_box(0);
lean_inc(v_idx_2053_);
v_pos_2055_ = v_a_2051_;
v_idx_2056_ = v_idx_2053_;
v_err_2057_ = v___x_2065_;
goto v___jp_2054_;
}
else
{
uint8_t v___x_2066_; uint8_t v_c_2067_; uint8_t v___x_2068_; 
v___x_2066_ = 10;
v_c_2067_ = lean_byte_array_fget(v_array_2052_, v_idx_2053_);
v___x_2068_ = lean_uint8_dec_eq(v_c_2067_, v___x_2066_);
if (v___x_2068_ == 0)
{
if (v___x_2064_ == 0)
{
goto v___jp_2061_;
}
else
{
lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2080_; 
lean_inc_ref(v_array_2052_);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_a_2051_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; lean_object* v_unused_2082_; 
v_unused_2081_ = lean_ctor_get(v_a_2051_, 1);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v_a_2051_, 0);
lean_dec(v_unused_2082_);
v___x_2070_ = v_a_2051_;
v_isShared_2071_ = v_isSharedCheck_2080_;
goto v_resetjp_2069_;
}
else
{
lean_dec(v_a_2051_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2080_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v_it_x27_2075_; 
v___x_2072_ = lean_unsigned_to_nat(1u);
v___x_2073_ = lean_nat_add(v_idx_2053_, v___x_2072_);
lean_dec(v_idx_2053_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2073_);
v_it_x27_2075_ = v___x_2070_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_array_2052_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2073_);
v_it_x27_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_box(v_c_2067_);
v___x_2077_ = lean_array_push(v_acc_2050_, v___x_2076_);
v_acc_2050_ = v___x_2077_;
v_a_2051_ = v_it_x27_2075_;
goto _start;
}
}
}
}
else
{
goto v___jp_2061_;
}
}
v___jp_2054_:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_nat_dec_eq(v_idx_2053_, v_idx_2056_);
lean_dec(v_idx_2056_);
lean_dec(v_idx_2053_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; 
lean_dec_ref(v_acc_2050_);
lean_inc(v_err_2057_);
v___x_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2059_, 0, v_pos_2055_);
lean_ctor_set(v___x_2059_, 1, v_err_2057_);
return v___x_2059_;
}
else
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v_pos_2055_);
lean_ctor_set(v___x_2060_, 1, v_acc_2050_);
return v___x_2060_;
}
}
v___jp_2061_:
{
lean_object* v___x_2062_; 
v___x_2062_ = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1));
lean_inc(v_idx_2053_);
v_pos_2055_ = v_a_2051_;
v_idx_2056_ = v_idx_2053_;
v_err_2057_ = v___x_2062_;
goto v___jp_2054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_a_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_pos_2087_; lean_object* v_res_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2135_; 
v_pos_2087_ = lean_ctor_get(v___x_2086_, 0);
v_res_2088_ = lean_ctor_get(v___x_2086_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2090_ = v___x_2086_;
v_isShared_2091_ = v_isSharedCheck_2135_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_res_2088_);
lean_inc(v_pos_2087_);
lean_dec(v___x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2135_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
uint8_t v___x_2092_; uint8_t v___x_2093_; uint8_t v___x_2094_; 
v___x_2092_ = 10;
v___x_2093_ = lean_unbox(v_res_2088_);
lean_dec(v_res_2088_);
v___x_2094_ = lean_uint8_dec_eq(v___x_2093_, v___x_2092_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_box(0);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2095_);
v___x_2097_ = v___x_2090_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_pos_2087_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_del_object(v___x_2090_);
v___x_2099_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0));
v___x_2100_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(v___x_2099_, v_pos_2087_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_pos_2101_; lean_object* v_res_2102_; lean_object* v___x_2103_; size_t v_sz_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
v_pos_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_pos_2101_);
v_res_2102_ = lean_ctor_get(v___x_2100_, 1);
lean_inc(v_res_2102_);
lean_dec_ref_known(v___x_2100_, 2);
v___x_2103_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0));
v_sz_2104_ = lean_array_size(v_res_2102_);
v___x_2105_ = ((size_t)0ULL);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_res_2102_, v_sz_2104_, v___x_2105_, v___x_2103_, v_pos_2101_);
lean_dec(v_res_2102_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_pos_2107_; lean_object* v_res_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2116_; 
v_pos_2107_ = lean_ctor_get(v___x_2106_, 0);
v_res_2108_ = lean_ctor_get(v___x_2106_, 1);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2110_ = v___x_2106_;
v_isShared_2111_ = v_isSharedCheck_2116_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_res_2108_);
lean_inc(v_pos_2107_);
lean_dec(v___x_2106_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2116_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_res_2108_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 1, v___x_2112_);
v___x_2114_ = v___x_2110_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_pos_2107_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
else
{
lean_object* v_pos_2117_; lean_object* v_err_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
v_pos_2117_ = lean_ctor_get(v___x_2106_, 0);
v_err_2118_ = lean_ctor_get(v___x_2106_, 1);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2106_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_err_2118_);
lean_inc(v_pos_2117_);
lean_dec(v___x_2106_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_pos_2117_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_err_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_object* v_pos_2126_; lean_object* v_err_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
v_pos_2126_ = lean_ctor_get(v___x_2100_, 0);
v_err_2127_ = lean_ctor_get(v___x_2100_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2100_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_err_2127_);
lean_inc(v_pos_2126_);
lean_dec(v___x_2100_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_pos_2126_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_err_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
else
{
lean_object* v_pos_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2144_; 
v_pos_2136_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v___x_2086_, 1);
lean_dec(v_unused_2145_);
v___x_2138_ = v___x_2086_;
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_pos_2136_);
lean_dec(v___x_2086_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_box(0);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 1, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_pos_2136_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(lean_object* v_a_2146_){
_start:
{
lean_object* v_pos_2148_; lean_object* v_err_2149_; lean_object* v___x_2165_; 
lean_inc_ref(v_a_2146_);
v___x_2165_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(v_a_2146_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_res_2166_; lean_object* v_pos_2167_; uint32_t v_isutcnt_2168_; uint32_t v_isstdcnt_2169_; uint32_t v_leapcnt_2170_; uint32_t v_timecnt_2171_; uint32_t v_typecnt_2172_; uint32_t v_charcnt_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_res_2166_ = lean_ctor_get(v___x_2165_, 1);
lean_inc(v_res_2166_);
v_pos_2167_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_pos_2167_);
lean_dec_ref_known(v___x_2165_, 2);
v_isutcnt_2168_ = lean_ctor_get_uint32(v_res_2166_, 0);
v_isstdcnt_2169_ = lean_ctor_get_uint32(v_res_2166_, 4);
v_leapcnt_2170_ = lean_ctor_get_uint32(v_res_2166_, 8);
v_timecnt_2171_ = lean_ctor_get_uint32(v_res_2166_, 12);
v_typecnt_2172_ = lean_ctor_get_uint32(v_res_2166_, 16);
v_charcnt_2173_ = lean_ctor_get_uint32(v_res_2166_, 20);
v___x_2174_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64), 1, 0);
lean_inc_ref(v___x_2174_);
v___x_2175_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_2174_, v_timecnt_2171_, v_pos_2167_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_pos_2176_; lean_object* v_res_2177_; lean_object* v___x_2178_; 
v_pos_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_pos_2176_);
v_res_2177_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_res_2177_);
lean_dec_ref_known(v___x_2175_, 2);
v___x_2178_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_2171_, v_pos_2176_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_pos_2179_; lean_object* v_res_2180_; lean_object* v___x_2181_; 
v_pos_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_pos_2179_);
v_res_2180_ = lean_ctor_get(v___x_2178_, 1);
lean_inc(v_res_2180_);
lean_dec_ref_known(v___x_2178_, 2);
v___x_2181_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_2172_, v_pos_2179_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_pos_2182_; lean_object* v_res_2183_; lean_object* v___x_2184_; 
v_pos_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_pos_2182_);
v_res_2183_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_res_2183_);
lean_dec_ref_known(v___x_2181_, 2);
v___x_2184_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_2183_, v_charcnt_2173_, v_pos_2182_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_pos_2185_; lean_object* v_res_2186_; lean_object* v___x_2187_; 
v_pos_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_pos_2185_);
v_res_2186_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_res_2186_);
lean_dec_ref_known(v___x_2184_, 2);
v___x_2187_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_2174_, v_leapcnt_2170_, v_pos_2185_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_pos_2188_; lean_object* v_res_2189_; lean_object* v___x_2190_; 
v_pos_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_pos_2188_);
v_res_2189_ = lean_ctor_get(v___x_2187_, 1);
lean_inc(v_res_2189_);
lean_dec_ref_known(v___x_2187_, 2);
v___x_2190_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_2169_, v_pos_2188_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_pos_2191_; lean_object* v_res_2192_; lean_object* v___x_2193_; 
v_pos_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_pos_2191_);
v_res_2192_ = lean_ctor_get(v___x_2190_, 1);
lean_inc(v_res_2192_);
lean_dec_ref_known(v___x_2190_, 2);
v___x_2193_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_2168_, v_pos_2191_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_pos_2194_; lean_object* v_res_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2216_; 
v_pos_2194_ = lean_ctor_get(v___x_2193_, 0);
v_res_2195_ = lean_ctor_get(v___x_2193_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2197_ = v___x_2193_;
v_isShared_2198_ = v_isSharedCheck_2216_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_res_2195_);
lean_inc(v_pos_2194_);
lean_dec(v___x_2193_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2216_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; 
v___x_2199_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(v_pos_2194_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_pos_2200_; lean_object* v_res_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref(v_a_2146_);
v_pos_2200_ = lean_ctor_get(v___x_2199_, 0);
v_res_2201_ = lean_ctor_get(v___x_2199_, 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2203_ = v___x_2199_;
v_isShared_2204_ = v_isSharedCheck_2213_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_res_2201_);
lean_inc(v_pos_2200_);
lean_dec(v___x_2199_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2213_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2205_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2205_, 0, v_res_2166_);
lean_ctor_set(v___x_2205_, 1, v_res_2177_);
lean_ctor_set(v___x_2205_, 2, v_res_2180_);
lean_ctor_set(v___x_2205_, 3, v_res_2183_);
lean_ctor_set(v___x_2205_, 4, v_res_2186_);
lean_ctor_set(v___x_2205_, 5, v_res_2189_);
lean_ctor_set(v___x_2205_, 6, v_res_2192_);
lean_ctor_set(v___x_2205_, 7, v_res_2195_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 1, v_res_2201_);
lean_ctor_set(v___x_2197_, 0, v___x_2205_);
v___x_2207_ = v___x_2197_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_res_2201_);
v___x_2207_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 1, v___x_2208_);
v___x_2210_ = v___x_2203_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_pos_2200_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_pos_2214_; lean_object* v_err_2215_; 
lean_del_object(v___x_2197_);
lean_dec(v_res_2195_);
lean_dec(v_res_2192_);
lean_dec(v_res_2189_);
lean_dec(v_res_2186_);
lean_dec(v_res_2183_);
lean_dec(v_res_2180_);
lean_dec(v_res_2177_);
lean_dec(v_res_2166_);
v_pos_2214_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_pos_2214_);
v_err_2215_ = lean_ctor_get(v___x_2199_, 1);
lean_inc(v_err_2215_);
lean_dec_ref_known(v___x_2199_, 2);
v_pos_2148_ = v_pos_2214_;
v_err_2149_ = v_err_2215_;
goto v___jp_2147_;
}
}
}
else
{
lean_object* v_pos_2217_; lean_object* v_err_2218_; 
lean_dec(v_res_2192_);
lean_dec(v_res_2189_);
lean_dec(v_res_2186_);
lean_dec(v_res_2183_);
lean_dec(v_res_2180_);
lean_dec(v_res_2177_);
lean_dec(v_res_2166_);
v_pos_2217_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_pos_2217_);
v_err_2218_ = lean_ctor_get(v___x_2193_, 1);
lean_inc(v_err_2218_);
lean_dec_ref_known(v___x_2193_, 2);
v_pos_2148_ = v_pos_2217_;
v_err_2149_ = v_err_2218_;
goto v___jp_2147_;
}
}
else
{
lean_object* v_pos_2219_; lean_object* v_err_2220_; 
lean_dec(v_res_2189_);
lean_dec(v_res_2186_);
lean_dec(v_res_2183_);
lean_dec(v_res_2180_);
lean_dec(v_res_2177_);
lean_dec(v_res_2166_);
v_pos_2219_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_pos_2219_);
v_err_2220_ = lean_ctor_get(v___x_2190_, 1);
lean_inc(v_err_2220_);
lean_dec_ref_known(v___x_2190_, 2);
v_pos_2148_ = v_pos_2219_;
v_err_2149_ = v_err_2220_;
goto v___jp_2147_;
}
}
else
{
lean_object* v_pos_2221_; lean_object* v_err_2222_; 
lean_dec(v_res_2186_);
lean_dec(v_res_2183_);
lean_dec(v_res_2180_);
lean_dec(v_res_2177_);
lean_dec(v_res_2166_);
v_pos_2221_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_pos_2221_);
v_err_2222_ = lean_ctor_get(v___x_2187_, 1);
lean_inc(v_err_2222_);
lean_dec_ref_known(v___x_2187_, 2);
v_pos_2148_ = v_pos_2221_;
v_err_2149_ = v_err_2222_;
goto v___jp_2147_;
}
}
else
{
lean_object* v_pos_2223_; lean_object* v_err_2224_; 
lean_dec(v_res_2183_);
lean_dec(v_res_2180_);
lean_dec(v_res_2177_);
lean_dec_ref(v___x_2174_);
lean_dec(v_res_2166_);
v_pos_2223_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_pos_2223_);
v_err_2224_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_err_2224_);
lean_dec_ref_known(v___x_2184_, 2);
v_pos_2148_ = v_pos_2223_;
v_err_2149_ = v_err_2224_;
goto v___jp_2147_;
}
}
else
{
lean_object* v_pos_2225_; lean_object* v_err_2226_; 
lean_dec(v_res_2180_);
lean_dec(v_res_2177_);
lean_dec_ref(v___x_2174_);
lean_dec(v_res_2166_);
v_pos_2225_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_pos_2225_);
v_err_2226_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_err_2226_);
lean_dec_ref_known(v___x_2181_, 2);
v_pos_2148_ = v_pos_2225_;
v_err_2149_ = v_err_2226_;
goto v___jp_2147_;
}
}
else
{
lean_object* v_pos_2227_; lean_object* v_err_2228_; 
lean_dec(v_res_2177_);
lean_dec_ref(v___x_2174_);
lean_dec(v_res_2166_);
v_pos_2227_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_pos_2227_);
v_err_2228_ = lean_ctor_get(v___x_2178_, 1);
lean_inc(v_err_2228_);
lean_dec_ref_known(v___x_2178_, 2);
v_pos_2148_ = v_pos_2227_;
v_err_2149_ = v_err_2228_;
goto v___jp_2147_;
}
}
else
{
lean_object* v_pos_2229_; lean_object* v_err_2230_; 
lean_dec_ref(v___x_2174_);
lean_dec(v_res_2166_);
v_pos_2229_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_pos_2229_);
v_err_2230_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_err_2230_);
lean_dec_ref_known(v___x_2175_, 2);
v_pos_2148_ = v_pos_2229_;
v_err_2149_ = v_err_2230_;
goto v___jp_2147_;
}
}
else
{
lean_object* v_pos_2231_; lean_object* v_err_2232_; 
v_pos_2231_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_pos_2231_);
v_err_2232_ = lean_ctor_get(v___x_2165_, 1);
lean_inc(v_err_2232_);
lean_dec_ref_known(v___x_2165_, 2);
v_pos_2148_ = v_pos_2231_;
v_err_2149_ = v_err_2232_;
goto v___jp_2147_;
}
v___jp_2147_:
{
lean_object* v_idx_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2163_; 
v_idx_2150_ = lean_ctor_get(v_a_2146_, 1);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_a_2146_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v_a_2146_, 0);
lean_dec(v_unused_2164_);
v___x_2152_ = v_a_2146_;
v_isShared_2153_ = v_isSharedCheck_2163_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_idx_2150_);
lean_dec(v_a_2146_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2163_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_idx_2154_; uint8_t v___x_2155_; 
v_idx_2154_ = lean_ctor_get(v_pos_2148_, 1);
v___x_2155_ = lean_nat_dec_eq(v_idx_2150_, v_idx_2154_);
lean_dec(v_idx_2150_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2157_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set_tag(v___x_2152_, 1);
lean_ctor_set(v___x_2152_, 1, v_err_2149_);
lean_ctor_set(v___x_2152_, 0, v_pos_2148_);
v___x_2157_ = v___x_2152_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_pos_2148_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_err_2149_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_err_2149_);
v___x_2159_ = lean_box(0);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v___x_2159_);
lean_ctor_set(v___x_2152_, 0, v_pos_2148_);
v___x_2161_ = v___x_2152_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_pos_2148_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_parse(lean_object* v_a_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(v_a_2233_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_pos_2235_; lean_object* v_res_2236_; lean_object* v___x_2237_; 
v_pos_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_pos_2235_);
v_res_2236_ = lean_ctor_get(v___x_2234_, 1);
lean_inc(v_res_2236_);
lean_dec_ref_known(v___x_2234_, 2);
v___x_2237_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(v_pos_2235_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_pos_2238_; lean_object* v_res_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2247_; 
v_pos_2238_ = lean_ctor_get(v___x_2237_, 0);
v_res_2239_ = lean_ctor_get(v___x_2237_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2241_ = v___x_2237_;
v_isShared_2242_ = v_isSharedCheck_2247_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_res_2239_);
lean_inc(v_pos_2238_);
lean_dec(v___x_2237_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2247_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v_res_2236_);
lean_ctor_set(v___x_2243_, 1, v_res_2239_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 1, v___x_2243_);
v___x_2245_ = v___x_2241_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_pos_2238_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
else
{
lean_object* v_pos_2248_; lean_object* v_err_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_res_2236_);
v_pos_2248_ = lean_ctor_get(v___x_2237_, 0);
v_err_2249_ = lean_ctor_get(v___x_2237_, 1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2237_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_err_2249_);
lean_inc(v_pos_2248_);
lean_dec(v___x_2237_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_pos_2248_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_err_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_object* v_pos_2257_; lean_object* v_err_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
v_pos_2257_ = lean_ctor_get(v___x_2234_, 0);
v_err_2258_ = lean_ctor_get(v___x_2234_, 1);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2234_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_err_2258_);
lean_inc(v_pos_2257_);
lean_dec(v___x_2234_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_pos_2257_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_err_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_TzIf(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default = _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default);
l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType = _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType);
l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default = _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default);
l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond = _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond);
l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1 = _init_l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1();
lean_mark_persistent(l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_Database_TzIf(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Repr(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_TzIf(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_TzIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_Database_TzIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_Database_TzIf(builtin);
}
#ifdef __cplusplus
}
#endif
