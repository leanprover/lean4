// Lean compiler output
// Module: Std.Time.Zoned.Database.TzIf
// Imports: public import Init.Data.Range.Polymorphic.Iterators public import Std.Internal.Parsec import Init.Data.Int.Repr
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
lean_object* v___y_439_; uint8_t v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___y_459_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
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
lean_inc(v___y_439_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 4);
lean_ctor_set(v___x_436_, 1, v___y_442_);
lean_ctor_set(v___x_436_, 0, v___y_439_);
v___x_444_ = v___x_436_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___y_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___y_442_);
v___x_444_ = v_reuseFailAlloc_454_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_445_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1, v___y_440_);
v___x_446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_446_, 0, v___y_441_);
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
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*1, v___y_440_);
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
v___y_439_ = v___x_471_;
v___y_440_ = v___x_461_;
v___y_441_ = v___x_470_;
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
v___y_439_ = v___x_471_;
v___y_440_ = v___x_461_;
v___y_441_ = v___x_470_;
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(uint8_t v___y_670_){
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0___boxed(lean_object* v___y_674_){
_start:
{
uint8_t v___y_1967__boxed_675_; lean_object* v_res_676_; 
v___y_1967__boxed_675_ = lean_unbox(v___y_674_);
v_res_676_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___y_1967__boxed_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_677_) == 0)
{
lean_object* v___x_679_; 
lean_dec(v_x_678_);
v___x_679_ = lean_box(0);
return v___x_679_;
}
else
{
lean_object* v_tail_680_; 
v_tail_680_ = lean_ctor_get(v_x_677_, 1);
if (lean_obj_tag(v_tail_680_) == 0)
{
lean_object* v_head_681_; uint8_t v___x_682_; lean_object* v___x_683_; 
lean_dec(v_x_678_);
v_head_681_ = lean_ctor_get(v_x_677_, 0);
lean_inc(v_head_681_);
lean_dec_ref_known(v_x_677_, 2);
v___x_682_ = lean_unbox(v_head_681_);
lean_dec(v_head_681_);
v___x_683_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_682_);
return v___x_683_;
}
else
{
lean_object* v_head_684_; uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc(v_tail_680_);
v_head_684_ = lean_ctor_get(v_x_677_, 0);
lean_inc(v_head_684_);
lean_dec_ref_known(v_x_677_, 2);
v___x_685_ = lean_unbox(v_head_684_);
lean_dec(v_head_684_);
v___x_686_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_685_);
v___x_687_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(v_x_678_, v___x_686_, v_tail_680_);
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(lean_object* v_xs_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_689_ = lean_array_get_size(v_xs_688_);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_nat_dec_eq(v___x_689_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_692_ = lean_array_to_list(v_xs_688_);
v___x_693_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_694_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(v___x_692_, v___x_693_);
v___x_695_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_696_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_694_);
v___x_698_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_695_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l_Std_Format_fill(v___x_700_);
return v___x_701_;
}
else
{
lean_object* v___x_702_; 
lean_dec_ref(v_xs_688_);
v___x_702_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_x_705_) == 0)
{
lean_dec(v_x_703_);
return v_x_704_;
}
else
{
lean_object* v_head_706_; lean_object* v_tail_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_726_; 
v_head_706_ = lean_ctor_get(v_x_705_, 0);
v_tail_707_ = lean_ctor_get(v_x_705_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_705_);
if (v_isSharedCheck_726_ == 0)
{
v___x_709_ = v_x_705_;
v_isShared_710_ = v_isSharedCheck_726_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_tail_707_);
lean_inc(v_head_706_);
lean_dec(v_x_705_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_726_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
lean_inc(v_x_703_);
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 5);
lean_ctor_set(v___x_709_, 1, v_x_703_);
lean_ctor_set(v___x_709_, 0, v_x_704_);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_x_704_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_x_703_);
v___x_712_ = v_reuseFailAlloc_725_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_715_ = lean_int_dec_lt(v_head_706_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = l_Int_repr(v_head_706_);
lean_dec(v_head_706_);
v___x_717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_712_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v_x_704_ = v___x_718_;
v_x_705_ = v_tail_707_;
goto _start;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_720_ = l_Int_repr(v_head_706_);
lean_dec(v_head_706_);
v___x_721_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
v___x_722_ = l_Repr_addAppParen(v___x_721_, v___x_713_);
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_712_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v_x_704_ = v___x_723_;
v_x_705_ = v_tail_707_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
if (lean_obj_tag(v_x_729_) == 0)
{
lean_dec(v_x_727_);
return v_x_728_;
}
else
{
lean_object* v_head_730_; lean_object* v_tail_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_750_; 
v_head_730_ = lean_ctor_get(v_x_729_, 0);
v_tail_731_ = lean_ctor_get(v_x_729_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v_x_729_);
if (v_isSharedCheck_750_ == 0)
{
v___x_733_ = v_x_729_;
v_isShared_734_ = v_isSharedCheck_750_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_tail_731_);
lean_inc(v_head_730_);
lean_dec(v_x_729_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_750_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
lean_inc(v_x_727_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 5);
lean_ctor_set(v___x_733_, 1, v_x_727_);
lean_ctor_set(v___x_733_, 0, v_x_728_);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_x_728_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_x_727_);
v___x_736_ = v_reuseFailAlloc_749_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_739_ = lean_int_dec_lt(v_head_730_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_740_ = l_Int_repr(v_head_730_);
lean_dec(v_head_730_);
v___x_741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
v___x_742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_736_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_727_, v___x_742_, v_tail_731_);
return v___x_743_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_744_ = l_Int_repr(v_head_730_);
lean_dec(v_head_730_);
v___x_745_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
v___x_746_ = l_Repr_addAppParen(v___x_745_, v___x_737_);
v___x_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_736_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_727_, v___x_747_, v_tail_731_);
return v___x_748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(lean_object* v___y_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_754_ = lean_int_dec_lt(v___y_751_, v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = l_Int_repr(v___y_751_);
v___x_756_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = l_Int_repr(v___y_751_);
v___x_758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
v___x_759_ = l_Repr_addAppParen(v___x_758_, v___x_752_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0___boxed(lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v___y_760_);
lean_dec(v___y_760_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
if (lean_obj_tag(v_x_762_) == 0)
{
lean_object* v___x_764_; 
lean_dec(v_x_763_);
v___x_764_ = lean_box(0);
return v___x_764_;
}
else
{
lean_object* v_tail_765_; 
v_tail_765_ = lean_ctor_get(v_x_762_, 1);
if (lean_obj_tag(v_tail_765_) == 0)
{
lean_object* v_head_766_; lean_object* v___x_767_; 
lean_dec(v_x_763_);
v_head_766_ = lean_ctor_get(v_x_762_, 0);
lean_inc(v_head_766_);
lean_dec_ref_known(v_x_762_, 2);
v___x_767_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_766_);
lean_dec(v_head_766_);
return v___x_767_;
}
else
{
lean_object* v_head_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_inc(v_tail_765_);
v_head_768_ = lean_ctor_get(v_x_762_, 0);
lean_inc(v_head_768_);
lean_dec_ref_known(v_x_762_, 2);
v___x_769_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_768_);
lean_dec(v_head_768_);
v___x_770_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(v_x_763_, v___x_769_, v_tail_765_);
return v___x_770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(lean_object* v_xs_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = lean_array_get_size(v_xs_771_);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_nat_dec_eq(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_775_ = lean_array_to_list(v_xs_771_);
v___x_776_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_777_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(v___x_775_, v___x_776_);
v___x_778_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_779_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v___x_777_);
v___x_781_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_778_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l_Std_Format_fill(v___x_783_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; 
lean_dec_ref(v_xs_771_);
v___x_785_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
if (lean_obj_tag(v_x_788_) == 0)
{
lean_dec(v_x_786_);
return v_x_787_;
}
else
{
lean_object* v_head_789_; lean_object* v_tail_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_800_; 
v_head_789_ = lean_ctor_get(v_x_788_, 0);
v_tail_790_ = lean_ctor_get(v_x_788_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_x_788_);
if (v_isSharedCheck_800_ == 0)
{
v___x_792_ = v_x_788_;
v_isShared_793_ = v_isSharedCheck_800_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_tail_790_);
lean_inc(v_head_789_);
lean_dec(v_x_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_800_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
lean_inc(v_x_786_);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 5);
lean_ctor_set(v___x_792_, 1, v_x_786_);
lean_ctor_set(v___x_792_, 0, v_x_787_);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_x_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_x_786_);
v___x_795_ = v_reuseFailAlloc_799_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_789_);
lean_dec(v_head_789_);
v___x_797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v_x_787_ = v___x_797_;
v_x_788_ = v_tail_790_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
lean_dec(v_x_801_);
return v_x_802_;
}
else
{
lean_object* v_head_804_; lean_object* v_tail_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_815_; 
v_head_804_ = lean_ctor_get(v_x_803_, 0);
v_tail_805_ = lean_ctor_get(v_x_803_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_803_);
if (v_isSharedCheck_815_ == 0)
{
v___x_807_ = v_x_803_;
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_tail_805_);
lean_inc(v_head_804_);
lean_dec(v_x_803_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
lean_inc(v_x_801_);
if (v_isShared_808_ == 0)
{
lean_ctor_set_tag(v___x_807_, 5);
lean_ctor_set(v___x_807_, 1, v_x_801_);
lean_ctor_set(v___x_807_, 0, v_x_802_);
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_x_802_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_x_801_);
v___x_810_ = v_reuseFailAlloc_814_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_804_);
lean_dec(v_head_804_);
v___x_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(v_x_801_, v___x_812_, v_tail_805_);
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
if (lean_obj_tag(v_x_816_) == 0)
{
lean_object* v___x_818_; 
lean_dec(v_x_817_);
v___x_818_ = lean_box(0);
return v___x_818_;
}
else
{
lean_object* v_tail_819_; 
v_tail_819_ = lean_ctor_get(v_x_816_, 1);
if (lean_obj_tag(v_tail_819_) == 0)
{
lean_object* v_head_820_; lean_object* v___x_821_; 
lean_dec(v_x_817_);
v_head_820_ = lean_ctor_get(v_x_816_, 0);
lean_inc(v_head_820_);
lean_dec_ref_known(v_x_816_, 2);
v___x_821_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_820_);
lean_dec(v_head_820_);
return v___x_821_;
}
else
{
lean_object* v_head_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_inc(v_tail_819_);
v_head_822_ = lean_ctor_get(v_x_816_, 0);
lean_inc(v_head_822_);
lean_dec_ref_known(v_x_816_, 2);
v___x_823_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_822_);
lean_dec(v_head_822_);
v___x_824_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(v_x_817_, v___x_823_, v_tail_819_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(lean_object* v_xs_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_826_ = lean_array_get_size(v_xs_825_);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_nat_dec_eq(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_829_ = lean_array_to_list(v_xs_825_);
v___x_830_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_831_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(v___x_829_, v___x_830_);
v___x_832_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_833_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_831_);
v___x_835_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_832_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Std_Format_fill(v___x_837_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; 
lean_dec_ref(v_xs_825_);
v___x_839_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_dec(v_x_840_);
return v_x_841_;
}
else
{
lean_object* v_head_843_; lean_object* v_tail_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_854_; 
v_head_843_ = lean_ctor_get(v_x_842_, 0);
v_tail_844_ = lean_ctor_get(v_x_842_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_854_ == 0)
{
v___x_846_ = v_x_842_;
v_isShared_847_ = v_isSharedCheck_854_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_tail_844_);
lean_inc(v_head_843_);
lean_dec(v_x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_854_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
lean_inc(v_x_840_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 5);
lean_ctor_set(v___x_846_, 1, v_x_840_);
lean_ctor_set(v___x_846_, 0, v_x_841_);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_x_841_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_x_840_);
v___x_849_ = v_reuseFailAlloc_853_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_843_);
v___x_851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v_x_841_ = v___x_851_;
v_x_842_ = v_tail_844_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
if (lean_obj_tag(v_x_857_) == 0)
{
lean_dec(v_x_855_);
return v_x_856_;
}
else
{
lean_object* v_head_858_; lean_object* v_tail_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_869_; 
v_head_858_ = lean_ctor_get(v_x_857_, 0);
v_tail_859_ = lean_ctor_get(v_x_857_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v_x_857_);
if (v_isSharedCheck_869_ == 0)
{
v___x_861_ = v_x_857_;
v_isShared_862_ = v_isSharedCheck_869_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_tail_859_);
lean_inc(v_head_858_);
lean_dec(v_x_857_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_869_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
lean_inc(v_x_855_);
if (v_isShared_862_ == 0)
{
lean_ctor_set_tag(v___x_861_, 5);
lean_ctor_set(v___x_861_, 1, v_x_855_);
lean_ctor_set(v___x_861_, 0, v_x_856_);
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_x_856_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_x_855_);
v___x_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_865_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_858_);
v___x_866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(v_x_855_, v___x_866_, v_tail_859_);
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_870_) == 0)
{
lean_object* v___x_872_; 
lean_dec(v_x_871_);
v___x_872_ = lean_box(0);
return v___x_872_;
}
else
{
lean_object* v_tail_873_; 
v_tail_873_ = lean_ctor_get(v_x_870_, 1);
if (lean_obj_tag(v_tail_873_) == 0)
{
lean_object* v_head_874_; lean_object* v___x_875_; 
lean_dec(v_x_871_);
v_head_874_ = lean_ctor_get(v_x_870_, 0);
lean_inc(v_head_874_);
lean_dec_ref_known(v_x_870_, 2);
v___x_875_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_874_);
return v___x_875_;
}
else
{
lean_object* v_head_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_inc(v_tail_873_);
v_head_876_ = lean_ctor_get(v_x_870_, 0);
lean_inc(v_head_876_);
lean_dec_ref_known(v_x_870_, 2);
v___x_877_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_876_);
v___x_878_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(v_x_871_, v___x_877_, v_tail_873_);
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(lean_object* v_xs_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_880_ = lean_array_get_size(v_xs_879_);
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_nat_dec_eq(v___x_880_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_883_ = lean_array_to_list(v_xs_879_);
v___x_884_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_885_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(v___x_883_, v___x_884_);
v___x_886_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_887_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_885_);
v___x_889_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_886_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Std_Format_fill(v___x_891_);
return v___x_892_;
}
else
{
lean_object* v___x_893_; 
lean_dec_ref(v_xs_879_);
v___x_893_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_893_;
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(10u);
v___x_904_ = lean_nat_to_int(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(19u);
v___x_909_ = lean_nat_to_int(v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_unsigned_to_nat(17u);
v___x_920_ = lean_nat_to_int(v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_unsigned_to_nat(15u);
v___x_925_ = lean_nat_to_int(v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(lean_object* v_x_932_){
_start:
{
lean_object* v_header_933_; lean_object* v_transitionTimes_934_; lean_object* v_transitionIndices_935_; lean_object* v_localTimeTypes_936_; lean_object* v_abbreviations_937_; lean_object* v_leapSeconds_938_; lean_object* v_stdWallIndicators_939_; lean_object* v_utLocalIndicators_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_header_933_ = lean_ctor_get(v_x_932_, 0);
lean_inc_ref(v_header_933_);
v_transitionTimes_934_ = lean_ctor_get(v_x_932_, 1);
lean_inc_ref(v_transitionTimes_934_);
v_transitionIndices_935_ = lean_ctor_get(v_x_932_, 2);
lean_inc_ref(v_transitionIndices_935_);
v_localTimeTypes_936_ = lean_ctor_get(v_x_932_, 3);
lean_inc_ref(v_localTimeTypes_936_);
v_abbreviations_937_ = lean_ctor_get(v_x_932_, 4);
lean_inc_ref(v_abbreviations_937_);
v_leapSeconds_938_ = lean_ctor_get(v_x_932_, 5);
lean_inc_ref(v_leapSeconds_938_);
v_stdWallIndicators_939_ = lean_ctor_get(v_x_932_, 6);
lean_inc_ref(v_stdWallIndicators_939_);
v_utLocalIndicators_940_ = lean_ctor_get(v_x_932_, 7);
lean_inc_ref(v_utLocalIndicators_940_);
lean_dec_ref(v_x_932_);
v___x_941_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_942_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3));
v___x_943_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4);
v___x_944_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_header_933_);
lean_dec_ref(v_header_933_);
v___x_945_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = 0;
v___x_947_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*1, v___x_946_);
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_942_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_box(1);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6));
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_941_);
v___x_956_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7);
v___x_957_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(v_transitionTimes_934_);
v___x_958_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set_uint8(v___x_959_, sizeof(void*)*1, v___x_946_);
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_955_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_949_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v___x_951_);
v___x_963_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9));
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_941_);
v___x_966_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10);
v___x_967_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(v_transitionIndices_935_);
v___x_968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set_uint8(v___x_969_, sizeof(void*)*1, v___x_946_);
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_965_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___x_949_);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_951_);
v___x_973_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11));
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_941_);
v___x_976_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4);
v___x_977_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(v_localTimeTypes_936_);
v___x_978_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*1, v___x_946_);
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_975_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_949_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_951_);
v___x_983_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13));
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_941_);
v___x_986_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14);
v___x_987_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(v_abbreviations_937_);
v___x_988_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*1, v___x_946_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_985_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_949_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_951_);
v___x_993_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16));
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_941_);
v___x_996_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17);
v___x_997_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(v_leapSeconds_938_);
v___x_998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*1, v___x_946_);
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_995_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_949_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_951_);
v___x_1003_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19));
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_941_);
v___x_1006_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(v_stdWallIndicators_939_);
v___x_1007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_966_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*1, v___x_946_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1005_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_949_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_951_);
v___x_1012_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21));
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_941_);
v___x_1015_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(v_utLocalIndicators_940_);
v___x_1016_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_966_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*1, v___x_946_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1014_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1020_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_1018_);
v___x_1022_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1019_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set_uint8(v___x_1025_, sizeof(void*)*1, v___x_946_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(lean_object* v_x_1026_, lean_object* v_prec_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_x_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___boxed(lean_object* v_x_1029_, lean_object* v_prec_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(v_x_1029_, v_prec_1030_);
lean_dec(v_prec_1030_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1));
return v___x_1049_;
}
else
{
lean_object* v_val_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1061_; 
v_val_1050_ = lean_ctor_get(v_x_1047_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1052_ = v_x_1047_;
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_val_1050_);
lean_dec(v_x_1047_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1054_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3));
v___x_1055_ = l_String_quote(v_val_1050_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 3);
lean_ctor_set(v___x_1052_, 0, v___x_1055_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1054_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = l_Repr_addAppParen(v___x_1058_, v_x_1048_);
return v___x_1059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___boxed(lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(v_x_1062_, v_x_1063_);
lean_dec(v_x_1063_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(lean_object* v_x_1077_){
_start:
{
lean_object* v_toTZifV1_1078_; lean_object* v_footer_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1113_; 
v_toTZifV1_1078_ = lean_ctor_get(v_x_1077_, 0);
v_footer_1079_ = lean_ctor_get(v_x_1077_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_x_1077_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1081_ = v_x_1077_;
v_isShared_1082_ = v_isSharedCheck_1113_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_footer_1079_);
lean_inc(v_toTZifV1_1078_);
lean_dec(v_x_1077_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1113_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1083_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_1084_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3));
v___x_1085_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_toTZifV1_1078_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 4);
lean_ctor_set(v___x_1081_, 1, v___x_1087_);
lean_ctor_set(v___x_1081_, 0, v___x_1085_);
v___x_1089_ = v___x_1081_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1090_ = 0;
v___x_1091_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set_uint8(v___x_1091_, sizeof(void*)*1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1084_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_1094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_box(1);
v___x_1096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5));
v___x_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___x_1083_);
v___x_1100_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4);
v___x_1101_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(v_footer_1079_, v___x_1086_);
v___x_1102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*1, v___x_1090_);
v___x_1104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1099_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1106_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1104_);
v___x_1108_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1105_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*1, v___x_1090_);
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(lean_object* v_x_1114_, lean_object* v_prec_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_x_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___boxed(lean_object* v_x_1117_, lean_object* v_prec_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(v_x_1117_, v_prec_1118_);
lean_dec(v_prec_1118_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
if (lean_obj_tag(v_x_1127_) == 0)
{
lean_object* v___x_1129_; 
v___x_1129_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1));
return v___x_1129_;
}
else
{
lean_object* v_val_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_val_1130_ = lean_ctor_get(v_x_1127_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v_x_1127_, 1);
v___x_1131_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3));
v___x_1132_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_val_1130_);
v___x_1133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = l_Repr_addAppParen(v___x_1133_, v_x_1128_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0___boxed(lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(v_x_1135_, v_x_1136_);
lean_dec(v_x_1136_);
return v_res_1137_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_unsigned_to_nat(6u);
v___x_1148_ = lean_nat_to_int(v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(lean_object* v_x_1152_){
_start:
{
lean_object* v_v1_1153_; lean_object* v_v2_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1187_; 
v_v1_1153_ = lean_ctor_get(v_x_1152_, 0);
v_v2_1154_ = lean_ctor_get(v_x_1152_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_x_1152_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1156_ = v_x_1152_;
v_isShared_1157_ = v_isSharedCheck_1187_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_v2_1154_);
lean_inc(v_v1_1153_);
lean_dec(v_x_1152_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1187_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1158_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_1159_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3));
v___x_1160_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_v1_1153_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 4);
lean_ctor_set(v___x_1156_, 1, v___x_1162_);
lean_ctor_set(v___x_1156_, 0, v___x_1160_);
v___x_1164_ = v___x_1156_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
uint8_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1165_ = 0;
v___x_1166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*1, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1159_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_1169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_box(1);
v___x_1171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6));
v___x_1173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v___x_1158_);
v___x_1175_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(v_v2_1154_, v___x_1161_);
v___x_1176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1160_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set_uint8(v___x_1177_, sizeof(void*)*1, v___x_1165_);
v___x_1178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1174_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1180_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v___x_1178_);
v___x_1182_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1179_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*1, v___x_1165_);
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr(lean_object* v_x_1188_, lean_object* v_prec_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(v_x_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___boxed(lean_object* v_x_1191_, lean_object* v_prec_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr(v_x_1191_, v_prec_1192_);
lean_dec(v_prec_1192_);
return v_res_1193_;
}
}
static lean_object* _init_l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = 0;
v___x_1202_ = lean_box_uint32(v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(lean_object* v_msg_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; uint32_t v___x_1206_; 
v___x_1204_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1;
v___x_1205_ = lean_panic_fn_borrowed(v___x_1204_, v_msg_1203_);
v___x_1206_ = lean_unbox_uint32(v___x_1205_);
lean_dec(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed(lean_object* v_msg_1207_){
_start:
{
uint32_t v_res_1208_; lean_object* v_r_1209_; 
v_res_1208_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v_msg_1207_);
v_r_1209_ = lean_box_uint32(v_res_1208_);
return v_r_1209_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1213_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2));
v___x_1214_ = lean_unsigned_to_nat(2u);
v___x_1215_ = lean_unsigned_to_nat(182u);
v___x_1216_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1));
v___x_1217_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0));
v___x_1218_ = l_mkPanicMessageWithDecl(v___x_1217_, v___x_1216_, v___x_1215_, v___x_1214_, v___x_1213_);
return v___x_1218_;
}
}
LEAN_EXPORT uint32_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(lean_object* v_bs_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1220_ = lean_byte_array_size(v_bs_1219_);
v___x_1221_ = lean_unsigned_to_nat(4u);
v___x_1222_ = lean_nat_dec_eq(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; uint32_t v___x_1224_; 
v___x_1223_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3);
v___x_1224_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v___x_1223_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; uint8_t v___x_1226_; uint32_t v___x_1227_; uint32_t v___x_1228_; uint32_t v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; uint32_t v___x_1232_; uint32_t v___x_1233_; uint32_t v___x_1234_; uint32_t v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; uint32_t v___x_1238_; uint32_t v___x_1239_; uint32_t v___x_1240_; uint32_t v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; uint32_t v___x_1244_; uint32_t v___x_1245_; 
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = lean_byte_array_get(v_bs_1219_, v___x_1225_);
v___x_1227_ = lean_uint8_to_uint32(v___x_1226_);
v___x_1228_ = 24;
v___x_1229_ = lean_uint32_shift_left(v___x_1227_, v___x_1228_);
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_byte_array_get(v_bs_1219_, v___x_1230_);
v___x_1232_ = lean_uint8_to_uint32(v___x_1231_);
v___x_1233_ = 16;
v___x_1234_ = lean_uint32_shift_left(v___x_1232_, v___x_1233_);
v___x_1235_ = lean_uint32_lor(v___x_1229_, v___x_1234_);
v___x_1236_ = lean_unsigned_to_nat(2u);
v___x_1237_ = lean_byte_array_get(v_bs_1219_, v___x_1236_);
v___x_1238_ = lean_uint8_to_uint32(v___x_1237_);
v___x_1239_ = 8;
v___x_1240_ = lean_uint32_shift_left(v___x_1238_, v___x_1239_);
v___x_1241_ = lean_uint32_lor(v___x_1235_, v___x_1240_);
v___x_1242_ = lean_unsigned_to_nat(3u);
v___x_1243_ = lean_byte_array_get(v_bs_1219_, v___x_1242_);
v___x_1244_ = lean_uint8_to_uint32(v___x_1243_);
v___x_1245_ = lean_uint32_lor(v___x_1241_, v___x_1244_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___boxed(lean_object* v_bs_1246_){
_start:
{
uint32_t v_res_1247_; lean_object* v_r_1248_; 
v_res_1247_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_1246_);
lean_dec_ref(v_bs_1246_);
v_r_1248_ = lean_box_uint32(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(lean_object* v_bs_1249_){
_start:
{
uint32_t v___x_1250_; lean_object* v_n_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1250_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_1249_);
v_n_1251_ = lean_uint32_to_nat(v___x_1250_);
v___x_1252_ = lean_unsigned_to_nat(2147483648u);
v___x_1253_ = lean_nat_dec_lt(v_n_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_cstr_to_nat("4294967296");
v___x_1255_ = lean_nat_sub(v___x_1254_, v_n_1251_);
lean_dec(v_n_1251_);
v___x_1256_ = l_Int_negOfNat(v___x_1255_);
lean_dec(v___x_1255_);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_nat_to_int(v_n_1251_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___boxed(lean_object* v_bs_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(v_bs_1258_);
lean_dec_ref(v_bs_1258_);
return v_res_1259_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0(void){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_cstr_to_nat("9223372036854775808");
return v___x_1260_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1(void){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(lean_object* v_bs_1262_){
_start:
{
uint64_t v___x_1263_; lean_object* v_n_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1263_ = l_ByteArray_toUInt64BE_x21(v_bs_1262_);
v_n_1264_ = lean_uint64_to_nat(v___x_1263_);
v___x_1265_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0);
v___x_1266_ = lean_nat_dec_lt(v_n_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1);
v___x_1268_ = lean_nat_sub(v___x_1267_, v_n_1264_);
lean_dec(v_n_1264_);
v___x_1269_ = l_Int_negOfNat(v___x_1268_);
lean_dec(v___x_1268_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_nat_to_int(v_n_1264_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___boxed(lean_object* v_bs_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(v_bs_1271_);
lean_dec_ref(v_bs_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(lean_object* v_upperBound_1273_, lean_object* v_p_1274_, lean_object* v_a_1275_, lean_object* v_b_1276_, lean_object* v___y_1277_){
_start:
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_nat_dec_lt(v_a_1275_, v_upperBound_1273_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_dec(v_a_1275_);
lean_dec_ref(v_p_1274_);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___y_1277_);
lean_ctor_set(v___x_1279_, 1, v_b_1276_);
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; 
lean_inc_ref(v_p_1274_);
v___x_1280_ = lean_apply_1(v_p_1274_, v___y_1277_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_pos_1281_; lean_object* v_res_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_pos_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_pos_1281_);
v_res_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_res_1282_);
lean_dec_ref_known(v___x_1280_, 2);
v___x_1283_ = lean_array_push(v_b_1276_, v_res_1282_);
v___x_1284_ = lean_unsigned_to_nat(1u);
v___x_1285_ = lean_nat_add(v_a_1275_, v___x_1284_);
lean_dec(v_a_1275_);
v_a_1275_ = v___x_1285_;
v_b_1276_ = v___x_1283_;
v___y_1277_ = v_pos_1281_;
goto _start;
}
else
{
lean_object* v_pos_1287_; lean_object* v_err_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_b_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_p_1274_);
v_pos_1287_ = lean_ctor_get(v___x_1280_, 0);
v_err_1288_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1280_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_err_1288_);
lean_inc(v_pos_1287_);
lean_dec(v___x_1280_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_pos_1287_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_err_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg___boxed(lean_object* v_upperBound_1296_, lean_object* v_p_1297_, lean_object* v_a_1298_, lean_object* v_b_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_1296_, v_p_1297_, v_a_1298_, v_b_1299_, v___y_1300_);
lean_dec(v_upperBound_1296_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(lean_object* v_n_1304_, lean_object* v_p_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1307_; lean_object* v_result_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_unsigned_to_nat(0u);
v_result_1308_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0));
v___x_1309_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_n_1304_, v_p_1305_, v___x_1307_, v_result_1308_, v_a_1306_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___boxed(lean_object* v_n_1310_, lean_object* v_p_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v_n_1310_, v_p_1311_, v_a_1312_);
lean_dec(v_n_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(lean_object* v_00_u03b1_1314_, lean_object* v_n_1315_, lean_object* v_p_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v_n_1315_, v_p_1316_, v_a_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___boxed(lean_object* v_00_u03b1_1319_, lean_object* v_n_1320_, lean_object* v_p_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(v_00_u03b1_1319_, v_n_1320_, v_p_1321_, v_a_1322_);
lean_dec(v_n_1320_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(lean_object* v_00_u03b1_1324_, lean_object* v_upperBound_1325_, lean_object* v_p_1326_, lean_object* v_inst_1327_, lean_object* v_R_1328_, lean_object* v_a_1329_, lean_object* v_b_1330_, lean_object* v_c_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_1325_, v_p_1326_, v_a_1329_, v_b_1330_, v___y_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_upperBound_1335_, lean_object* v_p_1336_, lean_object* v_inst_1337_, lean_object* v_R_1338_, lean_object* v_a_1339_, lean_object* v_b_1340_, lean_object* v_c_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(v_00_u03b1_1334_, v_upperBound_1335_, v_p_1336_, v_inst_1337_, v_R_1338_, v_a_1339_, v_b_1340_, v_c_1341_, v___y_1342_);
lean_dec(v_upperBound_1335_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu64(lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_unsigned_to_nat(8u);
v___x_1346_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1345_, v_a_1344_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_pos_1347_; lean_object* v_res_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1358_; 
v_pos_1347_ = lean_ctor_get(v___x_1346_, 0);
v_res_1348_ = lean_ctor_get(v___x_1346_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1350_ = v___x_1346_;
v_isShared_1351_ = v_isSharedCheck_1358_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_res_1348_);
lean_inc(v_pos_1347_);
lean_dec(v___x_1346_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1358_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; uint64_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1352_ = l_ByteSlice_toByteArray(v_res_1348_);
v___x_1353_ = l_ByteArray_toUInt64LE_x21(v___x_1352_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = lean_box_uint64(v___x_1353_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1354_);
v___x_1356_ = v___x_1350_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_pos_1347_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
else
{
lean_object* v_pos_1359_; lean_object* v_err_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_pos_1359_ = lean_ctor_get(v___x_1346_, 0);
v_err_1360_ = lean_ctor_get(v___x_1346_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1346_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_err_1360_);
lean_inc(v_pos_1359_);
lean_dec(v___x_1346_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_pos_1359_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_err_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64(lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_unsigned_to_nat(8u);
v___x_1370_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1369_, v_a_1368_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_pos_1371_; lean_object* v_res_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1381_; 
v_pos_1371_ = lean_ctor_get(v___x_1370_, 0);
v_res_1372_ = lean_ctor_get(v___x_1370_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1374_ = v___x_1370_;
v_isShared_1375_ = v_isSharedCheck_1381_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_res_1372_);
lean_inc(v_pos_1371_);
lean_dec(v___x_1370_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1381_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1376_ = l_ByteSlice_toByteArray(v_res_1372_);
v___x_1377_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(v___x_1376_);
lean_dec_ref(v___x_1376_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v___x_1377_);
v___x_1379_ = v___x_1374_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_pos_1371_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_object* v_pos_1382_; lean_object* v_err_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_pos_1382_ = lean_ctor_get(v___x_1370_, 0);
v_err_1383_ = lean_ctor_get(v___x_1370_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1370_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_err_1383_);
lean_inc(v_pos_1382_);
lean_dec(v___x_1370_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_pos_1382_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_err_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(lean_object* v_a_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_unsigned_to_nat(4u);
v___x_1393_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1392_, v_a_1391_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_pos_1394_; lean_object* v_res_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1405_; 
v_pos_1394_ = lean_ctor_get(v___x_1393_, 0);
v_res_1395_ = lean_ctor_get(v___x_1393_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1397_ = v___x_1393_;
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_res_1395_);
lean_inc(v_pos_1394_);
lean_dec(v___x_1393_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; uint32_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1399_ = l_ByteSlice_toByteArray(v_res_1395_);
v___x_1400_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v___x_1399_);
lean_dec_ref(v___x_1399_);
v___x_1401_ = lean_box_uint32(v___x_1400_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1401_);
v___x_1403_ = v___x_1397_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_pos_1394_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
else
{
lean_object* v_pos_1406_; lean_object* v_err_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v_pos_1406_ = lean_ctor_get(v___x_1393_, 0);
v_err_1407_ = lean_ctor_get(v___x_1393_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1393_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_err_1407_);
lean_inc(v_pos_1406_);
lean_dec(v___x_1393_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_pos_1406_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_err_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(lean_object* v_a_1415_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_unsigned_to_nat(4u);
v___x_1417_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1416_, v_a_1415_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_pos_1418_; lean_object* v_res_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1428_; 
v_pos_1418_ = lean_ctor_get(v___x_1417_, 0);
v_res_1419_ = lean_ctor_get(v___x_1417_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1421_ = v___x_1417_;
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_res_1419_);
lean_inc(v_pos_1418_);
lean_dec(v___x_1417_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1423_ = l_ByteSlice_toByteArray(v_res_1419_);
v___x_1424_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(v___x_1423_);
lean_dec_ref(v___x_1423_);
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
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_pos_1418_);
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
else
{
lean_object* v_pos_1429_; lean_object* v_err_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_pos_1429_ = lean_ctor_get(v___x_1417_, 0);
v_err_1430_ = lean_ctor_get(v___x_1417_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1417_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_err_1430_);
lean_inc(v_pos_1429_);
lean_dec(v___x_1417_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_pos_1429_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_err_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(lean_object* v_a_1438_){
_start:
{
lean_object* v_array_1439_; lean_object* v_idx_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_array_1439_ = lean_ctor_get(v_a_1438_, 0);
v_idx_1440_ = lean_ctor_get(v_a_1438_, 1);
v___x_1441_ = lean_byte_array_size(v_array_1439_);
v___x_1442_ = lean_nat_dec_lt(v_idx_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_a_1438_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
return v___x_1444_;
}
else
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1456_; 
lean_inc(v_idx_1440_);
lean_inc_ref(v_array_1439_);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_a_1438_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; lean_object* v_unused_1458_; 
v_unused_1457_ = lean_ctor_get(v_a_1438_, 1);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_a_1438_, 0);
lean_dec(v_unused_1458_);
v___x_1446_ = v_a_1438_;
v_isShared_1447_ = v_isSharedCheck_1456_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v_a_1438_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1456_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
uint8_t v_c_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_it_x27_1452_; 
v_c_1448_ = lean_byte_array_fget(v_array_1439_, v_idx_1440_);
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_nat_add(v_idx_1440_, v___x_1449_);
lean_dec(v_idx_1440_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v___x_1450_);
v_it_x27_1452_ = v___x_1446_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_array_1439_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1450_);
v_it_x27_1452_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_box(v_c_1448_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_it_x27_1452_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_a_1459_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_pos_1461_; lean_object* v_res_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1479_; 
v_pos_1461_ = lean_ctor_get(v___x_1460_, 0);
v_res_1462_ = lean_ctor_get(v___x_1460_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1464_ = v___x_1460_;
v_isShared_1465_ = v_isSharedCheck_1479_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_res_1462_);
lean_inc(v_pos_1461_);
lean_dec(v___x_1460_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1479_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
uint8_t v___x_1466_; uint8_t v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = 0;
v___x_1467_ = lean_unbox(v_res_1462_);
lean_dec(v_res_1462_);
v___x_1468_ = lean_uint8_dec_eq(v___x_1467_, v___x_1466_);
if (v___x_1468_ == 0)
{
uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1469_ = 1;
v___x_1470_ = lean_box(v___x_1469_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v___x_1470_);
v___x_1472_ = v___x_1464_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_pos_1461_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
else
{
uint8_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1474_ = 0;
v___x_1475_ = lean_box(v___x_1474_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v___x_1475_);
v___x_1477_ = v___x_1464_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_pos_1461_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_pos_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1488_; 
v_pos_1480_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v___x_1460_, 1);
lean_dec(v_unused_1489_);
v___x_1482_ = v___x_1460_;
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_pos_1480_);
lean_dec(v___x_1460_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = lean_box(0);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1484_);
v___x_1486_ = v___x_1482_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_pos_1480_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0(void){
_start:
{
lean_object* v___x_1490_; lean_object* v_utf8_1491_; 
v___x_1490_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17));
v_utf8_1491_ = lean_string_to_utf8(v___x_1490_);
return v_utf8_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(lean_object* v_a_1492_){
_start:
{
lean_object* v_utf8_1493_; lean_object* v___x_1494_; 
v_utf8_1493_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0);
v___x_1494_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1493_, v_a_1492_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_pos_1495_; lean_object* v___x_1496_; 
v_pos_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_pos_1495_);
lean_dec_ref_known(v___x_1494_, 2);
v___x_1496_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_pos_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_pos_1497_; lean_object* v_res_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_pos_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_pos_1497_);
v_res_1498_ = lean_ctor_get(v___x_1496_, 1);
lean_inc(v_res_1498_);
lean_dec_ref_known(v___x_1496_, 2);
v___x_1499_ = lean_unsigned_to_nat(15u);
v___x_1500_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1499_, v_pos_1497_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_pos_1501_; lean_object* v___x_1502_; 
v_pos_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_pos_1501_);
lean_dec_ref_known(v___x_1500_, 2);
v___x_1502_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_pos_1503_; lean_object* v_res_1504_; lean_object* v___x_1505_; 
v_pos_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_pos_1503_);
v_res_1504_ = lean_ctor_get(v___x_1502_, 1);
lean_inc(v_res_1504_);
lean_dec_ref_known(v___x_1502_, 2);
v___x_1505_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1503_);
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
lean_object* v_pos_1518_; lean_object* v_res_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1534_; 
v_pos_1518_ = lean_ctor_get(v___x_1517_, 0);
v_res_1519_ = lean_ctor_get(v___x_1517_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1521_ = v___x_1517_;
v_isShared_1522_ = v_isSharedCheck_1534_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_res_1519_);
lean_inc(v_pos_1518_);
lean_dec(v___x_1517_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1534_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; uint8_t v___x_1524_; uint32_t v___x_1525_; uint32_t v___x_1526_; uint32_t v___x_1527_; uint32_t v___x_1528_; uint32_t v___x_1529_; uint32_t v___x_1530_; lean_object* v___x_1532_; 
v___x_1523_ = lean_alloc_ctor(0, 0, 25);
v___x_1524_ = lean_unbox(v_res_1498_);
lean_dec(v_res_1498_);
lean_ctor_set_uint8(v___x_1523_, 24, v___x_1524_);
v___x_1525_ = lean_unbox_uint32(v_res_1504_);
lean_dec(v_res_1504_);
lean_ctor_set_uint32(v___x_1523_, 0, v___x_1525_);
v___x_1526_ = lean_unbox_uint32(v_res_1507_);
lean_dec(v_res_1507_);
lean_ctor_set_uint32(v___x_1523_, 4, v___x_1526_);
v___x_1527_ = lean_unbox_uint32(v_res_1510_);
lean_dec(v_res_1510_);
lean_ctor_set_uint32(v___x_1523_, 8, v___x_1527_);
v___x_1528_ = lean_unbox_uint32(v_res_1513_);
lean_dec(v_res_1513_);
lean_ctor_set_uint32(v___x_1523_, 12, v___x_1528_);
v___x_1529_ = lean_unbox_uint32(v_res_1516_);
lean_dec(v_res_1516_);
lean_ctor_set_uint32(v___x_1523_, 16, v___x_1529_);
v___x_1530_ = lean_unbox_uint32(v_res_1519_);
lean_dec(v_res_1519_);
lean_ctor_set_uint32(v___x_1523_, 20, v___x_1530_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1523_);
v___x_1532_ = v___x_1521_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_pos_1518_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1523_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
else
{
lean_object* v_pos_1535_; lean_object* v_err_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v_res_1516_);
lean_dec(v_res_1513_);
lean_dec(v_res_1510_);
lean_dec(v_res_1507_);
lean_dec(v_res_1504_);
lean_dec(v_res_1498_);
v_pos_1535_ = lean_ctor_get(v___x_1517_, 0);
v_err_1536_ = lean_ctor_get(v___x_1517_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1517_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_err_1536_);
lean_inc(v_pos_1535_);
lean_dec(v___x_1517_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_pos_1535_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_err_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_pos_1544_; lean_object* v_err_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_res_1513_);
lean_dec(v_res_1510_);
lean_dec(v_res_1507_);
lean_dec(v_res_1504_);
lean_dec(v_res_1498_);
v_pos_1544_ = lean_ctor_get(v___x_1514_, 0);
v_err_1545_ = lean_ctor_get(v___x_1514_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1514_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_err_1545_);
lean_inc(v_pos_1544_);
lean_dec(v___x_1514_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_pos_1544_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_err_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_pos_1553_; lean_object* v_err_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v_res_1510_);
lean_dec(v_res_1507_);
lean_dec(v_res_1504_);
lean_dec(v_res_1498_);
v_pos_1553_ = lean_ctor_get(v___x_1511_, 0);
v_err_1554_ = lean_ctor_get(v___x_1511_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1511_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_err_1554_);
lean_inc(v_pos_1553_);
lean_dec(v___x_1511_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_pos_1553_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_err_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_pos_1562_; lean_object* v_err_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_res_1507_);
lean_dec(v_res_1504_);
lean_dec(v_res_1498_);
v_pos_1562_ = lean_ctor_get(v___x_1508_, 0);
v_err_1563_ = lean_ctor_get(v___x_1508_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1508_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_err_1563_);
lean_inc(v_pos_1562_);
lean_dec(v___x_1508_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_pos_1562_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_err_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_object* v_pos_1571_; lean_object* v_err_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_res_1504_);
lean_dec(v_res_1498_);
v_pos_1571_ = lean_ctor_get(v___x_1505_, 0);
v_err_1572_ = lean_ctor_get(v___x_1505_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1505_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_err_1572_);
lean_inc(v_pos_1571_);
lean_dec(v___x_1505_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_pos_1571_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_err_1572_);
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
else
{
lean_object* v_pos_1580_; lean_object* v_err_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_res_1498_);
v_pos_1580_ = lean_ctor_get(v___x_1502_, 0);
v_err_1581_ = lean_ctor_get(v___x_1502_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1502_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_err_1581_);
lean_inc(v_pos_1580_);
lean_dec(v___x_1502_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_pos_1580_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_err_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_object* v_pos_1589_; lean_object* v_err_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v_res_1498_);
v_pos_1589_ = lean_ctor_get(v___x_1500_, 0);
v_err_1590_ = lean_ctor_get(v___x_1500_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1500_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_err_1590_);
lean_inc(v_pos_1589_);
lean_dec(v___x_1500_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_pos_1589_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_err_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v_pos_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1606_; 
v_pos_1598_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v___x_1496_, 1);
lean_dec(v_unused_1607_);
v___x_1600_ = v___x_1496_;
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_pos_1598_);
lean_dec(v___x_1496_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = lean_box(0);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 1, v___x_1602_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_pos_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v_pos_1608_; lean_object* v_err_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
v_pos_1608_ = lean_ctor_get(v___x_1494_, 0);
v_err_1609_ = lean_ctor_get(v___x_1494_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1494_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_err_1609_);
lean_inc(v_pos_1608_);
lean_dec(v___x_1494_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_pos_1608_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_err_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType(lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(v_a_1617_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_pos_1619_; lean_object* v_res_1620_; lean_object* v___x_1621_; 
v_pos_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_pos_1619_);
v_res_1620_ = lean_ctor_get(v___x_1618_, 1);
lean_inc(v_res_1620_);
lean_dec_ref_known(v___x_1618_, 2);
v___x_1621_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(v_pos_1619_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_pos_1622_; lean_object* v_res_1623_; lean_object* v___x_1624_; 
v_pos_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_pos_1622_);
v_res_1623_ = lean_ctor_get(v___x_1621_, 1);
lean_inc(v_res_1623_);
lean_dec_ref_known(v___x_1621_, 2);
v___x_1624_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_pos_1622_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_pos_1625_; lean_object* v_res_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1636_; 
v_pos_1625_ = lean_ctor_get(v___x_1624_, 0);
v_res_1626_ = lean_ctor_get(v___x_1624_, 1);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1628_ = v___x_1624_;
v_isShared_1629_ = v_isSharedCheck_1636_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_res_1626_);
lean_inc(v_pos_1625_);
lean_dec(v___x_1624_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1636_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; uint8_t v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1634_; 
v___x_1630_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1630_, 0, v_res_1620_);
v___x_1631_ = lean_unbox(v_res_1623_);
lean_dec(v_res_1623_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*1, v___x_1631_);
v___x_1632_ = lean_unbox(v_res_1626_);
lean_dec(v_res_1626_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*1 + 1, v___x_1632_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 1, v___x_1630_);
v___x_1634_ = v___x_1628_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_pos_1625_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v___x_1630_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_object* v_pos_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_res_1623_);
lean_dec(v_res_1620_);
v_pos_1637_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v___x_1624_, 1);
lean_dec(v_unused_1646_);
v___x_1639_ = v___x_1624_;
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_pos_1637_);
lean_dec(v___x_1624_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = lean_box(0);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 1, v___x_1641_);
v___x_1643_ = v___x_1639_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_pos_1637_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v_pos_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1655_; 
lean_dec(v_res_1620_);
v_pos_1647_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; 
v_unused_1656_ = lean_ctor_get(v___x_1621_, 1);
lean_dec(v_unused_1656_);
v___x_1649_ = v___x_1621_;
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_pos_1647_);
lean_dec(v___x_1621_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_box(0);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 1, v___x_1651_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_pos_1647_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_pos_1657_; lean_object* v_err_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v_pos_1657_ = lean_ctor_get(v___x_1618_, 0);
v_err_1658_ = lean_ctor_get(v___x_1618_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1618_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_err_1658_);
lean_inc(v_pos_1657_);
lean_dec(v___x_1618_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_pos_1657_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_err_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond(lean_object* v_p_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_apply_1(v_p_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_pos_1669_; lean_object* v_res_1670_; lean_object* v___x_1671_; 
v_pos_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_pos_1669_);
v_res_1670_ = lean_ctor_get(v___x_1668_, 1);
lean_inc(v_res_1670_);
lean_dec_ref_known(v___x_1668_, 2);
v___x_1671_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(v_pos_1669_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_pos_1672_; lean_object* v_res_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1681_; 
v_pos_1672_ = lean_ctor_get(v___x_1671_, 0);
v_res_1673_ = lean_ctor_get(v___x_1671_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1675_ = v___x_1671_;
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_res_1673_);
lean_inc(v_pos_1672_);
lean_dec(v___x_1671_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v_res_1670_);
lean_ctor_set(v___x_1677_, 1, v_res_1673_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 1, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_pos_1672_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_object* v_pos_1682_; lean_object* v_err_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v_res_1670_);
v_pos_1682_ = lean_ctor_get(v___x_1671_, 0);
v_err_1683_ = lean_ctor_get(v___x_1671_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1671_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_err_1683_);
lean_inc(v_pos_1682_);
lean_dec(v___x_1671_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_pos_1682_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_err_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_object* v_pos_1691_; lean_object* v_err_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
v_pos_1691_ = lean_ctor_get(v___x_1668_, 0);
v_err_1692_ = lean_ctor_get(v___x_1668_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1668_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_err_1692_);
lean_inc(v_pos_1691_);
lean_dec(v___x_1668_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_pos_1691_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_err_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(lean_object* v_size_1700_, uint32_t v_n_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_uint32_to_nat(v_n_1701_);
v___x_1704_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1703_, v_size_1700_, v_a_1702_);
lean_dec(v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes___boxed(lean_object* v_size_1705_, lean_object* v_n_1706_, lean_object* v_a_1707_){
_start:
{
uint32_t v_n_boxed_1708_; lean_object* v_res_1709_; 
v_n_boxed_1708_ = lean_unbox_uint32(v_n_1706_);
lean_dec(v_n_1706_);
v_res_1709_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v_size_1705_, v_n_boxed_1708_, v_a_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(uint32_t v_n_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_uint32_to_nat(v_n_1710_);
v___x_1713_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8), 1, 0);
v___x_1714_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1712_, v___x_1713_, v_a_1711_);
lean_dec(v___x_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices___boxed(lean_object* v_n_1715_, lean_object* v_a_1716_){
_start:
{
uint32_t v_n_boxed_1717_; lean_object* v_res_1718_; 
v_n_boxed_1717_ = lean_unbox_uint32(v_n_1715_);
lean_dec(v_n_1715_);
v_res_1718_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_n_boxed_1717_, v_a_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(uint32_t v_n_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_uint32_to_nat(v_n_1719_);
v___x_1722_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType), 1, 0);
v___x_1723_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1721_, v___x_1722_, v_a_1720_);
lean_dec(v___x_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes___boxed(lean_object* v_n_1724_, lean_object* v_a_1725_){
_start:
{
uint32_t v_n_boxed_1726_; lean_object* v_res_1727_; 
v_n_boxed_1726_ = lean_unbox_uint32(v_n_1724_);
lean_dec(v_n_1724_);
v_res_1727_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_n_boxed_1726_, v_a_1725_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(lean_object* v_upperBound_1729_, lean_object* v_res_1730_, lean_object* v_a_1731_, lean_object* v_b_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_nat_dec_lt(v_a_1731_, v_upperBound_1729_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; 
lean_dec(v_a_1731_);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___y_1733_);
lean_ctor_set(v___x_1735_, 1, v_b_1732_);
return v___x_1735_;
}
else
{
lean_object* v_fst_1736_; lean_object* v_snd_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1761_; 
v_fst_1736_ = lean_ctor_get(v_b_1732_, 0);
v_snd_1737_ = lean_ctor_get(v_b_1732_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_b_1732_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1739_ = v_b_1732_;
v_isShared_1740_ = v_isSharedCheck_1761_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_snd_1737_);
lean_inc(v_fst_1736_);
lean_dec(v_b_1732_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1761_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
uint8_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; uint8_t v___x_1745_; 
v___x_1741_ = 0;
v___x_1742_ = lean_box(v___x_1741_);
v___x_1743_ = lean_array_get(v___x_1742_, v_res_1730_, v_a_1731_);
lean_dec(v___x_1742_);
v___x_1744_ = lean_unbox(v___x_1743_);
v___x_1745_ = lean_uint8_dec_eq(v___x_1744_, v___x_1741_);
if (v___x_1745_ == 0)
{
uint8_t v___x_1746_; uint32_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1746_ = lean_unbox(v___x_1743_);
lean_dec(v___x_1743_);
v___x_1747_ = lean_uint8_to_uint32(v___x_1746_);
v___x_1748_ = lean_string_push(v_snd_1737_, v___x_1747_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v___x_1748_);
v___x_1750_ = v___x_1739_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_fst_1736_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_unsigned_to_nat(1u);
v___x_1752_ = lean_nat_add(v_a_1731_, v___x_1751_);
lean_dec(v_a_1731_);
v_a_1731_ = v___x_1752_;
v_b_1732_ = v___x_1750_;
goto _start;
}
}
else
{
lean_object* v_current_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec(v___x_1743_);
lean_dec(v_a_1731_);
v_current_1755_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0));
v___x_1756_ = lean_array_push(v_fst_1736_, v_snd_1737_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v_current_1755_);
lean_ctor_set(v___x_1739_, 0, v___x_1756_);
v___x_1758_ = v___x_1739_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_current_1755_);
v___x_1758_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___y_1733_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
return v___x_1759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___boxed(lean_object* v_upperBound_1762_, lean_object* v_res_1763_, lean_object* v_a_1764_, lean_object* v_b_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_1762_, v_res_1763_, v_a_1764_, v_b_1765_, v___y_1766_);
lean_dec_ref(v_res_1763_);
lean_dec(v_upperBound_1762_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(lean_object* v___x_1768_, lean_object* v_res_1769_, lean_object* v_as_1770_, size_t v_sz_1771_, size_t v_i_1772_, lean_object* v_b_1773_, lean_object* v___y_1774_){
_start:
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_usize_dec_lt(v_i_1772_, v_sz_1771_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___y_1774_);
lean_ctor_set(v___x_1776_, 1, v_b_1773_);
return v___x_1776_;
}
else
{
lean_object* v_a_1777_; uint8_t v_abbreviationIndex_1778_; lean_object* v_fst_1779_; lean_object* v_snd_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1803_; 
v_a_1777_ = lean_array_uget_borrowed(v_as_1770_, v_i_1772_);
v_abbreviationIndex_1778_ = lean_ctor_get_uint8(v_a_1777_, sizeof(void*)*1 + 1);
v_fst_1779_ = lean_ctor_get(v_b_1773_, 0);
v_snd_1780_ = lean_ctor_get(v_b_1773_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_b_1773_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1782_ = v_b_1773_;
v_isShared_1783_ = v_isSharedCheck_1803_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_snd_1780_);
lean_inc(v_fst_1779_);
lean_dec(v_b_1773_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1803_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1784_ = lean_uint8_to_nat(v_abbreviationIndex_1778_);
if (v_isShared_1783_ == 0)
{
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_fst_1779_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_snd_1780_);
v___x_1786_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v___x_1768_, v_res_1769_, v___x_1784_, v___x_1786_, v___y_1774_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_res_1788_; lean_object* v_pos_1789_; lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1801_; 
v_res_1788_ = lean_ctor_get(v___x_1787_, 1);
lean_inc(v_res_1788_);
v_pos_1789_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_pos_1789_);
lean_dec_ref_known(v___x_1787_, 2);
v_fst_1790_ = lean_ctor_get(v_res_1788_, 0);
v_snd_1791_ = lean_ctor_get(v_res_1788_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_res_1788_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1793_ = v_res_1788_;
v_isShared_1794_ = v_isSharedCheck_1801_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
lean_dec(v_res_1788_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1801_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_fst_1790_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_snd_1791_);
v___x_1796_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
size_t v___x_1797_; size_t v___x_1798_; 
v___x_1797_ = ((size_t)1ULL);
v___x_1798_ = lean_usize_add(v_i_1772_, v___x_1797_);
v_i_1772_ = v___x_1798_;
v_b_1773_ = v___x_1796_;
v___y_1774_ = v_pos_1789_;
goto _start;
}
}
}
else
{
return v___x_1787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1___boxed(lean_object* v___x_1804_, lean_object* v_res_1805_, lean_object* v_as_1806_, lean_object* v_sz_1807_, lean_object* v_i_1808_, lean_object* v_b_1809_, lean_object* v___y_1810_){
_start:
{
size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; lean_object* v_res_1813_; 
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1807_);
lean_dec(v_sz_1807_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1808_);
lean_dec(v_i_1808_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_1804_, v_res_1805_, v_as_1806_, v_sz_boxed_1811_, v_i_boxed_1812_, v_b_1809_, v___y_1810_);
lean_dec_ref(v_as_1806_);
lean_dec_ref(v_res_1805_);
lean_dec(v___x_1804_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(lean_object* v_times_1819_, uint32_t v_n_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_uint32_to_nat(v_n_1820_);
v___x_1823_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8), 1, 0);
v___x_1824_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1822_, v___x_1823_, v_a_1821_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_pos_1825_; lean_object* v_res_1826_; lean_object* v___x_1827_; size_t v_sz_1828_; size_t v___x_1829_; lean_object* v___x_1830_; 
v_pos_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_pos_1825_);
v_res_1826_ = lean_ctor_get(v___x_1824_, 1);
lean_inc(v_res_1826_);
lean_dec_ref_known(v___x_1824_, 2);
v___x_1827_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1));
v_sz_1828_ = lean_array_size(v_times_1819_);
v___x_1829_ = ((size_t)0ULL);
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_1822_, v_res_1826_, v_times_1819_, v_sz_1828_, v___x_1829_, v___x_1827_, v_pos_1825_);
lean_dec(v_res_1826_);
lean_dec(v___x_1822_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_res_1831_; lean_object* v_pos_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1840_; 
v_res_1831_ = lean_ctor_get(v___x_1830_, 1);
v_pos_1832_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1834_ = v___x_1830_;
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_res_1831_);
lean_inc(v_pos_1832_);
lean_dec(v___x_1830_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v_fst_1836_; lean_object* v___x_1838_; 
v_fst_1836_ = lean_ctor_get(v_res_1831_, 0);
lean_inc(v_fst_1836_);
lean_dec(v_res_1831_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v_fst_1836_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_pos_1832_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_fst_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
else
{
lean_object* v_pos_1841_; lean_object* v_err_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_pos_1841_ = lean_ctor_get(v___x_1830_, 0);
v_err_1842_ = lean_ctor_get(v___x_1830_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1830_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_err_1842_);
lean_inc(v_pos_1841_);
lean_dec(v___x_1830_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_pos_1841_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_err_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
lean_object* v_pos_1850_; lean_object* v_err_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v___x_1822_);
v_pos_1850_ = lean_ctor_get(v___x_1824_, 0);
v_err_1851_ = lean_ctor_get(v___x_1824_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1824_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_err_1851_);
lean_inc(v_pos_1850_);
lean_dec(v___x_1824_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_pos_1850_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_err_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___boxed(lean_object* v_times_1859_, lean_object* v_n_1860_, lean_object* v_a_1861_){
_start:
{
uint32_t v_n_boxed_1862_; lean_object* v_res_1863_; 
v_n_boxed_1862_ = lean_unbox_uint32(v_n_1860_);
lean_dec(v_n_1860_);
v_res_1863_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_times_1859_, v_n_boxed_1862_, v_a_1861_);
lean_dec_ref(v_times_1859_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(lean_object* v_upperBound_1864_, lean_object* v_res_1865_, lean_object* v_inst_1866_, lean_object* v_R_1867_, lean_object* v_a_1868_, lean_object* v_b_1869_, lean_object* v_c_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_1864_, v_res_1865_, v_a_1868_, v_b_1869_, v___y_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___boxed(lean_object* v_upperBound_1873_, lean_object* v_res_1874_, lean_object* v_inst_1875_, lean_object* v_R_1876_, lean_object* v_a_1877_, lean_object* v_b_1878_, lean_object* v_c_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(v_upperBound_1873_, v_res_1874_, v_inst_1875_, v_R_1876_, v_a_1877_, v_b_1878_, v_c_1879_, v___y_1880_);
lean_dec_ref(v_res_1874_);
lean_dec(v_upperBound_1873_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(lean_object* v_size_1882_, uint32_t v_n_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = lean_uint32_to_nat(v_n_1883_);
v___x_1886_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond), 2, 1);
lean_closure_set(v___x_1886_, 0, v_size_1882_);
v___x_1887_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1885_, v___x_1886_, v_a_1884_);
lean_dec(v___x_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds___boxed(lean_object* v_size_1888_, lean_object* v_n_1889_, lean_object* v_a_1890_){
_start:
{
uint32_t v_n_boxed_1891_; lean_object* v_res_1892_; 
v_n_boxed_1891_ = lean_unbox_uint32(v_n_1889_);
lean_dec(v_n_1889_);
v_res_1892_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v_size_1888_, v_n_boxed_1891_, v_a_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(uint32_t v_n_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_uint32_to_nat(v_n_1893_);
v___x_1896_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool), 1, 0);
v___x_1897_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1895_, v___x_1896_, v_a_1894_);
lean_dec(v___x_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators___boxed(lean_object* v_n_1898_, lean_object* v_a_1899_){
_start:
{
uint32_t v_n_boxed_1900_; lean_object* v_res_1901_; 
v_n_boxed_1900_ = lean_unbox_uint32(v_n_1898_);
lean_dec(v_n_1898_);
v_res_1901_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_n_boxed_1900_, v_a_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(v_a_1902_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_res_1904_; lean_object* v_pos_1905_; uint32_t v_isutcnt_1906_; uint32_t v_isstdcnt_1907_; uint32_t v_leapcnt_1908_; uint32_t v_timecnt_1909_; uint32_t v_typecnt_1910_; uint32_t v_charcnt_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_res_1904_ = lean_ctor_get(v___x_1903_, 1);
lean_inc(v_res_1904_);
v_pos_1905_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_pos_1905_);
lean_dec_ref_known(v___x_1903_, 2);
v_isutcnt_1906_ = lean_ctor_get_uint32(v_res_1904_, 0);
v_isstdcnt_1907_ = lean_ctor_get_uint32(v_res_1904_, 4);
v_leapcnt_1908_ = lean_ctor_get_uint32(v_res_1904_, 8);
v_timecnt_1909_ = lean_ctor_get_uint32(v_res_1904_, 12);
v_typecnt_1910_ = lean_ctor_get_uint32(v_res_1904_, 16);
v_charcnt_1911_ = lean_ctor_get_uint32(v_res_1904_, 20);
v___x_1912_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32), 1, 0);
lean_inc_ref(v___x_1912_);
v___x_1913_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_1912_, v_timecnt_1909_, v_pos_1905_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_pos_1914_; lean_object* v_res_1915_; lean_object* v___x_1916_; 
v_pos_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_pos_1914_);
v_res_1915_ = lean_ctor_get(v___x_1913_, 1);
lean_inc(v_res_1915_);
lean_dec_ref_known(v___x_1913_, 2);
v___x_1916_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_1909_, v_pos_1914_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_pos_1917_; lean_object* v_res_1918_; lean_object* v___x_1919_; 
v_pos_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_pos_1917_);
v_res_1918_ = lean_ctor_get(v___x_1916_, 1);
lean_inc(v_res_1918_);
lean_dec_ref_known(v___x_1916_, 2);
v___x_1919_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_1910_, v_pos_1917_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_pos_1920_; lean_object* v_res_1921_; lean_object* v___x_1922_; 
v_pos_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_pos_1920_);
v_res_1921_ = lean_ctor_get(v___x_1919_, 1);
lean_inc(v_res_1921_);
lean_dec_ref_known(v___x_1919_, 2);
v___x_1922_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_1921_, v_charcnt_1911_, v_pos_1920_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_pos_1923_; lean_object* v_res_1924_; lean_object* v___x_1925_; 
v_pos_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_pos_1923_);
v_res_1924_ = lean_ctor_get(v___x_1922_, 1);
lean_inc(v_res_1924_);
lean_dec_ref_known(v___x_1922_, 2);
v___x_1925_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_1912_, v_leapcnt_1908_, v_pos_1923_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_pos_1926_; lean_object* v_res_1927_; lean_object* v___x_1928_; 
v_pos_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_pos_1926_);
v_res_1927_ = lean_ctor_get(v___x_1925_, 1);
lean_inc(v_res_1927_);
lean_dec_ref_known(v___x_1925_, 2);
v___x_1928_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_1907_, v_pos_1926_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_pos_1929_; lean_object* v_res_1930_; lean_object* v___x_1931_; 
v_pos_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_pos_1929_);
v_res_1930_ = lean_ctor_get(v___x_1928_, 1);
lean_inc(v_res_1930_);
lean_dec_ref_known(v___x_1928_, 2);
v___x_1931_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_1906_, v_pos_1929_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_pos_1932_; lean_object* v_res_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1941_; 
v_pos_1932_ = lean_ctor_get(v___x_1931_, 0);
v_res_1933_ = lean_ctor_get(v___x_1931_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1935_ = v___x_1931_;
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_res_1933_);
lean_inc(v_pos_1932_);
lean_dec(v___x_1931_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1937_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1937_, 0, v_res_1904_);
lean_ctor_set(v___x_1937_, 1, v_res_1915_);
lean_ctor_set(v___x_1937_, 2, v_res_1918_);
lean_ctor_set(v___x_1937_, 3, v_res_1921_);
lean_ctor_set(v___x_1937_, 4, v_res_1924_);
lean_ctor_set(v___x_1937_, 5, v_res_1927_);
lean_ctor_set(v___x_1937_, 6, v_res_1930_);
lean_ctor_set(v___x_1937_, 7, v_res_1933_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v___x_1937_);
v___x_1939_ = v___x_1935_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_pos_1932_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
else
{
lean_object* v_pos_1942_; lean_object* v_err_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_res_1930_);
lean_dec(v_res_1927_);
lean_dec(v_res_1924_);
lean_dec(v_res_1921_);
lean_dec(v_res_1918_);
lean_dec(v_res_1915_);
lean_dec(v_res_1904_);
v_pos_1942_ = lean_ctor_get(v___x_1931_, 0);
v_err_1943_ = lean_ctor_get(v___x_1931_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1931_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_err_1943_);
lean_inc(v_pos_1942_);
lean_dec(v___x_1931_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_pos_1942_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_err_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_pos_1951_; lean_object* v_err_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_res_1927_);
lean_dec(v_res_1924_);
lean_dec(v_res_1921_);
lean_dec(v_res_1918_);
lean_dec(v_res_1915_);
lean_dec(v_res_1904_);
v_pos_1951_ = lean_ctor_get(v___x_1928_, 0);
v_err_1952_ = lean_ctor_get(v___x_1928_, 1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1928_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_err_1952_);
lean_inc(v_pos_1951_);
lean_dec(v___x_1928_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_pos_1951_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_err_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_pos_1960_; lean_object* v_err_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v_res_1924_);
lean_dec(v_res_1921_);
lean_dec(v_res_1918_);
lean_dec(v_res_1915_);
lean_dec(v_res_1904_);
v_pos_1960_ = lean_ctor_get(v___x_1925_, 0);
v_err_1961_ = lean_ctor_get(v___x_1925_, 1);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1925_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_err_1961_);
lean_inc(v_pos_1960_);
lean_dec(v___x_1925_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_pos_1960_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_err_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v_pos_1969_; lean_object* v_err_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec(v_res_1921_);
lean_dec(v_res_1918_);
lean_dec(v_res_1915_);
lean_dec_ref(v___x_1912_);
lean_dec(v_res_1904_);
v_pos_1969_ = lean_ctor_get(v___x_1922_, 0);
v_err_1970_ = lean_ctor_get(v___x_1922_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1922_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_err_1970_);
lean_inc(v_pos_1969_);
lean_dec(v___x_1922_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_pos_1969_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_err_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_object* v_pos_1978_; lean_object* v_err_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v_res_1918_);
lean_dec(v_res_1915_);
lean_dec_ref(v___x_1912_);
lean_dec(v_res_1904_);
v_pos_1978_ = lean_ctor_get(v___x_1919_, 0);
v_err_1979_ = lean_ctor_get(v___x_1919_, 1);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1919_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_err_1979_);
lean_inc(v_pos_1978_);
lean_dec(v___x_1919_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_pos_1978_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_err_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_pos_1987_; lean_object* v_err_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_res_1915_);
lean_dec_ref(v___x_1912_);
lean_dec(v_res_1904_);
v_pos_1987_ = lean_ctor_get(v___x_1916_, 0);
v_err_1988_ = lean_ctor_get(v___x_1916_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1916_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_err_1988_);
lean_inc(v_pos_1987_);
lean_dec(v___x_1916_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_pos_1987_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_err_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v_pos_1996_; lean_object* v_err_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v___x_1912_);
lean_dec(v_res_1904_);
v_pos_1996_ = lean_ctor_get(v___x_1913_, 0);
v_err_1997_ = lean_ctor_get(v___x_1913_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1913_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_err_1997_);
lean_inc(v_pos_1996_);
lean_dec(v___x_1913_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_pos_1996_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_err_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_pos_2005_; lean_object* v_err_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
v_pos_2005_ = lean_ctor_get(v___x_1903_, 0);
v_err_2006_ = lean_ctor_get(v___x_1903_, 1);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1903_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_err_2006_);
lean_inc(v_pos_2005_);
lean_dec(v___x_1903_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_pos_2005_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_err_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(lean_object* v_as_2014_, size_t v_sz_2015_, size_t v_i_2016_, lean_object* v_b_2017_, lean_object* v___y_2018_){
_start:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_usize_dec_lt(v_i_2016_, v_sz_2015_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___y_2018_);
lean_ctor_set(v___x_2020_, 1, v_b_2017_);
return v___x_2020_;
}
else
{
lean_object* v_a_2021_; uint8_t v___x_2022_; uint32_t v___x_2023_; lean_object* v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; 
v_a_2021_ = lean_array_uget_borrowed(v_as_2014_, v_i_2016_);
v___x_2022_ = lean_unbox(v_a_2021_);
v___x_2023_ = lean_uint8_to_uint32(v___x_2022_);
v___x_2024_ = lean_string_push(v_b_2017_, v___x_2023_);
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_2016_, v___x_2025_);
v_i_2016_ = v___x_2026_;
v_b_2017_ = v___x_2024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1___boxed(lean_object* v_as_2028_, lean_object* v_sz_2029_, lean_object* v_i_2030_, lean_object* v_b_2031_, lean_object* v___y_2032_){
_start:
{
size_t v_sz_boxed_2033_; size_t v_i_boxed_2034_; lean_object* v_res_2035_; 
v_sz_boxed_2033_ = lean_unbox_usize(v_sz_2029_);
lean_dec(v_sz_2029_);
v_i_boxed_2034_ = lean_unbox_usize(v_i_2030_);
lean_dec(v_i_2030_);
v_res_2035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_as_2028_, v_sz_boxed_2033_, v_i_boxed_2034_, v_b_2031_, v___y_2032_);
lean_dec_ref(v_as_2028_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(lean_object* v_acc_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_array_2041_; lean_object* v_idx_2042_; lean_object* v_pos_2044_; lean_object* v_idx_2045_; lean_object* v_err_2046_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_array_2041_ = lean_ctor_get(v_a_2040_, 0);
v_idx_2042_ = lean_ctor_get(v_a_2040_, 1);
lean_inc(v_idx_2042_);
v___x_2052_ = lean_byte_array_size(v_array_2041_);
v___x_2053_ = lean_nat_dec_lt(v_idx_2042_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_box(0);
lean_inc(v_idx_2042_);
v_pos_2044_ = v_a_2040_;
v_idx_2045_ = v_idx_2042_;
v_err_2046_ = v___x_2054_;
goto v___jp_2043_;
}
else
{
uint8_t v___x_2055_; uint8_t v_c_2056_; uint8_t v___x_2057_; 
v___x_2055_ = 10;
v_c_2056_ = lean_byte_array_fget(v_array_2041_, v_idx_2042_);
v___x_2057_ = lean_uint8_dec_eq(v_c_2056_, v___x_2055_);
if (v___x_2057_ == 0)
{
if (v___x_2053_ == 0)
{
goto v___jp_2050_;
}
else
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2069_; 
lean_inc_ref(v_array_2041_);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_a_2040_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; lean_object* v_unused_2071_; 
v_unused_2070_ = lean_ctor_get(v_a_2040_, 1);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_a_2040_, 0);
lean_dec(v_unused_2071_);
v___x_2059_ = v_a_2040_;
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v_a_2040_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v_it_x27_2064_; 
v___x_2061_ = lean_unsigned_to_nat(1u);
v___x_2062_ = lean_nat_add(v_idx_2042_, v___x_2061_);
lean_dec(v_idx_2042_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2062_);
v_it_x27_2064_ = v___x_2059_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_array_2041_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2062_);
v_it_x27_2064_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_box(v_c_2056_);
v___x_2066_ = lean_array_push(v_acc_2039_, v___x_2065_);
v_acc_2039_ = v___x_2066_;
v_a_2040_ = v_it_x27_2064_;
goto _start;
}
}
}
}
else
{
goto v___jp_2050_;
}
}
v___jp_2043_:
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_nat_dec_eq(v_idx_2042_, v_idx_2045_);
lean_dec(v_idx_2045_);
lean_dec(v_idx_2042_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec_ref(v_acc_2039_);
lean_inc(v_err_2046_);
v___x_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2048_, 0, v_pos_2044_);
lean_ctor_set(v___x_2048_, 1, v_err_2046_);
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v_pos_2044_);
lean_ctor_set(v___x_2049_, 1, v_acc_2039_);
return v___x_2049_;
}
}
v___jp_2050_:
{
lean_object* v___x_2051_; 
v___x_2051_ = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1));
lean_inc(v_idx_2042_);
v_pos_2044_ = v_a_2040_;
v_idx_2045_ = v_idx_2042_;
v_err_2046_ = v___x_2051_;
goto v___jp_2043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(lean_object* v_a_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_a_2074_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_pos_2076_; lean_object* v_res_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2124_; 
v_pos_2076_ = lean_ctor_get(v___x_2075_, 0);
v_res_2077_ = lean_ctor_get(v___x_2075_, 1);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2079_ = v___x_2075_;
v_isShared_2080_ = v_isSharedCheck_2124_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_res_2077_);
lean_inc(v_pos_2076_);
lean_dec(v___x_2075_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2124_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
uint8_t v___x_2081_; uint8_t v___x_2082_; uint8_t v___x_2083_; 
v___x_2081_ = 10;
v___x_2082_ = lean_unbox(v_res_2077_);
lean_dec(v_res_2077_);
v___x_2083_ = lean_uint8_dec_eq(v___x_2082_, v___x_2081_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = lean_box(0);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v___x_2084_);
v___x_2086_ = v___x_2079_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_pos_2076_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_del_object(v___x_2079_);
v___x_2088_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0));
v___x_2089_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(v___x_2088_, v_pos_2076_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_pos_2090_; lean_object* v_res_2091_; lean_object* v___x_2092_; size_t v_sz_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v_pos_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_pos_2090_);
v_res_2091_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_res_2091_);
lean_dec_ref_known(v___x_2089_, 2);
v___x_2092_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0));
v_sz_2093_ = lean_array_size(v_res_2091_);
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_res_2091_, v_sz_2093_, v___x_2094_, v___x_2092_, v_pos_2090_);
lean_dec(v_res_2091_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_pos_2096_; lean_object* v_res_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2105_; 
v_pos_2096_ = lean_ctor_get(v___x_2095_, 0);
v_res_2097_ = lean_ctor_get(v___x_2095_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2099_ = v___x_2095_;
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_res_2097_);
lean_inc(v_pos_2096_);
lean_dec(v___x_2095_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2105_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v_res_2097_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v___x_2101_);
v___x_2103_ = v___x_2099_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_pos_2096_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
else
{
lean_object* v_pos_2106_; lean_object* v_err_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_pos_2106_ = lean_ctor_get(v___x_2095_, 0);
v_err_2107_ = lean_ctor_get(v___x_2095_, 1);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2095_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_err_2107_);
lean_inc(v_pos_2106_);
lean_dec(v___x_2095_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_pos_2106_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_err_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_pos_2115_; lean_object* v_err_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
v_pos_2115_ = lean_ctor_get(v___x_2089_, 0);
v_err_2116_ = lean_ctor_get(v___x_2089_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2089_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_err_2116_);
lean_inc(v_pos_2115_);
lean_dec(v___x_2089_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_pos_2115_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_err_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
}
else
{
lean_object* v_pos_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2133_; 
v_pos_2125_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v___x_2075_, 1);
lean_dec(v_unused_2134_);
v___x_2127_ = v___x_2075_;
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_pos_2125_);
lean_dec(v___x_2075_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_box(0);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 1, v___x_2129_);
v___x_2131_ = v___x_2127_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_pos_2125_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(lean_object* v_a_2135_){
_start:
{
lean_object* v_pos_2137_; lean_object* v_err_2138_; lean_object* v___x_2154_; 
lean_inc_ref(v_a_2135_);
v___x_2154_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(v_a_2135_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_res_2155_; lean_object* v_pos_2156_; uint32_t v_isutcnt_2157_; uint32_t v_isstdcnt_2158_; uint32_t v_leapcnt_2159_; uint32_t v_timecnt_2160_; uint32_t v_typecnt_2161_; uint32_t v_charcnt_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v_res_2155_ = lean_ctor_get(v___x_2154_, 1);
lean_inc(v_res_2155_);
v_pos_2156_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_pos_2156_);
lean_dec_ref_known(v___x_2154_, 2);
v_isutcnt_2157_ = lean_ctor_get_uint32(v_res_2155_, 0);
v_isstdcnt_2158_ = lean_ctor_get_uint32(v_res_2155_, 4);
v_leapcnt_2159_ = lean_ctor_get_uint32(v_res_2155_, 8);
v_timecnt_2160_ = lean_ctor_get_uint32(v_res_2155_, 12);
v_typecnt_2161_ = lean_ctor_get_uint32(v_res_2155_, 16);
v_charcnt_2162_ = lean_ctor_get_uint32(v_res_2155_, 20);
v___x_2163_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64), 1, 0);
lean_inc_ref(v___x_2163_);
v___x_2164_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_2163_, v_timecnt_2160_, v_pos_2156_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_pos_2165_; lean_object* v_res_2166_; lean_object* v___x_2167_; 
v_pos_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_pos_2165_);
v_res_2166_ = lean_ctor_get(v___x_2164_, 1);
lean_inc(v_res_2166_);
lean_dec_ref_known(v___x_2164_, 2);
v___x_2167_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_2160_, v_pos_2165_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_pos_2168_; lean_object* v_res_2169_; lean_object* v___x_2170_; 
v_pos_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_pos_2168_);
v_res_2169_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_res_2169_);
lean_dec_ref_known(v___x_2167_, 2);
v___x_2170_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_2161_, v_pos_2168_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_pos_2171_; lean_object* v_res_2172_; lean_object* v___x_2173_; 
v_pos_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_pos_2171_);
v_res_2172_ = lean_ctor_get(v___x_2170_, 1);
lean_inc(v_res_2172_);
lean_dec_ref_known(v___x_2170_, 2);
v___x_2173_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_2172_, v_charcnt_2162_, v_pos_2171_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_pos_2174_; lean_object* v_res_2175_; lean_object* v___x_2176_; 
v_pos_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_pos_2174_);
v_res_2175_ = lean_ctor_get(v___x_2173_, 1);
lean_inc(v_res_2175_);
lean_dec_ref_known(v___x_2173_, 2);
v___x_2176_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_2163_, v_leapcnt_2159_, v_pos_2174_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_pos_2177_; lean_object* v_res_2178_; lean_object* v___x_2179_; 
v_pos_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_pos_2177_);
v_res_2178_ = lean_ctor_get(v___x_2176_, 1);
lean_inc(v_res_2178_);
lean_dec_ref_known(v___x_2176_, 2);
v___x_2179_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_2158_, v_pos_2177_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_pos_2180_; lean_object* v_res_2181_; lean_object* v___x_2182_; 
v_pos_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_pos_2180_);
v_res_2181_ = lean_ctor_get(v___x_2179_, 1);
lean_inc(v_res_2181_);
lean_dec_ref_known(v___x_2179_, 2);
v___x_2182_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_2157_, v_pos_2180_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_pos_2183_; lean_object* v_res_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2205_; 
v_pos_2183_ = lean_ctor_get(v___x_2182_, 0);
v_res_2184_ = lean_ctor_get(v___x_2182_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2186_ = v___x_2182_;
v_isShared_2187_ = v_isSharedCheck_2205_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_res_2184_);
lean_inc(v_pos_2183_);
lean_dec(v___x_2182_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2205_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; 
v___x_2188_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(v_pos_2183_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_pos_2189_; lean_object* v_res_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2202_; 
lean_dec_ref(v_a_2135_);
v_pos_2189_ = lean_ctor_get(v___x_2188_, 0);
v_res_2190_ = lean_ctor_get(v___x_2188_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2192_ = v___x_2188_;
v_isShared_2193_ = v_isSharedCheck_2202_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_res_2190_);
lean_inc(v_pos_2189_);
lean_dec(v___x_2188_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2202_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2194_, 0, v_res_2155_);
lean_ctor_set(v___x_2194_, 1, v_res_2166_);
lean_ctor_set(v___x_2194_, 2, v_res_2169_);
lean_ctor_set(v___x_2194_, 3, v_res_2172_);
lean_ctor_set(v___x_2194_, 4, v_res_2175_);
lean_ctor_set(v___x_2194_, 5, v_res_2178_);
lean_ctor_set(v___x_2194_, 6, v_res_2181_);
lean_ctor_set(v___x_2194_, 7, v_res_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v_res_2190_);
lean_ctor_set(v___x_2186_, 0, v___x_2194_);
v___x_2196_ = v___x_2186_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_res_2190_);
v___x_2196_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v___x_2197_);
v___x_2199_ = v___x_2192_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_pos_2189_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_pos_2203_; lean_object* v_err_2204_; 
lean_del_object(v___x_2186_);
lean_dec(v_res_2184_);
lean_dec(v_res_2181_);
lean_dec(v_res_2178_);
lean_dec(v_res_2175_);
lean_dec(v_res_2172_);
lean_dec(v_res_2169_);
lean_dec(v_res_2166_);
lean_dec(v_res_2155_);
v_pos_2203_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_pos_2203_);
v_err_2204_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_err_2204_);
lean_dec_ref_known(v___x_2188_, 2);
v_pos_2137_ = v_pos_2203_;
v_err_2138_ = v_err_2204_;
goto v___jp_2136_;
}
}
}
else
{
lean_object* v_pos_2206_; lean_object* v_err_2207_; 
lean_dec(v_res_2181_);
lean_dec(v_res_2178_);
lean_dec(v_res_2175_);
lean_dec(v_res_2172_);
lean_dec(v_res_2169_);
lean_dec(v_res_2166_);
lean_dec(v_res_2155_);
v_pos_2206_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_pos_2206_);
v_err_2207_ = lean_ctor_get(v___x_2182_, 1);
lean_inc(v_err_2207_);
lean_dec_ref_known(v___x_2182_, 2);
v_pos_2137_ = v_pos_2206_;
v_err_2138_ = v_err_2207_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_pos_2208_; lean_object* v_err_2209_; 
lean_dec(v_res_2178_);
lean_dec(v_res_2175_);
lean_dec(v_res_2172_);
lean_dec(v_res_2169_);
lean_dec(v_res_2166_);
lean_dec(v_res_2155_);
v_pos_2208_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_pos_2208_);
v_err_2209_ = lean_ctor_get(v___x_2179_, 1);
lean_inc(v_err_2209_);
lean_dec_ref_known(v___x_2179_, 2);
v_pos_2137_ = v_pos_2208_;
v_err_2138_ = v_err_2209_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_pos_2210_; lean_object* v_err_2211_; 
lean_dec(v_res_2175_);
lean_dec(v_res_2172_);
lean_dec(v_res_2169_);
lean_dec(v_res_2166_);
lean_dec(v_res_2155_);
v_pos_2210_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_pos_2210_);
v_err_2211_ = lean_ctor_get(v___x_2176_, 1);
lean_inc(v_err_2211_);
lean_dec_ref_known(v___x_2176_, 2);
v_pos_2137_ = v_pos_2210_;
v_err_2138_ = v_err_2211_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_pos_2212_; lean_object* v_err_2213_; 
lean_dec(v_res_2172_);
lean_dec(v_res_2169_);
lean_dec(v_res_2166_);
lean_dec_ref(v___x_2163_);
lean_dec(v_res_2155_);
v_pos_2212_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_pos_2212_);
v_err_2213_ = lean_ctor_get(v___x_2173_, 1);
lean_inc(v_err_2213_);
lean_dec_ref_known(v___x_2173_, 2);
v_pos_2137_ = v_pos_2212_;
v_err_2138_ = v_err_2213_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_pos_2214_; lean_object* v_err_2215_; 
lean_dec(v_res_2169_);
lean_dec(v_res_2166_);
lean_dec_ref(v___x_2163_);
lean_dec(v_res_2155_);
v_pos_2214_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_pos_2214_);
v_err_2215_ = lean_ctor_get(v___x_2170_, 1);
lean_inc(v_err_2215_);
lean_dec_ref_known(v___x_2170_, 2);
v_pos_2137_ = v_pos_2214_;
v_err_2138_ = v_err_2215_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_pos_2216_; lean_object* v_err_2217_; 
lean_dec(v_res_2166_);
lean_dec_ref(v___x_2163_);
lean_dec(v_res_2155_);
v_pos_2216_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_pos_2216_);
v_err_2217_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_err_2217_);
lean_dec_ref_known(v___x_2167_, 2);
v_pos_2137_ = v_pos_2216_;
v_err_2138_ = v_err_2217_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_pos_2218_; lean_object* v_err_2219_; 
lean_dec_ref(v___x_2163_);
lean_dec(v_res_2155_);
v_pos_2218_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_pos_2218_);
v_err_2219_ = lean_ctor_get(v___x_2164_, 1);
lean_inc(v_err_2219_);
lean_dec_ref_known(v___x_2164_, 2);
v_pos_2137_ = v_pos_2218_;
v_err_2138_ = v_err_2219_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_pos_2220_; lean_object* v_err_2221_; 
v_pos_2220_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_pos_2220_);
v_err_2221_ = lean_ctor_get(v___x_2154_, 1);
lean_inc(v_err_2221_);
lean_dec_ref_known(v___x_2154_, 2);
v_pos_2137_ = v_pos_2220_;
v_err_2138_ = v_err_2221_;
goto v___jp_2136_;
}
v___jp_2136_:
{
lean_object* v_idx_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2152_; 
v_idx_2139_ = lean_ctor_get(v_a_2135_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_a_2135_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v_a_2135_, 0);
lean_dec(v_unused_2153_);
v___x_2141_ = v_a_2135_;
v_isShared_2142_ = v_isSharedCheck_2152_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_idx_2139_);
lean_dec(v_a_2135_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2152_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_idx_2143_; uint8_t v___x_2144_; 
v_idx_2143_ = lean_ctor_get(v_pos_2137_, 1);
v___x_2144_ = lean_nat_dec_eq(v_idx_2139_, v_idx_2143_);
lean_dec(v_idx_2139_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2146_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set_tag(v___x_2141_, 1);
lean_ctor_set(v___x_2141_, 1, v_err_2138_);
lean_ctor_set(v___x_2141_, 0, v_pos_2137_);
v___x_2146_ = v___x_2141_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_pos_2137_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_err_2138_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec(v_err_2138_);
v___x_2148_ = lean_box(0);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v___x_2148_);
lean_ctor_set(v___x_2141_, 0, v_pos_2137_);
v___x_2150_ = v___x_2141_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_pos_2137_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_parse(lean_object* v_a_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(v_a_2222_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_pos_2224_; lean_object* v_res_2225_; lean_object* v___x_2226_; 
v_pos_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_pos_2224_);
v_res_2225_ = lean_ctor_get(v___x_2223_, 1);
lean_inc(v_res_2225_);
lean_dec_ref_known(v___x_2223_, 2);
v___x_2226_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(v_pos_2224_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_pos_2227_; lean_object* v_res_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2236_; 
v_pos_2227_ = lean_ctor_get(v___x_2226_, 0);
v_res_2228_ = lean_ctor_get(v___x_2226_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2230_ = v___x_2226_;
v_isShared_2231_ = v_isSharedCheck_2236_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_res_2228_);
lean_inc(v_pos_2227_);
lean_dec(v___x_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2236_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v_res_2225_);
lean_ctor_set(v___x_2232_, 1, v_res_2228_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v___x_2232_);
v___x_2234_ = v___x_2230_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_pos_2227_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
else
{
lean_object* v_pos_2237_; lean_object* v_err_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_res_2225_);
v_pos_2237_ = lean_ctor_get(v___x_2226_, 0);
v_err_2238_ = lean_ctor_get(v___x_2226_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2226_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_err_2238_);
lean_inc(v_pos_2237_);
lean_dec(v___x_2226_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_pos_2237_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_err_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_object* v_pos_2246_; lean_object* v_err_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_pos_2246_ = lean_ctor_get(v___x_2223_, 0);
v_err_2247_ = lean_ctor_get(v___x_2223_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2223_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_err_2247_);
lean_inc(v_pos_2246_);
lean_dec(v___x_2223_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_pos_2246_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_err_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
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
