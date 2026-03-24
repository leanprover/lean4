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
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
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
extern uint8_t l_instInhabitedUInt8;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint32_t lean_uint8_to_uint32(uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_uint8_of_nat(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_take(lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
extern uint32_t l_instInhabitedUInt32;
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1;
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedHeader_default;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedHeader;
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
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV1;
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
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZifV2;
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
static lean_once_cell_t l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZif_default;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instInhabitedTZif;
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
static lean_once_cell_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0;
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
lean_dec_ref(v_a_71_);
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
lean_inc(v_quotContext_77_);
v_currMacroScope_78_ = lean_ctor_get(v_a_71_, 2);
lean_inc(v_currMacroScope_78_);
v_ref_79_ = lean_ctor_get(v_a_71_, 5);
lean_inc(v_ref_79_);
lean_dec_ref(v_a_71_);
v___x_80_ = 0;
v___x_81_ = l_Lean_SourceInfo_fromRef(v_ref_79_, v___x_80_);
lean_dec(v_ref_79_);
v___x_82_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1);
v___x_83_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2));
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
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1(lean_object* v_x_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1));
lean_inc(v_x_91_);
v___x_95_ = l_Lean_Syntax_isOfKind(v_x_91_, v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_x_91_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_a_93_);
return v___x_97_;
}
else
{
lean_object* v_ref_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_ref_98_ = l_Lean_replaceRef(v_x_91_, v_a_92_);
lean_dec(v_x_91_);
v___x_99_ = 0;
v___x_100_ = l_Lean_SourceInfo_fromRef(v_ref_98_, v___x_99_);
lean_dec(v_ref_98_);
v___x_101_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20));
v___x_102_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21));
lean_inc(v___x_100_);
v___x_103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_100_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = l_Lean_Syntax_node1(v___x_100_, v___x_101_, v___x_103_);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_a_93_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___boxed(lean_object* v_x_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1(v_x_106_, v_a_107_, v_a_108_);
lean_dec(v_a_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1(lean_object* v_x_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1));
v___x_126_ = l_Lean_Syntax_isOfKind(v_x_122_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec_ref(v_a_123_);
v___x_127_ = lean_box(1);
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v_a_124_);
return v___x_128_;
}
else
{
lean_object* v_quotContext_129_; lean_object* v_currMacroScope_130_; lean_object* v_ref_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_quotContext_129_ = lean_ctor_get(v_a_123_, 1);
lean_inc(v_quotContext_129_);
v_currMacroScope_130_ = lean_ctor_get(v_a_123_, 2);
lean_inc(v_currMacroScope_130_);
v_ref_131_ = lean_ctor_get(v_a_123_, 5);
lean_inc(v_ref_131_);
lean_dec_ref(v_a_123_);
v___x_132_ = 0;
v___x_133_ = l_Lean_SourceInfo_fromRef(v_ref_131_, v___x_132_);
lean_dec(v_ref_131_);
v___x_134_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1);
v___x_135_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2));
v___x_136_ = l_Lean_addMacroScope(v_quotContext_129_, v___x_135_, v_currMacroScope_130_);
v___x_137_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6));
v___x_138_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_138_, 0, v___x_133_);
lean_ctor_set(v___x_138_, 1, v___x_134_);
lean_ctor_set(v___x_138_, 2, v___x_136_);
lean_ctor_set(v___x_138_, 3, v___x_137_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_a_124_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2(lean_object* v_x_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1));
lean_inc(v_x_140_);
v___x_144_ = l_Lean_Syntax_isOfKind(v_x_140_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_x_140_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v_a_142_);
return v___x_146_;
}
else
{
lean_object* v_ref_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_ref_147_ = l_Lean_replaceRef(v_x_140_, v_a_141_);
lean_dec(v_x_140_);
v___x_148_ = 0;
v___x_149_ = l_Lean_SourceInfo_fromRef(v_ref_147_, v___x_148_);
lean_dec(v_ref_147_);
v___x_150_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1));
v___x_151_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2));
lean_inc(v___x_149_);
v___x_152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_149_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Lean_Syntax_node1(v___x_149_, v___x_150_, v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_a_142_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2___boxed(lean_object* v_x_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2(v_x_155_, v_a_156_, v_a_157_);
lean_dec(v_a_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_TZif_instReprHeader_repr_spec__0(lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_nat_to_int(v_a_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(11u);
v___x_175_ = lean_nat_to_int(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(12u);
v___x_186_ = lean_nat_to_int(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0));
v___x_201_ = lean_string_length(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24);
v___x_203_ = lean_nat_to_int(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(lean_object* v_x_208_){
_start:
{
uint8_t v_version_209_; uint32_t v_isutcnt_210_; uint32_t v_isstdcnt_211_; uint32_t v_leapcnt_212_; uint32_t v_timecnt_213_; uint32_t v_typecnt_214_; uint32_t v_charcnt_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_version_209_ = lean_ctor_get_uint8(v_x_208_, 24);
v_isutcnt_210_ = lean_ctor_get_uint32(v_x_208_, 0);
v_isstdcnt_211_ = lean_ctor_get_uint32(v_x_208_, 4);
v_leapcnt_212_ = lean_ctor_get_uint32(v_x_208_, 8);
v_timecnt_213_ = lean_ctor_get_uint32(v_x_208_, 12);
v_typecnt_214_ = lean_ctor_get_uint32(v_x_208_, 16);
v_charcnt_215_ = lean_ctor_get_uint32(v_x_208_, 20);
v___x_216_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_217_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6));
v___x_218_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7);
v___x_219_ = lean_uint8_to_nat(v_version_209_);
v___x_220_ = l_Nat_reprFast(v___x_219_);
v___x_221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
v___x_222_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_218_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = 0;
v___x_224_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_223_);
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_217_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_box(1);
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11));
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_216_);
v___x_233_ = lean_uint32_to_nat(v_isutcnt_210_);
v___x_234_ = l_Nat_reprFast(v___x_233_);
v___x_235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_218_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_223_);
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_232_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_226_);
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_228_);
v___x_241_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13));
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_216_);
v___x_244_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14);
v___x_245_ = lean_uint32_to_nat(v_isstdcnt_211_);
v___x_246_ = l_Nat_reprFast(v___x_245_);
v___x_247_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
v___x_248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_244_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set_uint8(v___x_249_, sizeof(void*)*1, v___x_223_);
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_243_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_226_);
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_228_);
v___x_253_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16));
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_216_);
v___x_256_ = lean_uint32_to_nat(v_leapcnt_212_);
v___x_257_ = l_Nat_reprFast(v___x_256_);
v___x_258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
v___x_259_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_218_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*1, v___x_223_);
v___x_261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_255_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_226_);
v___x_263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_228_);
v___x_264_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18));
v___x_265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_216_);
v___x_267_ = lean_uint32_to_nat(v_timecnt_213_);
v___x_268_ = l_Nat_reprFast(v___x_267_);
v___x_269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_218_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*1, v___x_223_);
v___x_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_266_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_226_);
v___x_274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_228_);
v___x_275_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20));
v___x_276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_216_);
v___x_278_ = lean_uint32_to_nat(v_typecnt_214_);
v___x_279_ = l_Nat_reprFast(v___x_278_);
v___x_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
v___x_281_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_218_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*1, v___x_223_);
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_277_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_226_);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_228_);
v___x_286_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22));
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_216_);
v___x_289_ = lean_uint32_to_nat(v_charcnt_215_);
v___x_290_ = l_Nat_reprFast(v___x_289_);
v___x_291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_218_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*1, v___x_223_);
v___x_294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_288_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_296_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_294_);
v___x_298_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_295_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*1, v___x_223_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___boxed(lean_object* v_x_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_x_302_);
lean_dec_ref(v_x_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr(lean_object* v_x_304_, lean_object* v_prec_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_x_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprHeader_repr___boxed(lean_object* v_x_307_, lean_object* v_prec_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr(v_x_307_, v_prec_308_);
lean_dec(v_prec_308_);
lean_dec_ref(v_x_307_);
return v_res_309_;
}
}
static uint8_t _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0(void){
_start:
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_uint8_of_nat(v___x_312_);
return v___x_313_;
}
}
static uint32_t _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1(void){
_start:
{
lean_object* v___x_314_; uint32_t v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_uint32_of_nat(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2(void){
_start:
{
uint32_t v___x_316_; uint8_t v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_uint32_once(&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1, &l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1);
v___x_317_ = lean_uint8_once(&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0);
v___x_318_ = lean_alloc_ctor(0, 0, 25);
lean_ctor_set_uint8(v___x_318_, 24, v___x_317_);
lean_ctor_set_uint32(v___x_318_, 0, v___x_316_);
lean_ctor_set_uint32(v___x_318_, 4, v___x_316_);
lean_ctor_set_uint32(v___x_318_, 8, v___x_316_);
lean_ctor_set_uint32(v___x_318_, 12, v___x_316_);
lean_ctor_set_uint32(v___x_318_, 16, v___x_316_);
lean_ctor_set_uint32(v___x_318_, 20, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2, &l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Std_Time_TimeZone_TZif_instInhabitedHeader_default;
return v___x_320_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(13u);
v___x_331_ = lean_nat_to_int(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(9u);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(21u);
v___x_341_ = lean_nat_to_int(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_nat_to_int(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(lean_object* v_x_344_){
_start:
{
lean_object* v_gmtOffset_345_; uint8_t v_isDst_346_; uint8_t v_abbreviationIndex_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___y_352_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_gmtOffset_345_ = lean_ctor_get(v_x_344_, 0);
v_isDst_346_ = lean_ctor_get_uint8(v_x_344_, sizeof(void*)*1);
v_abbreviationIndex_347_ = lean_ctor_get_uint8(v_x_344_, sizeof(void*)*1 + 1);
v___x_348_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_349_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3));
v___x_350_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4);
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_390_ = lean_int_dec_lt(v_gmtOffset_345_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = l_Int_repr(v_gmtOffset_345_);
v___x_392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
v___y_352_ = v___x_392_;
goto v___jp_351_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = l_Int_repr(v_gmtOffset_345_);
v___x_394_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
v___x_395_ = l_Repr_addAppParen(v___x_394_, v___x_388_);
v___y_352_ = v___x_395_;
goto v___jp_351_;
}
v___jp_351_:
{
lean_object* v___x_353_; uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_353_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_350_);
lean_ctor_set(v___x_353_, 1, v___y_352_);
v___x_354_ = 0;
v___x_355_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1, v___x_354_);
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_349_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = lean_box(1);
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6));
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_348_);
v___x_364_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7);
v___x_365_ = l_Bool_repr___redArg(v_isDst_346_);
v___x_366_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_354_);
v___x_368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_363_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_357_);
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_359_);
v___x_371_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9));
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_348_);
v___x_374_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10);
v___x_375_ = lean_uint8_to_nat(v_abbreviationIndex_347_);
v___x_376_ = l_Nat_reprFast(v___x_375_);
v___x_377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
v___x_378_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_374_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*1, v___x_354_);
v___x_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_373_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_382_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_380_);
v___x_384_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_381_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*1, v___x_354_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___boxed(lean_object* v_x_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_x_396_);
lean_dec_ref(v_x_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(lean_object* v_x_398_, lean_object* v_prec_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_x_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___boxed(lean_object* v_x_401_, lean_object* v_prec_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(v_x_401_, v_prec_402_);
lean_dec(v_prec_402_);
lean_dec_ref(v_x_401_);
return v_res_403_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0(void){
_start:
{
uint8_t v___x_406_; uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_uint8_once(&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0);
v___x_407_ = 0;
v___x_408_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_409_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*1, v___x_407_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*1 + 1, v___x_406_);
return v___x_409_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default(void){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0);
return v___x_410_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType(void){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default;
return v___x_411_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(18u);
v___x_422_ = lean_nat_to_int(v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(14u);
v___x_427_ = lean_nat_to_int(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(lean_object* v_x_428_){
_start:
{
lean_object* v_transitionTime_429_; lean_object* v_correction_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_484_; 
v_transitionTime_429_ = lean_ctor_get(v_x_428_, 0);
v_correction_430_ = lean_ctor_get(v_x_428_, 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_484_ == 0)
{
v___x_432_ = v_x_428_;
v_isShared_433_ = v_isSharedCheck_484_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_correction_430_);
lean_inc(v_transitionTime_429_);
lean_dec(v_x_428_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_484_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___y_455_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_451_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_452_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3));
v___x_453_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_478_ = lean_int_dec_lt(v_transitionTime_429_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = l_Int_repr(v_transitionTime_429_);
lean_dec(v_transitionTime_429_);
v___x_480_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
v___y_455_ = v___x_480_;
goto v___jp_454_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = l_Int_repr(v_transitionTime_429_);
lean_dec(v_transitionTime_429_);
v___x_482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___x_483_ = l_Repr_addAppParen(v___x_482_, v___x_476_);
v___y_455_ = v___x_483_;
goto v___jp_454_;
}
v___jp_434_:
{
lean_object* v___x_440_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set_tag(v___x_432_, 4);
lean_ctor_set(v___x_432_, 1, v___y_438_);
lean_ctor_set(v___x_432_, 0, v___y_437_);
v___x_440_ = v___x_432_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___y_437_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v___y_438_);
v___x_440_ = v_reuseFailAlloc_450_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_441_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*1, v___y_436_);
v___x_442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_442_, 0, v___y_435_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_444_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_442_);
v___x_446_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_443_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*1, v___y_436_);
return v___x_449_;
}
}
v___jp_454_:
{
lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_453_);
lean_ctor_set(v___x_456_, 1, v___y_455_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_457_);
v___x_459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_452_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_box(1);
v___x_463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6));
v___x_465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_451_);
v___x_467_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_470_ = lean_int_dec_lt(v_correction_430_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = l_Int_repr(v_correction_430_);
lean_dec(v_correction_430_);
v___x_472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
v___y_435_ = v___x_466_;
v___y_436_ = v___x_457_;
v___y_437_ = v___x_467_;
v___y_438_ = v___x_472_;
goto v___jp_434_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = l_Int_repr(v_correction_430_);
lean_dec(v_correction_430_);
v___x_474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
v___x_475_ = l_Repr_addAppParen(v___x_474_, v___x_468_);
v___y_435_ = v___x_466_;
v___y_436_ = v___x_457_;
v___y_437_ = v___x_467_;
v___y_438_ = v___x_475_;
goto v___jp_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr(lean_object* v_x_485_, lean_object* v_prec_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_x_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___boxed(lean_object* v_x_488_, lean_object* v_prec_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr(v_x_488_, v_prec_489_);
lean_dec(v_prec_489_);
return v_res_490_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default(void){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0);
return v___x_495_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default;
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_499_) == 0)
{
lean_dec(v_x_497_);
return v_x_498_;
}
else
{
lean_object* v_head_500_; lean_object* v_tail_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_512_; 
v_head_500_ = lean_ctor_get(v_x_499_, 0);
v_tail_501_ = lean_ctor_get(v_x_499_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_499_);
if (v_isSharedCheck_512_ == 0)
{
v___x_503_ = v_x_499_;
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_tail_501_);
lean_inc(v_head_500_);
lean_dec(v_x_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
lean_inc(v_x_497_);
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 5);
lean_ctor_set(v___x_503_, 1, v_x_497_);
lean_ctor_set(v___x_503_, 0, v_x_498_);
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_x_498_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_x_497_);
v___x_506_ = v_reuseFailAlloc_511_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_unbox(v_head_500_);
lean_dec(v_head_500_);
v___x_508_ = l_Bool_repr___redArg(v___x_507_);
v___x_509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_506_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v_x_498_ = v___x_509_;
v_x_499_ = v_tail_501_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16(lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
if (lean_obj_tag(v_x_515_) == 0)
{
lean_dec(v_x_513_);
return v_x_514_;
}
else
{
lean_object* v_head_516_; lean_object* v_tail_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_528_; 
v_head_516_ = lean_ctor_get(v_x_515_, 0);
v_tail_517_ = lean_ctor_get(v_x_515_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_528_ == 0)
{
v___x_519_ = v_x_515_;
v_isShared_520_ = v_isSharedCheck_528_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_tail_517_);
lean_inc(v_head_516_);
lean_dec(v_x_515_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_528_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
lean_inc(v_x_513_);
if (v_isShared_520_ == 0)
{
lean_ctor_set_tag(v___x_519_, 5);
lean_ctor_set(v___x_519_, 1, v_x_513_);
lean_ctor_set(v___x_519_, 0, v_x_514_);
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_x_514_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_x_513_);
v___x_522_ = v_reuseFailAlloc_527_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_523_ = lean_unbox(v_head_516_);
lean_dec(v_head_516_);
v___x_524_ = l_Bool_repr___redArg(v___x_523_);
v___x_525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_522_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(v_x_513_, v___x_525_, v_tail_517_);
return v___x_526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
lean_object* v___x_531_; 
lean_dec(v_x_530_);
v___x_531_ = lean_box(0);
return v___x_531_;
}
else
{
lean_object* v_tail_532_; 
v_tail_532_ = lean_ctor_get(v_x_529_, 1);
if (lean_obj_tag(v_tail_532_) == 0)
{
lean_object* v_head_533_; uint8_t v___x_534_; lean_object* v___x_535_; 
lean_dec(v_x_530_);
v_head_533_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_head_533_);
lean_dec_ref(v_x_529_);
v___x_534_ = lean_unbox(v_head_533_);
lean_dec(v_head_533_);
v___x_535_ = l_Bool_repr___redArg(v___x_534_);
return v___x_535_;
}
else
{
lean_object* v_head_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_inc(v_tail_532_);
v_head_536_ = lean_ctor_get(v_x_529_, 0);
lean_inc(v_head_536_);
lean_dec_ref(v_x_529_);
v___x_537_ = lean_unbox(v_head_536_);
lean_dec(v_head_536_);
v___x_538_ = l_Bool_repr___redArg(v___x_537_);
v___x_539_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16(v_x_530_, v___x_538_, v_tail_532_);
return v___x_539_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0));
v___x_546_ = lean_string_length(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3);
v___x_548_ = lean_nat_to_int(v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(lean_object* v_xs_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_array_get_size(v_xs_556_);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_nat_dec_eq(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_560_ = lean_array_to_list(v_xs_556_);
v___x_561_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_562_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(v___x_560_, v___x_561_);
v___x_563_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_564_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_562_);
v___x_566_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_563_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = l_Std_Format_fill(v___x_568_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; 
lean_dec_ref(v_xs_556_);
v___x_570_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(lean_object* v___y_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = l_String_quote(v___y_571_);
v___x_573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
lean_dec(v_x_574_);
return v_x_575_;
}
else
{
lean_object* v_head_577_; lean_object* v_tail_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_589_; 
v_head_577_ = lean_ctor_get(v_x_576_, 0);
v_tail_578_ = lean_ctor_get(v_x_576_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_x_576_);
if (v_isSharedCheck_589_ == 0)
{
v___x_580_ = v_x_576_;
v_isShared_581_ = v_isSharedCheck_589_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_tail_578_);
lean_inc(v_head_577_);
lean_dec(v_x_576_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_589_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
lean_inc(v_x_574_);
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 5);
lean_ctor_set(v___x_580_, 1, v_x_574_);
lean_ctor_set(v___x_580_, 0, v_x_575_);
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_x_575_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_x_574_);
v___x_583_ = v_reuseFailAlloc_588_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = l_String_quote(v_head_577_);
v___x_585_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
v___x_586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_583_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v_x_575_ = v___x_586_;
v_x_576_ = v_tail_578_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10(lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_dec(v_x_590_);
return v_x_591_;
}
else
{
lean_object* v_head_593_; lean_object* v_tail_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_605_; 
v_head_593_ = lean_ctor_get(v_x_592_, 0);
v_tail_594_ = lean_ctor_get(v_x_592_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_605_ == 0)
{
v___x_596_ = v_x_592_;
v_isShared_597_ = v_isSharedCheck_605_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_tail_594_);
lean_inc(v_head_593_);
lean_dec(v_x_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_605_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
lean_inc(v_x_590_);
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 5);
lean_ctor_set(v___x_596_, 1, v_x_590_);
lean_ctor_set(v___x_596_, 0, v_x_591_);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_x_591_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_x_590_);
v___x_599_ = v_reuseFailAlloc_604_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_600_ = l_String_quote(v_head_593_);
v___x_601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_599_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(v_x_590_, v___x_602_, v_tail_594_);
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(lean_object* v_x_606_, lean_object* v_x_607_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_object* v___x_608_; 
lean_dec(v_x_607_);
v___x_608_ = lean_box(0);
return v___x_608_;
}
else
{
lean_object* v_tail_609_; 
v_tail_609_ = lean_ctor_get(v_x_606_, 1);
if (lean_obj_tag(v_tail_609_) == 0)
{
lean_object* v_head_610_; lean_object* v___x_611_; 
lean_dec(v_x_607_);
v_head_610_ = lean_ctor_get(v_x_606_, 0);
lean_inc(v_head_610_);
lean_dec_ref(v_x_606_);
v___x_611_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(v_head_610_);
return v___x_611_;
}
else
{
lean_object* v_head_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_inc(v_tail_609_);
v_head_612_ = lean_ctor_get(v_x_606_, 0);
lean_inc(v_head_612_);
lean_dec_ref(v_x_606_);
v___x_613_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(v_head_612_);
v___x_614_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10(v_x_607_, v___x_613_, v_tail_609_);
return v___x_614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(lean_object* v_xs_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = lean_array_get_size(v_xs_615_);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = lean_nat_dec_eq(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_619_ = lean_array_to_list(v_xs_615_);
v___x_620_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_621_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(v___x_619_, v___x_620_);
v___x_622_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_623_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v___x_621_);
v___x_625_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_622_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = l_Std_Format_fill(v___x_627_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; 
lean_dec_ref(v_xs_615_);
v___x_629_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_dec(v_x_630_);
return v_x_631_;
}
else
{
lean_object* v_head_633_; lean_object* v_tail_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_647_; 
v_head_633_ = lean_ctor_get(v_x_632_, 0);
v_tail_634_ = lean_ctor_get(v_x_632_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_647_ == 0)
{
v___x_636_ = v_x_632_;
v_isShared_637_ = v_isSharedCheck_647_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_tail_634_);
lean_inc(v_head_633_);
lean_dec(v_x_632_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_647_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
lean_inc(v_x_630_);
if (v_isShared_637_ == 0)
{
lean_ctor_set_tag(v___x_636_, 5);
lean_ctor_set(v___x_636_, 1, v_x_630_);
lean_ctor_set(v___x_636_, 0, v_x_631_);
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_x_631_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_x_630_);
v___x_639_ = v_reuseFailAlloc_646_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_640_ = lean_unbox(v_head_633_);
lean_dec(v_head_633_);
v___x_641_ = lean_uint8_to_nat(v___x_640_);
v___x_642_ = l_Nat_reprFast(v___x_641_);
v___x_643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
v___x_644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_639_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v_x_631_ = v___x_644_;
v_x_632_ = v_tail_634_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
lean_dec(v_x_648_);
return v_x_649_;
}
else
{
lean_object* v_head_651_; lean_object* v_tail_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_665_; 
v_head_651_ = lean_ctor_get(v_x_650_, 0);
v_tail_652_ = lean_ctor_get(v_x_650_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_665_ == 0)
{
v___x_654_ = v_x_650_;
v_isShared_655_ = v_isSharedCheck_665_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_tail_652_);
lean_inc(v_head_651_);
lean_dec(v_x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_665_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
lean_inc(v_x_648_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 5);
lean_ctor_set(v___x_654_, 1, v_x_648_);
lean_ctor_set(v___x_654_, 0, v_x_649_);
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_x_649_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_x_648_);
v___x_657_ = v_reuseFailAlloc_664_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_658_ = lean_unbox(v_head_651_);
lean_dec(v_head_651_);
v___x_659_ = lean_uint8_to_nat(v___x_658_);
v___x_660_ = l_Nat_reprFast(v___x_659_);
v___x_661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_657_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(v_x_648_, v___x_662_, v_tail_652_);
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(uint8_t v___y_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_uint8_to_nat(v___y_666_);
v___x_668_ = l_Nat_reprFast(v___x_667_);
v___x_669_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0___boxed(lean_object* v___y_670_){
_start:
{
uint8_t v___y_1967__boxed_671_; lean_object* v_res_672_; 
v___y_1967__boxed_671_ = lean_unbox(v___y_670_);
v_res_672_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___y_1967__boxed_671_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
if (lean_obj_tag(v_x_673_) == 0)
{
lean_object* v___x_675_; 
lean_dec(v_x_674_);
v___x_675_ = lean_box(0);
return v___x_675_;
}
else
{
lean_object* v_tail_676_; 
v_tail_676_ = lean_ctor_get(v_x_673_, 1);
if (lean_obj_tag(v_tail_676_) == 0)
{
lean_object* v_head_677_; uint8_t v___x_678_; lean_object* v___x_679_; 
lean_dec(v_x_674_);
v_head_677_ = lean_ctor_get(v_x_673_, 0);
lean_inc(v_head_677_);
lean_dec_ref(v_x_673_);
v___x_678_ = lean_unbox(v_head_677_);
lean_dec(v_head_677_);
v___x_679_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_678_);
return v___x_679_;
}
else
{
lean_object* v_head_680_; uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_inc(v_tail_676_);
v_head_680_ = lean_ctor_get(v_x_673_, 0);
lean_inc(v_head_680_);
lean_dec_ref(v_x_673_);
v___x_681_ = lean_unbox(v_head_680_);
lean_dec(v_head_680_);
v___x_682_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_681_);
v___x_683_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(v_x_674_, v___x_682_, v_tail_676_);
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(lean_object* v_xs_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_685_ = lean_array_get_size(v_xs_684_);
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_nat_dec_eq(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_688_ = lean_array_to_list(v_xs_684_);
v___x_689_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_690_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(v___x_688_, v___x_689_);
v___x_691_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_692_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___x_690_);
v___x_694_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_691_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Std_Format_fill(v___x_696_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; 
lean_dec_ref(v_xs_684_);
v___x_698_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
if (lean_obj_tag(v_x_701_) == 0)
{
lean_dec(v_x_699_);
return v_x_700_;
}
else
{
lean_object* v_head_702_; lean_object* v_tail_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_722_; 
v_head_702_ = lean_ctor_get(v_x_701_, 0);
v_tail_703_ = lean_ctor_get(v_x_701_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_701_);
if (v_isSharedCheck_722_ == 0)
{
v___x_705_ = v_x_701_;
v_isShared_706_ = v_isSharedCheck_722_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_tail_703_);
lean_inc(v_head_702_);
lean_dec(v_x_701_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_722_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
lean_inc(v_x_699_);
if (v_isShared_706_ == 0)
{
lean_ctor_set_tag(v___x_705_, 5);
lean_ctor_set(v___x_705_, 1, v_x_699_);
lean_ctor_set(v___x_705_, 0, v_x_700_);
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_x_700_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_x_699_);
v___x_708_ = v_reuseFailAlloc_721_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_711_ = lean_int_dec_lt(v_head_702_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = l_Int_repr(v_head_702_);
lean_dec(v_head_702_);
v___x_713_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
v___x_714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_708_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v_x_700_ = v___x_714_;
v_x_701_ = v_tail_703_;
goto _start;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = l_Int_repr(v_head_702_);
lean_dec(v_head_702_);
v___x_717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
v___x_718_ = l_Repr_addAppParen(v___x_717_, v___x_709_);
v___x_719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_708_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v_x_700_ = v___x_719_;
v_x_701_ = v_tail_703_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_){
_start:
{
if (lean_obj_tag(v_x_725_) == 0)
{
lean_dec(v_x_723_);
return v_x_724_;
}
else
{
lean_object* v_head_726_; lean_object* v_tail_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_746_; 
v_head_726_ = lean_ctor_get(v_x_725_, 0);
v_tail_727_ = lean_ctor_get(v_x_725_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_725_);
if (v_isSharedCheck_746_ == 0)
{
v___x_729_ = v_x_725_;
v_isShared_730_ = v_isSharedCheck_746_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_tail_727_);
lean_inc(v_head_726_);
lean_dec(v_x_725_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_746_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
lean_inc(v_x_723_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 5);
lean_ctor_set(v___x_729_, 1, v_x_723_);
lean_ctor_set(v___x_729_, 0, v_x_724_);
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_x_724_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_x_723_);
v___x_732_ = v_reuseFailAlloc_745_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_735_ = lean_int_dec_lt(v_head_726_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_736_ = l_Int_repr(v_head_726_);
lean_dec(v_head_726_);
v___x_737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
v___x_738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_732_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_723_, v___x_738_, v_tail_727_);
return v___x_739_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_740_ = l_Int_repr(v_head_726_);
lean_dec(v_head_726_);
v___x_741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
v___x_742_ = l_Repr_addAppParen(v___x_741_, v___x_733_);
v___x_743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_732_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_723_, v___x_743_, v_tail_727_);
return v___x_744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(lean_object* v___y_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_750_ = lean_int_dec_lt(v___y_747_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = l_Int_repr(v___y_747_);
v___x_752_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = l_Int_repr(v___y_747_);
v___x_754_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
v___x_755_ = l_Repr_addAppParen(v___x_754_, v___x_748_);
return v___x_755_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0___boxed(lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v___y_756_);
lean_dec(v___y_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
lean_object* v___x_760_; 
lean_dec(v_x_759_);
v___x_760_ = lean_box(0);
return v___x_760_;
}
else
{
lean_object* v_tail_761_; 
v_tail_761_ = lean_ctor_get(v_x_758_, 1);
if (lean_obj_tag(v_tail_761_) == 0)
{
lean_object* v_head_762_; lean_object* v___x_763_; 
lean_dec(v_x_759_);
v_head_762_ = lean_ctor_get(v_x_758_, 0);
lean_inc(v_head_762_);
lean_dec_ref(v_x_758_);
v___x_763_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_762_);
lean_dec(v_head_762_);
return v___x_763_;
}
else
{
lean_object* v_head_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_inc(v_tail_761_);
v_head_764_ = lean_ctor_get(v_x_758_, 0);
lean_inc(v_head_764_);
lean_dec_ref(v_x_758_);
v___x_765_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_764_);
lean_dec(v_head_764_);
v___x_766_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(v_x_759_, v___x_765_, v_tail_761_);
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(lean_object* v_xs_767_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_array_get_size(v_xs_767_);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_nat_dec_eq(v___x_768_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_771_ = lean_array_to_list(v_xs_767_);
v___x_772_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_773_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(v___x_771_, v___x_772_);
v___x_774_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_775_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_773_);
v___x_777_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_774_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l_Std_Format_fill(v___x_779_);
return v___x_780_;
}
else
{
lean_object* v___x_781_; 
lean_dec_ref(v_xs_767_);
v___x_781_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_dec(v_x_782_);
return v_x_783_;
}
else
{
lean_object* v_head_785_; lean_object* v_tail_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_796_; 
v_head_785_ = lean_ctor_get(v_x_784_, 0);
v_tail_786_ = lean_ctor_get(v_x_784_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_796_ == 0)
{
v___x_788_ = v_x_784_;
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_tail_786_);
lean_inc(v_head_785_);
lean_dec(v_x_784_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
lean_inc(v_x_782_);
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 5);
lean_ctor_set(v___x_788_, 1, v_x_782_);
lean_ctor_set(v___x_788_, 0, v_x_783_);
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_x_783_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_x_782_);
v___x_791_ = v_reuseFailAlloc_795_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_785_);
lean_dec(v_head_785_);
v___x_793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v_x_783_ = v___x_793_;
v_x_784_ = v_tail_786_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_799_) == 0)
{
lean_dec(v_x_797_);
return v_x_798_;
}
else
{
lean_object* v_head_800_; lean_object* v_tail_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_811_; 
v_head_800_ = lean_ctor_get(v_x_799_, 0);
v_tail_801_ = lean_ctor_get(v_x_799_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_811_ == 0)
{
v___x_803_ = v_x_799_;
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_tail_801_);
lean_inc(v_head_800_);
lean_dec(v_x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
lean_inc(v_x_797_);
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 5);
lean_ctor_set(v___x_803_, 1, v_x_797_);
lean_ctor_set(v___x_803_, 0, v_x_798_);
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_x_798_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_x_797_);
v___x_806_ = v_reuseFailAlloc_810_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_800_);
lean_dec(v_head_800_);
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(v_x_797_, v___x_808_, v_tail_801_);
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
if (lean_obj_tag(v_x_812_) == 0)
{
lean_object* v___x_814_; 
lean_dec(v_x_813_);
v___x_814_ = lean_box(0);
return v___x_814_;
}
else
{
lean_object* v_tail_815_; 
v_tail_815_ = lean_ctor_get(v_x_812_, 1);
if (lean_obj_tag(v_tail_815_) == 0)
{
lean_object* v_head_816_; lean_object* v___x_817_; 
lean_dec(v_x_813_);
v_head_816_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_head_816_);
lean_dec_ref(v_x_812_);
v___x_817_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_816_);
lean_dec(v_head_816_);
return v___x_817_;
}
else
{
lean_object* v_head_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_inc(v_tail_815_);
v_head_818_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_head_818_);
lean_dec_ref(v_x_812_);
v___x_819_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_818_);
lean_dec(v_head_818_);
v___x_820_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(v_x_813_, v___x_819_, v_tail_815_);
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(lean_object* v_xs_821_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_822_ = lean_array_get_size(v_xs_821_);
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_nat_dec_eq(v___x_822_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_825_ = lean_array_to_list(v_xs_821_);
v___x_826_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_827_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(v___x_825_, v___x_826_);
v___x_828_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_829_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___x_827_);
v___x_831_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_828_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Std_Format_fill(v___x_833_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; 
lean_dec_ref(v_xs_821_);
v___x_835_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
if (lean_obj_tag(v_x_838_) == 0)
{
lean_dec(v_x_836_);
return v_x_837_;
}
else
{
lean_object* v_head_839_; lean_object* v_tail_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_850_; 
v_head_839_ = lean_ctor_get(v_x_838_, 0);
v_tail_840_ = lean_ctor_get(v_x_838_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_x_838_);
if (v_isSharedCheck_850_ == 0)
{
v___x_842_ = v_x_838_;
v_isShared_843_ = v_isSharedCheck_850_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_tail_840_);
lean_inc(v_head_839_);
lean_dec(v_x_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_850_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
lean_inc(v_x_836_);
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 5);
lean_ctor_set(v___x_842_, 1, v_x_836_);
lean_ctor_set(v___x_842_, 0, v_x_837_);
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_x_837_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_x_836_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_839_);
v___x_847_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v_x_837_ = v___x_847_;
v_x_838_ = v_tail_840_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_x_853_) == 0)
{
lean_dec(v_x_851_);
return v_x_852_;
}
else
{
lean_object* v_head_854_; lean_object* v_tail_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_865_; 
v_head_854_ = lean_ctor_get(v_x_853_, 0);
v_tail_855_ = lean_ctor_get(v_x_853_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_x_853_);
if (v_isSharedCheck_865_ == 0)
{
v___x_857_ = v_x_853_;
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_tail_855_);
lean_inc(v_head_854_);
lean_dec(v_x_853_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
lean_inc(v_x_851_);
if (v_isShared_858_ == 0)
{
lean_ctor_set_tag(v___x_857_, 5);
lean_ctor_set(v___x_857_, 1, v_x_851_);
lean_ctor_set(v___x_857_, 0, v_x_852_);
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_x_852_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_x_851_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_854_);
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(v_x_851_, v___x_862_, v_tail_855_);
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
lean_object* v___x_868_; 
lean_dec(v_x_867_);
v___x_868_ = lean_box(0);
return v___x_868_;
}
else
{
lean_object* v_tail_869_; 
v_tail_869_ = lean_ctor_get(v_x_866_, 1);
if (lean_obj_tag(v_tail_869_) == 0)
{
lean_object* v_head_870_; lean_object* v___x_871_; 
lean_dec(v_x_867_);
v_head_870_ = lean_ctor_get(v_x_866_, 0);
lean_inc(v_head_870_);
lean_dec_ref(v_x_866_);
v___x_871_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_870_);
return v___x_871_;
}
else
{
lean_object* v_head_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_inc(v_tail_869_);
v_head_872_ = lean_ctor_get(v_x_866_, 0);
lean_inc(v_head_872_);
lean_dec_ref(v_x_866_);
v___x_873_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_872_);
v___x_874_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(v_x_867_, v___x_873_, v_tail_869_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(lean_object* v_xs_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_876_ = lean_array_get_size(v_xs_875_);
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_nat_dec_eq(v___x_876_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_879_ = lean_array_to_list(v_xs_875_);
v___x_880_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_881_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(v___x_879_, v___x_880_);
v___x_882_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_883_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_881_);
v___x_885_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_882_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Std_Format_fill(v___x_887_);
return v___x_888_;
}
else
{
lean_object* v___x_889_; 
lean_dec_ref(v_xs_875_);
v___x_889_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_889_;
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_unsigned_to_nat(10u);
v___x_900_ = lean_nat_to_int(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(19u);
v___x_905_ = lean_nat_to_int(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_unsigned_to_nat(17u);
v___x_916_ = lean_nat_to_int(v___x_915_);
return v___x_916_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(15u);
v___x_921_ = lean_nat_to_int(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(lean_object* v_x_928_){
_start:
{
lean_object* v_header_929_; lean_object* v_transitionTimes_930_; lean_object* v_transitionIndices_931_; lean_object* v_localTimeTypes_932_; lean_object* v_abbreviations_933_; lean_object* v_leapSeconds_934_; lean_object* v_stdWallIndicators_935_; lean_object* v_utLocalIndicators_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_header_929_ = lean_ctor_get(v_x_928_, 0);
lean_inc_ref(v_header_929_);
v_transitionTimes_930_ = lean_ctor_get(v_x_928_, 1);
lean_inc_ref(v_transitionTimes_930_);
v_transitionIndices_931_ = lean_ctor_get(v_x_928_, 2);
lean_inc_ref(v_transitionIndices_931_);
v_localTimeTypes_932_ = lean_ctor_get(v_x_928_, 3);
lean_inc_ref(v_localTimeTypes_932_);
v_abbreviations_933_ = lean_ctor_get(v_x_928_, 4);
lean_inc_ref(v_abbreviations_933_);
v_leapSeconds_934_ = lean_ctor_get(v_x_928_, 5);
lean_inc_ref(v_leapSeconds_934_);
v_stdWallIndicators_935_ = lean_ctor_get(v_x_928_, 6);
lean_inc_ref(v_stdWallIndicators_935_);
v_utLocalIndicators_936_ = lean_ctor_get(v_x_928_, 7);
lean_inc_ref(v_utLocalIndicators_936_);
lean_dec_ref(v_x_928_);
v___x_937_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_938_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3));
v___x_939_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4);
v___x_940_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_header_929_);
lean_dec_ref(v_header_929_);
v___x_941_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = 0;
v___x_943_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*1, v___x_942_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_938_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_box(1);
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6));
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_937_);
v___x_952_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7);
v___x_953_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(v_transitionTimes_930_);
v___x_954_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*1, v___x_942_);
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_951_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_945_);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___x_947_);
v___x_959_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9));
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_937_);
v___x_962_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10);
v___x_963_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(v_transitionIndices_931_);
v___x_964_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*1, v___x_942_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_961_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_945_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_947_);
v___x_969_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11));
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___x_937_);
v___x_972_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4);
v___x_973_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(v_localTimeTypes_932_);
v___x_974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*1, v___x_942_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_971_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_945_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_947_);
v___x_979_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13));
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_937_);
v___x_982_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14);
v___x_983_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(v_abbreviations_933_);
v___x_984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*1, v___x_942_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_981_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_945_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_947_);
v___x_989_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16));
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_937_);
v___x_992_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17);
v___x_993_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(v_leapSeconds_934_);
v___x_994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v___x_942_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_991_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_945_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_947_);
v___x_999_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19));
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_937_);
v___x_1002_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(v_stdWallIndicators_935_);
v___x_1003_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_962_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set_uint8(v___x_1004_, sizeof(void*)*1, v___x_942_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1001_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_945_);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_947_);
v___x_1008_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21));
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_937_);
v___x_1011_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(v_utLocalIndicators_936_);
v___x_1012_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_962_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*1, v___x_942_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1010_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1016_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_1014_);
v___x_1018_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1015_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set_uint8(v___x_1021_, sizeof(void*)*1, v___x_942_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(lean_object* v_x_1022_, lean_object* v_prec_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_x_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___boxed(lean_object* v_x_1025_, lean_object* v_prec_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(v_x_1025_, v_prec_1026_);
lean_dec(v_prec_1026_);
return v_res_1027_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0));
v___x_1033_ = l_Std_Time_TimeZone_TZif_instInhabitedHeader_default;
v___x_1034_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_1032_);
lean_ctor_set(v___x_1034_, 2, v___x_1032_);
lean_ctor_set(v___x_1034_, 3, v___x_1032_);
lean_ctor_set(v___x_1034_, 4, v___x_1032_);
lean_ctor_set(v___x_1034_, 5, v___x_1032_);
lean_ctor_set(v___x_1034_, 6, v___x_1032_);
lean_ctor_set(v___x_1034_, 7, v___x_1032_);
return v___x_1034_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default(void){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1, &l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1);
return v___x_1035_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1(void){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
if (lean_obj_tag(v_x_1043_) == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1));
return v___x_1045_;
}
else
{
lean_object* v_val_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1057_; 
v_val_1046_ = lean_ctor_get(v_x_1043_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_x_1043_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1048_ = v_x_1043_;
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_val_1046_);
lean_dec(v_x_1043_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1050_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3));
v___x_1051_ = l_String_quote(v_val_1046_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 3);
lean_ctor_set(v___x_1048_, 0, v___x_1051_);
v___x_1053_ = v___x_1048_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1050_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Repr_addAppParen(v___x_1054_, v_x_1044_);
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___boxed(lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(v_x_1058_, v_x_1059_);
lean_dec(v_x_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(lean_object* v_x_1073_){
_start:
{
lean_object* v_toTZifV1_1074_; lean_object* v_footer_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1109_; 
v_toTZifV1_1074_ = lean_ctor_get(v_x_1073_, 0);
v_footer_1075_ = lean_ctor_get(v_x_1073_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1077_ = v_x_1073_;
v_isShared_1078_ = v_isSharedCheck_1109_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_footer_1075_);
lean_inc(v_toTZifV1_1074_);
lean_dec(v_x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1109_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1079_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_1080_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3));
v___x_1081_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_toTZifV1_1074_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 4);
lean_ctor_set(v___x_1077_, 1, v___x_1083_);
lean_ctor_set(v___x_1077_, 0, v___x_1081_);
v___x_1085_ = v___x_1077_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1086_ = 0;
v___x_1087_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1080_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_1090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_box(1);
v___x_1092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5));
v___x_1094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___x_1079_);
v___x_1096_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4);
v___x_1097_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(v_footer_1075_, v___x_1082_);
v___x_1098_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*1, v___x_1086_);
v___x_1100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1095_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1102_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___x_1100_);
v___x_1104_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1101_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*1, v___x_1086_);
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(lean_object* v_x_1110_, lean_object* v_prec_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_x_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___boxed(lean_object* v_x_1113_, lean_object* v_prec_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(v_x_1113_, v_prec_1114_);
lean_dec(v_prec_1114_);
return v_res_1115_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_box(0);
v___x_1119_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default(void){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0);
return v___x_1121_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2(void){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default;
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1));
return v___x_1125_;
}
else
{
lean_object* v_val_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_val_1126_ = lean_ctor_get(v_x_1123_, 0);
lean_inc(v_val_1126_);
lean_dec_ref(v_x_1123_);
v___x_1127_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3));
v___x_1128_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_val_1126_);
v___x_1129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Repr_addAppParen(v___x_1129_, v_x_1124_);
return v___x_1130_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0___boxed(lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(v_x_1131_, v_x_1132_);
lean_dec(v_x_1132_);
return v_res_1133_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_unsigned_to_nat(6u);
v___x_1144_ = lean_nat_to_int(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(lean_object* v_x_1148_){
_start:
{
lean_object* v_v1_1149_; lean_object* v_v2_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1183_; 
v_v1_1149_ = lean_ctor_get(v_x_1148_, 0);
v_v2_1150_ = lean_ctor_get(v_x_1148_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1152_ = v_x_1148_;
v_isShared_1153_ = v_isSharedCheck_1183_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_v2_1150_);
lean_inc(v_v1_1149_);
lean_dec(v_x_1148_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1183_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1154_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_1155_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3));
v___x_1156_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4);
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_v1_1149_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 4);
lean_ctor_set(v___x_1152_, 1, v___x_1158_);
lean_ctor_set(v___x_1152_, 0, v___x_1156_);
v___x_1160_ = v___x_1152_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1161_ = 0;
v___x_1162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*1, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1155_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_1165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_box(1);
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6));
v___x_1169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v___x_1154_);
v___x_1171_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(v_v2_1150_, v___x_1157_);
v___x_1172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1156_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*1, v___x_1161_);
v___x_1174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1170_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1176_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v___x_1174_);
v___x_1178_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1175_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*1, v___x_1161_);
return v___x_1181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr(lean_object* v_x_1184_, lean_object* v_prec_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(v_x_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___boxed(lean_object* v_x_1187_, lean_object* v_prec_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr(v_x_1187_, v_prec_1188_);
lean_dec(v_prec_1188_);
return v_res_1189_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_box(0);
v___x_1193_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v___x_1192_);
return v___x_1194_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default(void){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0);
return v___x_1195_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif(void){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Std_Time_TimeZone_TZif_instInhabitedTZif_default;
return v___x_1196_;
}
}
static lean_object* _init_l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = l_instInhabitedUInt32;
v___x_1198_ = lean_box_uint32(v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(lean_object* v_msg_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; uint32_t v___x_1202_; 
v___x_1200_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1;
v___x_1201_ = lean_panic_fn(v___x_1200_, v_msg_1199_);
v___x_1202_ = lean_unbox_uint32(v___x_1201_);
lean_dec(v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed(lean_object* v_msg_1203_){
_start:
{
uint32_t v_res_1204_; lean_object* v_r_1205_; 
v_res_1204_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v_msg_1203_);
v_r_1205_ = lean_box_uint32(v_res_1204_);
return v_r_1205_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1209_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2));
v___x_1210_ = lean_unsigned_to_nat(2u);
v___x_1211_ = lean_unsigned_to_nat(181u);
v___x_1212_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1));
v___x_1213_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0));
v___x_1214_ = l_mkPanicMessageWithDecl(v___x_1213_, v___x_1212_, v___x_1211_, v___x_1210_, v___x_1209_);
return v___x_1214_;
}
}
LEAN_EXPORT uint32_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(lean_object* v_bs_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1216_ = lean_byte_array_size(v_bs_1215_);
v___x_1217_ = lean_unsigned_to_nat(4u);
v___x_1218_ = lean_nat_dec_eq(v___x_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; uint32_t v___x_1220_; 
v___x_1219_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3);
v___x_1220_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v___x_1219_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; uint8_t v___x_1222_; uint32_t v___x_1223_; uint32_t v___x_1224_; uint32_t v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; uint32_t v___x_1228_; uint32_t v___x_1229_; uint32_t v___x_1230_; uint32_t v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; uint32_t v___x_1234_; uint32_t v___x_1235_; uint32_t v___x_1236_; uint32_t v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; uint32_t v___x_1240_; uint32_t v___x_1241_; 
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_byte_array_get(v_bs_1215_, v___x_1221_);
v___x_1223_ = lean_uint8_to_uint32(v___x_1222_);
v___x_1224_ = 24;
v___x_1225_ = lean_uint32_shift_left(v___x_1223_, v___x_1224_);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_byte_array_get(v_bs_1215_, v___x_1226_);
v___x_1228_ = lean_uint8_to_uint32(v___x_1227_);
v___x_1229_ = 16;
v___x_1230_ = lean_uint32_shift_left(v___x_1228_, v___x_1229_);
v___x_1231_ = lean_uint32_lor(v___x_1225_, v___x_1230_);
v___x_1232_ = lean_unsigned_to_nat(2u);
v___x_1233_ = lean_byte_array_get(v_bs_1215_, v___x_1232_);
v___x_1234_ = lean_uint8_to_uint32(v___x_1233_);
v___x_1235_ = 8;
v___x_1236_ = lean_uint32_shift_left(v___x_1234_, v___x_1235_);
v___x_1237_ = lean_uint32_lor(v___x_1231_, v___x_1236_);
v___x_1238_ = lean_unsigned_to_nat(3u);
v___x_1239_ = lean_byte_array_get(v_bs_1215_, v___x_1238_);
v___x_1240_ = lean_uint8_to_uint32(v___x_1239_);
v___x_1241_ = lean_uint32_lor(v___x_1237_, v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___boxed(lean_object* v_bs_1242_){
_start:
{
uint32_t v_res_1243_; lean_object* v_r_1244_; 
v_res_1243_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_1242_);
lean_dec_ref(v_bs_1242_);
v_r_1244_ = lean_box_uint32(v_res_1243_);
return v_r_1244_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_unsigned_to_nat(31u);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_shiftl(v___x_1246_, v___x_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(lean_object* v_bs_1248_){
_start:
{
uint32_t v___x_1249_; lean_object* v_n_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1249_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_1248_);
v_n_1250_ = lean_uint32_to_nat(v___x_1249_);
v___x_1251_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0);
v___x_1252_ = lean_nat_dec_lt(v_n_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_cstr_to_nat("4294967296");
v___x_1254_ = lean_nat_sub(v___x_1253_, v_n_1250_);
lean_dec(v_n_1250_);
v___x_1255_ = l_Int_negOfNat(v___x_1254_);
lean_dec(v___x_1254_);
return v___x_1255_;
}
else
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_nat_to_int(v_n_1250_);
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___boxed(lean_object* v_bs_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(v_bs_1257_);
lean_dec_ref(v_bs_1257_);
return v_res_1258_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_unsigned_to_nat(63u);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_shiftl(v___x_1260_, v___x_1259_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1(void){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(lean_object* v_bs_1263_){
_start:
{
uint64_t v___x_1264_; lean_object* v_n_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1264_ = l_ByteArray_toUInt64BE_x21(v_bs_1263_);
v_n_1265_ = lean_uint64_to_nat(v___x_1264_);
v___x_1266_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0);
v___x_1267_ = lean_nat_dec_lt(v_n_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1);
v___x_1269_ = lean_nat_sub(v___x_1268_, v_n_1265_);
lean_dec(v_n_1265_);
v___x_1270_ = l_Int_negOfNat(v___x_1269_);
lean_dec(v___x_1269_);
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_nat_to_int(v_n_1265_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___boxed(lean_object* v_bs_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(v_bs_1272_);
lean_dec_ref(v_bs_1272_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(lean_object* v_upperBound_1274_, lean_object* v_p_1275_, lean_object* v_a_1276_, lean_object* v_b_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = lean_nat_dec_lt(v_a_1276_, v_upperBound_1274_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec(v_a_1276_);
lean_dec_ref(v_p_1275_);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___y_1278_);
lean_ctor_set(v___x_1280_, 1, v_b_1277_);
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; 
lean_inc_ref(v_p_1275_);
v___x_1281_ = lean_apply_1(v_p_1275_, v___y_1278_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_pos_1282_; lean_object* v_res_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_pos_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_pos_1282_);
v_res_1283_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_res_1283_);
lean_dec_ref(v___x_1281_);
v___x_1284_ = lean_array_push(v_b_1277_, v_res_1283_);
v___x_1285_ = lean_unsigned_to_nat(1u);
v___x_1286_ = lean_nat_add(v_a_1276_, v___x_1285_);
lean_dec(v_a_1276_);
v_a_1276_ = v___x_1286_;
v_b_1277_ = v___x_1284_;
v___y_1278_ = v_pos_1282_;
goto _start;
}
else
{
lean_object* v_pos_1288_; lean_object* v_err_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_b_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_p_1275_);
v_pos_1288_ = lean_ctor_get(v___x_1281_, 0);
v_err_1289_ = lean_ctor_get(v___x_1281_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1281_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_err_1289_);
lean_inc(v_pos_1288_);
lean_dec(v___x_1281_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_pos_1288_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_err_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg___boxed(lean_object* v_upperBound_1297_, lean_object* v_p_1298_, lean_object* v_a_1299_, lean_object* v_b_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_1297_, v_p_1298_, v_a_1299_, v_b_1300_, v___y_1301_);
lean_dec(v_upperBound_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(lean_object* v_n_1305_, lean_object* v_p_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v___x_1308_; lean_object* v_result_1309_; lean_object* v___x_1310_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v_result_1309_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0));
v___x_1310_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_n_1305_, v_p_1306_, v___x_1308_, v_result_1309_, v_a_1307_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___boxed(lean_object* v_n_1311_, lean_object* v_p_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v_n_1311_, v_p_1312_, v_a_1313_);
lean_dec(v_n_1311_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(lean_object* v_00_u03b1_1315_, lean_object* v_n_1316_, lean_object* v_p_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v_n_1316_, v_p_1317_, v_a_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___boxed(lean_object* v_00_u03b1_1320_, lean_object* v_n_1321_, lean_object* v_p_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(v_00_u03b1_1320_, v_n_1321_, v_p_1322_, v_a_1323_);
lean_dec(v_n_1321_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(lean_object* v_00_u03b1_1325_, lean_object* v_upperBound_1326_, lean_object* v_p_1327_, lean_object* v_inst_1328_, lean_object* v_R_1329_, lean_object* v_a_1330_, lean_object* v_b_1331_, lean_object* v_c_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_1326_, v_p_1327_, v_a_1330_, v_b_1331_, v___y_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_upperBound_1336_, lean_object* v_p_1337_, lean_object* v_inst_1338_, lean_object* v_R_1339_, lean_object* v_a_1340_, lean_object* v_b_1341_, lean_object* v_c_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(v_00_u03b1_1335_, v_upperBound_1336_, v_p_1337_, v_inst_1338_, v_R_1339_, v_a_1340_, v_b_1341_, v_c_1342_, v___y_1343_);
lean_dec(v_upperBound_1336_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu64(lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_unsigned_to_nat(8u);
v___x_1347_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1346_, v_a_1345_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_pos_1348_; lean_object* v_res_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1359_; 
v_pos_1348_ = lean_ctor_get(v___x_1347_, 0);
v_res_1349_ = lean_ctor_get(v___x_1347_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1351_ = v___x_1347_;
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_res_1349_);
lean_inc(v_pos_1348_);
lean_dec(v___x_1347_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; uint64_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1353_ = l_ByteSlice_toByteArray(v_res_1349_);
v___x_1354_ = l_ByteArray_toUInt64LE_x21(v___x_1353_);
lean_dec_ref(v___x_1353_);
v___x_1355_ = lean_box_uint64(v___x_1354_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 1, v___x_1355_);
v___x_1357_ = v___x_1351_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_pos_1348_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_pos_1360_; lean_object* v_err_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
v_pos_1360_ = lean_ctor_get(v___x_1347_, 0);
v_err_1361_ = lean_ctor_get(v___x_1347_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1347_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_err_1361_);
lean_inc(v_pos_1360_);
lean_dec(v___x_1347_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_pos_1360_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_err_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64(lean_object* v_a_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_unsigned_to_nat(8u);
v___x_1371_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1370_, v_a_1369_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_pos_1372_; lean_object* v_res_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1382_; 
v_pos_1372_ = lean_ctor_get(v___x_1371_, 0);
v_res_1373_ = lean_ctor_get(v___x_1371_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1375_ = v___x_1371_;
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_res_1373_);
lean_inc(v_pos_1372_);
lean_dec(v___x_1371_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1377_ = l_ByteSlice_toByteArray(v_res_1373_);
v___x_1378_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(v___x_1377_);
lean_dec_ref(v___x_1377_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1378_);
v___x_1380_ = v___x_1375_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_pos_1372_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
lean_object* v_pos_1383_; lean_object* v_err_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_pos_1383_ = lean_ctor_get(v___x_1371_, 0);
v_err_1384_ = lean_ctor_get(v___x_1371_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1371_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_err_1384_);
lean_inc(v_pos_1383_);
lean_dec(v___x_1371_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_pos_1383_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_err_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_unsigned_to_nat(4u);
v___x_1394_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1393_, v_a_1392_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_pos_1395_; lean_object* v_res_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1406_; 
v_pos_1395_ = lean_ctor_get(v___x_1394_, 0);
v_res_1396_ = lean_ctor_get(v___x_1394_, 1);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1398_ = v___x_1394_;
v_isShared_1399_ = v_isSharedCheck_1406_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_res_1396_);
lean_inc(v_pos_1395_);
lean_dec(v___x_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1406_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; uint32_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1400_ = l_ByteSlice_toByteArray(v_res_1396_);
v___x_1401_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v___x_1400_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = lean_box_uint32(v___x_1401_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v___x_1402_);
v___x_1404_ = v___x_1398_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_pos_1395_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v_pos_1407_; lean_object* v_err_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_pos_1407_ = lean_ctor_get(v___x_1394_, 0);
v_err_1408_ = lean_ctor_get(v___x_1394_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1394_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_err_1408_);
lean_inc(v_pos_1407_);
lean_dec(v___x_1394_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_pos_1407_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_err_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(lean_object* v_a_1416_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_unsigned_to_nat(4u);
v___x_1418_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1417_, v_a_1416_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_pos_1419_; lean_object* v_res_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1429_; 
v_pos_1419_ = lean_ctor_get(v___x_1418_, 0);
v_res_1420_ = lean_ctor_get(v___x_1418_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1422_ = v___x_1418_;
v_isShared_1423_ = v_isSharedCheck_1429_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_res_1420_);
lean_inc(v_pos_1419_);
lean_dec(v___x_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1429_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1424_ = l_ByteSlice_toByteArray(v_res_1420_);
v___x_1425_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(v___x_1424_);
lean_dec_ref(v___x_1424_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 1, v___x_1425_);
v___x_1427_ = v___x_1422_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_pos_1419_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_pos_1430_; lean_object* v_err_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_pos_1430_ = lean_ctor_get(v___x_1418_, 0);
v_err_1431_ = lean_ctor_get(v___x_1418_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1418_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_err_1431_);
lean_inc(v_pos_1430_);
lean_dec(v___x_1418_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_pos_1430_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_err_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(lean_object* v_a_1439_){
_start:
{
lean_object* v_array_1440_; lean_object* v_idx_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_array_1440_ = lean_ctor_get(v_a_1439_, 0);
v_idx_1441_ = lean_ctor_get(v_a_1439_, 1);
v___x_1442_ = lean_byte_array_size(v_array_1440_);
v___x_1443_ = lean_nat_dec_lt(v_idx_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_a_1439_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
return v___x_1445_;
}
else
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1457_; 
lean_inc(v_idx_1441_);
lean_inc_ref(v_array_1440_);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_a_1439_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; lean_object* v_unused_1459_; 
v_unused_1458_ = lean_ctor_get(v_a_1439_, 1);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_a_1439_, 0);
lean_dec(v_unused_1459_);
v___x_1447_ = v_a_1439_;
v_isShared_1448_ = v_isSharedCheck_1457_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v_a_1439_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1457_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
uint8_t v_c_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_it_x27_1453_; 
v_c_1449_ = lean_byte_array_fget(v_array_1440_, v_idx_1441_);
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_add(v_idx_1441_, v___x_1450_);
lean_dec(v_idx_1441_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 1, v___x_1451_);
v_it_x27_1453_ = v___x_1447_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_array_1440_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1451_);
v_it_x27_1453_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_box(v_c_1449_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v_it_x27_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_a_1460_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_pos_1462_; lean_object* v_res_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1480_; 
v_pos_1462_ = lean_ctor_get(v___x_1461_, 0);
v_res_1463_ = lean_ctor_get(v___x_1461_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1465_ = v___x_1461_;
v_isShared_1466_ = v_isSharedCheck_1480_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_res_1463_);
lean_inc(v_pos_1462_);
lean_dec(v___x_1461_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1480_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
uint8_t v___x_1467_; uint8_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = 0;
v___x_1468_ = lean_unbox(v_res_1463_);
lean_dec(v_res_1463_);
v___x_1469_ = lean_uint8_dec_eq(v___x_1468_, v___x_1467_);
if (v___x_1469_ == 0)
{
uint8_t v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1470_ = 1;
v___x_1471_ = lean_box(v___x_1470_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v___x_1471_);
v___x_1473_ = v___x_1465_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_pos_1462_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
else
{
uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1475_ = 0;
v___x_1476_ = lean_box(v___x_1475_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v___x_1476_);
v___x_1478_ = v___x_1465_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_pos_1462_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_pos_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1489_; 
v_pos_1481_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v___x_1461_, 1);
lean_dec(v_unused_1490_);
v___x_1483_ = v___x_1461_;
v_isShared_1484_ = v_isSharedCheck_1489_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_pos_1481_);
lean_dec(v___x_1461_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1489_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1485_ = lean_box(0);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 1, v___x_1485_);
v___x_1487_ = v___x_1483_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_pos_1481_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17));
v___x_1492_ = lean_string_to_utf8(v___x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0);
v___x_1495_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_1494_, v_a_1493_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_pos_1496_; lean_object* v___x_1497_; 
v_pos_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_pos_1496_);
lean_dec_ref(v___x_1495_);
v___x_1497_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_pos_1496_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_pos_1498_; lean_object* v_res_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v_pos_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_pos_1498_);
v_res_1499_ = lean_ctor_get(v___x_1497_, 1);
lean_inc(v_res_1499_);
lean_dec_ref(v___x_1497_);
v___x_1500_ = lean_unsigned_to_nat(15u);
v___x_1501_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1500_, v_pos_1498_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_pos_1502_; lean_object* v___x_1503_; 
v_pos_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_pos_1502_);
lean_dec_ref(v___x_1501_);
v___x_1503_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1502_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_pos_1504_; lean_object* v_res_1505_; lean_object* v___x_1506_; 
v_pos_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_pos_1504_);
v_res_1505_ = lean_ctor_get(v___x_1503_, 1);
lean_inc(v_res_1505_);
lean_dec_ref(v___x_1503_);
v___x_1506_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1504_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_pos_1507_; lean_object* v_res_1508_; lean_object* v___x_1509_; 
v_pos_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_pos_1507_);
v_res_1508_ = lean_ctor_get(v___x_1506_, 1);
lean_inc(v_res_1508_);
lean_dec_ref(v___x_1506_);
v___x_1509_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1507_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_pos_1510_; lean_object* v_res_1511_; lean_object* v___x_1512_; 
v_pos_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_pos_1510_);
v_res_1511_ = lean_ctor_get(v___x_1509_, 1);
lean_inc(v_res_1511_);
lean_dec_ref(v___x_1509_);
v___x_1512_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1510_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_pos_1513_; lean_object* v_res_1514_; lean_object* v___x_1515_; 
v_pos_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_pos_1513_);
v_res_1514_ = lean_ctor_get(v___x_1512_, 1);
lean_inc(v_res_1514_);
lean_dec_ref(v___x_1512_);
v___x_1515_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1513_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_pos_1516_; lean_object* v_res_1517_; lean_object* v___x_1518_; 
v_pos_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_pos_1516_);
v_res_1517_ = lean_ctor_get(v___x_1515_, 1);
lean_inc(v_res_1517_);
lean_dec_ref(v___x_1515_);
v___x_1518_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1516_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_pos_1519_; lean_object* v_res_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1535_; 
v_pos_1519_ = lean_ctor_get(v___x_1518_, 0);
v_res_1520_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1522_ = v___x_1518_;
v_isShared_1523_ = v_isSharedCheck_1535_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_res_1520_);
lean_inc(v_pos_1519_);
lean_dec(v___x_1518_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1535_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; uint8_t v___x_1525_; uint32_t v___x_1526_; uint32_t v___x_1527_; uint32_t v___x_1528_; uint32_t v___x_1529_; uint32_t v___x_1530_; uint32_t v___x_1531_; lean_object* v___x_1533_; 
v___x_1524_ = lean_alloc_ctor(0, 0, 25);
v___x_1525_ = lean_unbox(v_res_1499_);
lean_dec(v_res_1499_);
lean_ctor_set_uint8(v___x_1524_, 24, v___x_1525_);
v___x_1526_ = lean_unbox_uint32(v_res_1505_);
lean_dec(v_res_1505_);
lean_ctor_set_uint32(v___x_1524_, 0, v___x_1526_);
v___x_1527_ = lean_unbox_uint32(v_res_1508_);
lean_dec(v_res_1508_);
lean_ctor_set_uint32(v___x_1524_, 4, v___x_1527_);
v___x_1528_ = lean_unbox_uint32(v_res_1511_);
lean_dec(v_res_1511_);
lean_ctor_set_uint32(v___x_1524_, 8, v___x_1528_);
v___x_1529_ = lean_unbox_uint32(v_res_1514_);
lean_dec(v_res_1514_);
lean_ctor_set_uint32(v___x_1524_, 12, v___x_1529_);
v___x_1530_ = lean_unbox_uint32(v_res_1517_);
lean_dec(v_res_1517_);
lean_ctor_set_uint32(v___x_1524_, 16, v___x_1530_);
v___x_1531_ = lean_unbox_uint32(v_res_1520_);
lean_dec(v_res_1520_);
lean_ctor_set_uint32(v___x_1524_, 20, v___x_1531_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v___x_1524_);
v___x_1533_ = v___x_1522_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_pos_1519_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1524_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
lean_object* v_pos_1536_; lean_object* v_err_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec(v_res_1517_);
lean_dec(v_res_1514_);
lean_dec(v_res_1511_);
lean_dec(v_res_1508_);
lean_dec(v_res_1505_);
lean_dec(v_res_1499_);
v_pos_1536_ = lean_ctor_get(v___x_1518_, 0);
v_err_1537_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1518_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_err_1537_);
lean_inc(v_pos_1536_);
lean_dec(v___x_1518_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_pos_1536_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_err_1537_);
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
else
{
lean_object* v_pos_1545_; lean_object* v_err_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_res_1514_);
lean_dec(v_res_1511_);
lean_dec(v_res_1508_);
lean_dec(v_res_1505_);
lean_dec(v_res_1499_);
v_pos_1545_ = lean_ctor_get(v___x_1515_, 0);
v_err_1546_ = lean_ctor_get(v___x_1515_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1515_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_err_1546_);
lean_inc(v_pos_1545_);
lean_dec(v___x_1515_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_pos_1545_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_err_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_pos_1554_; lean_object* v_err_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_res_1511_);
lean_dec(v_res_1508_);
lean_dec(v_res_1505_);
lean_dec(v_res_1499_);
v_pos_1554_ = lean_ctor_get(v___x_1512_, 0);
v_err_1555_ = lean_ctor_get(v___x_1512_, 1);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1512_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_err_1555_);
lean_inc(v_pos_1554_);
lean_dec(v___x_1512_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_pos_1554_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_err_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_pos_1563_; lean_object* v_err_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_res_1508_);
lean_dec(v_res_1505_);
lean_dec(v_res_1499_);
v_pos_1563_ = lean_ctor_get(v___x_1509_, 0);
v_err_1564_ = lean_ctor_get(v___x_1509_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1509_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_err_1564_);
lean_inc(v_pos_1563_);
lean_dec(v___x_1509_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_pos_1563_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_err_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_object* v_pos_1572_; lean_object* v_err_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v_res_1505_);
lean_dec(v_res_1499_);
v_pos_1572_ = lean_ctor_get(v___x_1506_, 0);
v_err_1573_ = lean_ctor_get(v___x_1506_, 1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1506_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_err_1573_);
lean_inc(v_pos_1572_);
lean_dec(v___x_1506_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_pos_1572_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_err_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_pos_1581_; lean_object* v_err_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_res_1499_);
v_pos_1581_ = lean_ctor_get(v___x_1503_, 0);
v_err_1582_ = lean_ctor_get(v___x_1503_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1503_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_err_1582_);
lean_inc(v_pos_1581_);
lean_dec(v___x_1503_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_pos_1581_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_err_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v_pos_1590_; lean_object* v_err_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_res_1499_);
v_pos_1590_ = lean_ctor_get(v___x_1501_, 0);
v_err_1591_ = lean_ctor_get(v___x_1501_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1501_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_err_1591_);
lean_inc(v_pos_1590_);
lean_dec(v___x_1501_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_pos_1590_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_err_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_pos_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1607_; 
v_pos_1599_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v___x_1497_, 1);
lean_dec(v_unused_1608_);
v___x_1601_ = v___x_1497_;
v_isShared_1602_ = v_isSharedCheck_1607_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_pos_1599_);
lean_dec(v___x_1497_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1607_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_box(0);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 1, v___x_1603_);
v___x_1605_ = v___x_1601_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_pos_1599_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v_pos_1609_; lean_object* v_err_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_pos_1609_ = lean_ctor_get(v___x_1495_, 0);
v_err_1610_ = lean_ctor_get(v___x_1495_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1495_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_err_1610_);
lean_inc(v_pos_1609_);
lean_dec(v___x_1495_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_pos_1609_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_err_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType(lean_object* v_a_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(v_a_1618_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_pos_1620_; lean_object* v_res_1621_; lean_object* v___x_1622_; 
v_pos_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_pos_1620_);
v_res_1621_ = lean_ctor_get(v___x_1619_, 1);
lean_inc(v_res_1621_);
lean_dec_ref(v___x_1619_);
v___x_1622_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(v_pos_1620_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_pos_1623_; lean_object* v_res_1624_; lean_object* v___x_1625_; 
v_pos_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_pos_1623_);
v_res_1624_ = lean_ctor_get(v___x_1622_, 1);
lean_inc(v_res_1624_);
lean_dec_ref(v___x_1622_);
v___x_1625_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_pos_1623_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_pos_1626_; lean_object* v_res_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1637_; 
v_pos_1626_ = lean_ctor_get(v___x_1625_, 0);
v_res_1627_ = lean_ctor_get(v___x_1625_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1629_ = v___x_1625_;
v_isShared_1630_ = v_isSharedCheck_1637_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_res_1627_);
lean_inc(v_pos_1626_);
lean_dec(v___x_1625_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1637_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1635_; 
v___x_1631_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1631_, 0, v_res_1621_);
v___x_1632_ = lean_unbox(v_res_1624_);
lean_dec(v_res_1624_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*1, v___x_1632_);
v___x_1633_ = lean_unbox(v_res_1627_);
lean_dec(v_res_1627_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*1 + 1, v___x_1633_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 1, v___x_1631_);
v___x_1635_ = v___x_1629_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_pos_1626_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v___x_1631_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
else
{
lean_object* v_pos_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_res_1624_);
lean_dec(v_res_1621_);
v_pos_1638_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v___x_1625_, 1);
lean_dec(v_unused_1647_);
v___x_1640_ = v___x_1625_;
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_pos_1638_);
lean_dec(v___x_1625_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = lean_box(0);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_pos_1638_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_object* v_pos_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_res_1621_);
v_pos_1648_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; 
v_unused_1657_ = lean_ctor_get(v___x_1622_, 1);
lean_dec(v_unused_1657_);
v___x_1650_ = v___x_1622_;
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_pos_1648_);
lean_dec(v___x_1622_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_box(0);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 1, v___x_1652_);
v___x_1654_ = v___x_1650_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_pos_1648_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_pos_1658_; lean_object* v_err_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_pos_1658_ = lean_ctor_get(v___x_1619_, 0);
v_err_1659_ = lean_ctor_get(v___x_1619_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1619_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_err_1659_);
lean_inc(v_pos_1658_);
lean_dec(v___x_1619_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_pos_1658_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_err_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond(lean_object* v_p_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_apply_1(v_p_1667_, v_a_1668_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_pos_1670_; lean_object* v_res_1671_; lean_object* v___x_1672_; 
v_pos_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_pos_1670_);
v_res_1671_ = lean_ctor_get(v___x_1669_, 1);
lean_inc(v_res_1671_);
lean_dec_ref(v___x_1669_);
v___x_1672_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(v_pos_1670_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_pos_1673_; lean_object* v_res_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1682_; 
v_pos_1673_ = lean_ctor_get(v___x_1672_, 0);
v_res_1674_ = lean_ctor_get(v___x_1672_, 1);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1676_ = v___x_1672_;
v_isShared_1677_ = v_isSharedCheck_1682_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_res_1674_);
lean_inc(v_pos_1673_);
lean_dec(v___x_1672_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1682_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v_res_1671_);
lean_ctor_set(v___x_1678_, 1, v_res_1674_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v___x_1678_);
v___x_1680_ = v___x_1676_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_pos_1673_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
else
{
lean_object* v_pos_1683_; lean_object* v_err_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec(v_res_1671_);
v_pos_1683_ = lean_ctor_get(v___x_1672_, 0);
v_err_1684_ = lean_ctor_get(v___x_1672_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1672_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_err_1684_);
lean_inc(v_pos_1683_);
lean_dec(v___x_1672_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_pos_1683_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_err_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
else
{
lean_object* v_pos_1692_; lean_object* v_err_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_pos_1692_ = lean_ctor_get(v___x_1669_, 0);
v_err_1693_ = lean_ctor_get(v___x_1669_, 1);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1669_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_err_1693_);
lean_inc(v_pos_1692_);
lean_dec(v___x_1669_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_pos_1692_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_err_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(lean_object* v_size_1701_, uint32_t v_n_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_uint32_to_nat(v_n_1702_);
v___x_1705_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1704_, v_size_1701_, v_a_1703_);
lean_dec(v___x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes___boxed(lean_object* v_size_1706_, lean_object* v_n_1707_, lean_object* v_a_1708_){
_start:
{
uint32_t v_n_boxed_1709_; lean_object* v_res_1710_; 
v_n_boxed_1709_ = lean_unbox_uint32(v_n_1707_);
lean_dec(v_n_1707_);
v_res_1710_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v_size_1706_, v_n_boxed_1709_, v_a_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(uint32_t v_n_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = lean_uint32_to_nat(v_n_1711_);
v___x_1714_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8), 1, 0);
v___x_1715_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1713_, v___x_1714_, v_a_1712_);
lean_dec(v___x_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices___boxed(lean_object* v_n_1716_, lean_object* v_a_1717_){
_start:
{
uint32_t v_n_boxed_1718_; lean_object* v_res_1719_; 
v_n_boxed_1718_ = lean_unbox_uint32(v_n_1716_);
lean_dec(v_n_1716_);
v_res_1719_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_n_boxed_1718_, v_a_1717_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(uint32_t v_n_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_uint32_to_nat(v_n_1720_);
v___x_1723_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType), 1, 0);
v___x_1724_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1722_, v___x_1723_, v_a_1721_);
lean_dec(v___x_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes___boxed(lean_object* v_n_1725_, lean_object* v_a_1726_){
_start:
{
uint32_t v_n_boxed_1727_; lean_object* v_res_1728_; 
v_n_boxed_1727_ = lean_unbox_uint32(v_n_1725_);
lean_dec(v_n_1725_);
v_res_1728_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_n_boxed_1727_, v_a_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(lean_object* v_upperBound_1730_, lean_object* v_res_1731_, lean_object* v_a_1732_, lean_object* v_b_1733_, lean_object* v___y_1734_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_nat_dec_lt(v_a_1732_, v_upperBound_1730_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
lean_dec(v_a_1732_);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___y_1734_);
lean_ctor_set(v___x_1736_, 1, v_b_1733_);
return v___x_1736_;
}
else
{
lean_object* v_fst_1737_; lean_object* v_snd_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1763_; 
v_fst_1737_ = lean_ctor_get(v_b_1733_, 0);
v_snd_1738_ = lean_ctor_get(v_b_1733_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_b_1733_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1740_ = v_b_1733_;
v_isShared_1741_ = v_isSharedCheck_1763_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_snd_1738_);
lean_inc(v_fst_1737_);
lean_dec(v_b_1733_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1763_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; uint8_t v___x_1746_; uint8_t v___x_1747_; 
v___x_1742_ = l_instInhabitedUInt8;
v___x_1743_ = lean_box(v___x_1742_);
v___x_1744_ = lean_array_get_borrowed(v___x_1743_, v_res_1731_, v_a_1732_);
v___x_1745_ = 0;
v___x_1746_ = lean_unbox(v___x_1744_);
v___x_1747_ = lean_uint8_dec_eq(v___x_1746_, v___x_1745_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; uint32_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1748_ = lean_unbox(v___x_1744_);
v___x_1749_ = lean_uint8_to_uint32(v___x_1748_);
v___x_1750_ = lean_string_push(v_snd_1738_, v___x_1749_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v___x_1750_);
v___x_1752_ = v___x_1740_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_fst_1737_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = lean_nat_add(v_a_1732_, v___x_1753_);
lean_dec(v_a_1732_);
v_a_1732_ = v___x_1754_;
v_b_1733_ = v___x_1752_;
goto _start;
}
}
else
{
lean_object* v_current_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
lean_dec(v_a_1732_);
v_current_1757_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0));
v___x_1758_ = lean_array_push(v_fst_1737_, v_snd_1738_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v_current_1757_);
lean_ctor_set(v___x_1740_, 0, v___x_1758_);
v___x_1760_ = v___x_1740_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_current_1757_);
v___x_1760_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___y_1734_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
return v___x_1761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___boxed(lean_object* v_upperBound_1764_, lean_object* v_res_1765_, lean_object* v_a_1766_, lean_object* v_b_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_1764_, v_res_1765_, v_a_1766_, v_b_1767_, v___y_1768_);
lean_dec_ref(v_res_1765_);
lean_dec(v_upperBound_1764_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(lean_object* v___x_1770_, lean_object* v_res_1771_, lean_object* v_as_1772_, size_t v_sz_1773_, size_t v_i_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_){
_start:
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_usize_dec_lt(v_i_1774_, v_sz_1773_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___y_1776_);
lean_ctor_set(v___x_1778_, 1, v_b_1775_);
return v___x_1778_;
}
else
{
lean_object* v_a_1779_; uint8_t v_abbreviationIndex_1780_; lean_object* v_fst_1781_; lean_object* v_snd_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1805_; 
v_a_1779_ = lean_array_uget_borrowed(v_as_1772_, v_i_1774_);
v_abbreviationIndex_1780_ = lean_ctor_get_uint8(v_a_1779_, sizeof(void*)*1 + 1);
v_fst_1781_ = lean_ctor_get(v_b_1775_, 0);
v_snd_1782_ = lean_ctor_get(v_b_1775_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_b_1775_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1784_ = v_b_1775_;
v_isShared_1785_ = v_isSharedCheck_1805_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snd_1782_);
lean_inc(v_fst_1781_);
lean_dec(v_b_1775_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1805_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1786_ = lean_uint8_to_nat(v_abbreviationIndex_1780_);
if (v_isShared_1785_ == 0)
{
v___x_1788_ = v___x_1784_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_fst_1781_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_snd_1782_);
v___x_1788_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v___x_1770_, v_res_1771_, v___x_1786_, v___x_1788_, v___y_1776_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_res_1790_; lean_object* v_pos_1791_; lean_object* v_fst_1792_; lean_object* v_snd_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1803_; 
v_res_1790_ = lean_ctor_get(v___x_1789_, 1);
lean_inc(v_res_1790_);
v_pos_1791_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_pos_1791_);
lean_dec_ref(v___x_1789_);
v_fst_1792_ = lean_ctor_get(v_res_1790_, 0);
v_snd_1793_ = lean_ctor_get(v_res_1790_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_res_1790_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1795_ = v_res_1790_;
v_isShared_1796_ = v_isSharedCheck_1803_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_snd_1793_);
lean_inc(v_fst_1792_);
lean_dec(v_res_1790_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1803_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_fst_1792_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_snd_1793_);
v___x_1798_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
size_t v___x_1799_; size_t v___x_1800_; 
v___x_1799_ = ((size_t)1ULL);
v___x_1800_ = lean_usize_add(v_i_1774_, v___x_1799_);
v_i_1774_ = v___x_1800_;
v_b_1775_ = v___x_1798_;
v___y_1776_ = v_pos_1791_;
goto _start;
}
}
}
else
{
return v___x_1789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1___boxed(lean_object* v___x_1806_, lean_object* v_res_1807_, lean_object* v_as_1808_, lean_object* v_sz_1809_, lean_object* v_i_1810_, lean_object* v_b_1811_, lean_object* v___y_1812_){
_start:
{
size_t v_sz_boxed_1813_; size_t v_i_boxed_1814_; lean_object* v_res_1815_; 
v_sz_boxed_1813_ = lean_unbox_usize(v_sz_1809_);
lean_dec(v_sz_1809_);
v_i_boxed_1814_ = lean_unbox_usize(v_i_1810_);
lean_dec(v_i_1810_);
v_res_1815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_1806_, v_res_1807_, v_as_1808_, v_sz_boxed_1813_, v_i_boxed_1814_, v_b_1811_, v___y_1812_);
lean_dec_ref(v_as_1808_);
lean_dec_ref(v_res_1807_);
lean_dec(v___x_1806_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(lean_object* v_times_1821_, uint32_t v_n_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_uint32_to_nat(v_n_1822_);
v___x_1825_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8), 1, 0);
v___x_1826_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1824_, v___x_1825_, v_a_1823_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_pos_1827_; lean_object* v_res_1828_; lean_object* v___x_1829_; size_t v_sz_1830_; size_t v___x_1831_; lean_object* v___x_1832_; 
v_pos_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_pos_1827_);
v_res_1828_ = lean_ctor_get(v___x_1826_, 1);
lean_inc(v_res_1828_);
lean_dec_ref(v___x_1826_);
v___x_1829_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1));
v_sz_1830_ = lean_array_size(v_times_1821_);
v___x_1831_ = ((size_t)0ULL);
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_1824_, v_res_1828_, v_times_1821_, v_sz_1830_, v___x_1831_, v___x_1829_, v_pos_1827_);
lean_dec(v_res_1828_);
lean_dec(v___x_1824_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_res_1833_; lean_object* v_pos_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1842_; 
v_res_1833_ = lean_ctor_get(v___x_1832_, 1);
v_pos_1834_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1836_ = v___x_1832_;
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_res_1833_);
lean_inc(v_pos_1834_);
lean_dec(v___x_1832_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_fst_1838_; lean_object* v___x_1840_; 
v_fst_1838_ = lean_ctor_get(v_res_1833_, 0);
lean_inc(v_fst_1838_);
lean_dec(v_res_1833_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 1, v_fst_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_pos_1834_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_fst_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
lean_object* v_pos_1843_; lean_object* v_err_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
v_pos_1843_ = lean_ctor_get(v___x_1832_, 0);
v_err_1844_ = lean_ctor_get(v___x_1832_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1832_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_err_1844_);
lean_inc(v_pos_1843_);
lean_dec(v___x_1832_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_pos_1843_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_err_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_pos_1852_; lean_object* v_err_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v___x_1824_);
v_pos_1852_ = lean_ctor_get(v___x_1826_, 0);
v_err_1853_ = lean_ctor_get(v___x_1826_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1826_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_err_1853_);
lean_inc(v_pos_1852_);
lean_dec(v___x_1826_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_pos_1852_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_err_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___boxed(lean_object* v_times_1861_, lean_object* v_n_1862_, lean_object* v_a_1863_){
_start:
{
uint32_t v_n_boxed_1864_; lean_object* v_res_1865_; 
v_n_boxed_1864_ = lean_unbox_uint32(v_n_1862_);
lean_dec(v_n_1862_);
v_res_1865_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_times_1861_, v_n_boxed_1864_, v_a_1863_);
lean_dec_ref(v_times_1861_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(lean_object* v_upperBound_1866_, lean_object* v_res_1867_, lean_object* v_inst_1868_, lean_object* v_R_1869_, lean_object* v_a_1870_, lean_object* v_b_1871_, lean_object* v_c_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_1866_, v_res_1867_, v_a_1870_, v_b_1871_, v___y_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___boxed(lean_object* v_upperBound_1875_, lean_object* v_res_1876_, lean_object* v_inst_1877_, lean_object* v_R_1878_, lean_object* v_a_1879_, lean_object* v_b_1880_, lean_object* v_c_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(v_upperBound_1875_, v_res_1876_, v_inst_1877_, v_R_1878_, v_a_1879_, v_b_1880_, v_c_1881_, v___y_1882_);
lean_dec_ref(v_res_1876_);
lean_dec(v_upperBound_1875_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(lean_object* v_size_1884_, uint32_t v_n_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = lean_uint32_to_nat(v_n_1885_);
v___x_1888_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond), 2, 1);
lean_closure_set(v___x_1888_, 0, v_size_1884_);
v___x_1889_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1887_, v___x_1888_, v_a_1886_);
lean_dec(v___x_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds___boxed(lean_object* v_size_1890_, lean_object* v_n_1891_, lean_object* v_a_1892_){
_start:
{
uint32_t v_n_boxed_1893_; lean_object* v_res_1894_; 
v_n_boxed_1893_ = lean_unbox_uint32(v_n_1891_);
lean_dec(v_n_1891_);
v_res_1894_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v_size_1890_, v_n_boxed_1893_, v_a_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(uint32_t v_n_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = lean_uint32_to_nat(v_n_1895_);
v___x_1898_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool), 1, 0);
v___x_1899_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1897_, v___x_1898_, v_a_1896_);
lean_dec(v___x_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators___boxed(lean_object* v_n_1900_, lean_object* v_a_1901_){
_start:
{
uint32_t v_n_boxed_1902_; lean_object* v_res_1903_; 
v_n_boxed_1902_ = lean_unbox_uint32(v_n_1900_);
lean_dec(v_n_1900_);
v_res_1903_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_n_boxed_1902_, v_a_1901_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(lean_object* v_a_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(v_a_1904_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_res_1906_; lean_object* v_pos_1907_; uint32_t v_isutcnt_1908_; uint32_t v_isstdcnt_1909_; uint32_t v_leapcnt_1910_; uint32_t v_timecnt_1911_; uint32_t v_typecnt_1912_; uint32_t v_charcnt_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_res_1906_ = lean_ctor_get(v___x_1905_, 1);
lean_inc(v_res_1906_);
v_pos_1907_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_pos_1907_);
lean_dec_ref(v___x_1905_);
v_isutcnt_1908_ = lean_ctor_get_uint32(v_res_1906_, 0);
v_isstdcnt_1909_ = lean_ctor_get_uint32(v_res_1906_, 4);
v_leapcnt_1910_ = lean_ctor_get_uint32(v_res_1906_, 8);
v_timecnt_1911_ = lean_ctor_get_uint32(v_res_1906_, 12);
v_typecnt_1912_ = lean_ctor_get_uint32(v_res_1906_, 16);
v_charcnt_1913_ = lean_ctor_get_uint32(v_res_1906_, 20);
v___x_1914_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32), 1, 0);
lean_inc_ref(v___x_1914_);
v___x_1915_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_1914_, v_timecnt_1911_, v_pos_1907_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_pos_1916_; lean_object* v_res_1917_; lean_object* v___x_1918_; 
v_pos_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_pos_1916_);
v_res_1917_ = lean_ctor_get(v___x_1915_, 1);
lean_inc(v_res_1917_);
lean_dec_ref(v___x_1915_);
v___x_1918_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_1911_, v_pos_1916_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_pos_1919_; lean_object* v_res_1920_; lean_object* v___x_1921_; 
v_pos_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_pos_1919_);
v_res_1920_ = lean_ctor_get(v___x_1918_, 1);
lean_inc(v_res_1920_);
lean_dec_ref(v___x_1918_);
v___x_1921_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_1912_, v_pos_1919_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_pos_1922_; lean_object* v_res_1923_; lean_object* v___x_1924_; 
v_pos_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_pos_1922_);
v_res_1923_ = lean_ctor_get(v___x_1921_, 1);
lean_inc(v_res_1923_);
lean_dec_ref(v___x_1921_);
v___x_1924_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_1923_, v_charcnt_1913_, v_pos_1922_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_pos_1925_; lean_object* v_res_1926_; lean_object* v___x_1927_; 
v_pos_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_pos_1925_);
v_res_1926_ = lean_ctor_get(v___x_1924_, 1);
lean_inc(v_res_1926_);
lean_dec_ref(v___x_1924_);
v___x_1927_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_1914_, v_leapcnt_1910_, v_pos_1925_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_pos_1928_; lean_object* v_res_1929_; lean_object* v___x_1930_; 
v_pos_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_pos_1928_);
v_res_1929_ = lean_ctor_get(v___x_1927_, 1);
lean_inc(v_res_1929_);
lean_dec_ref(v___x_1927_);
v___x_1930_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_1909_, v_pos_1928_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_pos_1931_; lean_object* v_res_1932_; lean_object* v___x_1933_; 
v_pos_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_pos_1931_);
v_res_1932_ = lean_ctor_get(v___x_1930_, 1);
lean_inc(v_res_1932_);
lean_dec_ref(v___x_1930_);
v___x_1933_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_1908_, v_pos_1931_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_pos_1934_; lean_object* v_res_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1943_; 
v_pos_1934_ = lean_ctor_get(v___x_1933_, 0);
v_res_1935_ = lean_ctor_get(v___x_1933_, 1);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1937_ = v___x_1933_;
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_res_1935_);
lean_inc(v_pos_1934_);
lean_dec(v___x_1933_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1939_, 0, v_res_1906_);
lean_ctor_set(v___x_1939_, 1, v_res_1917_);
lean_ctor_set(v___x_1939_, 2, v_res_1920_);
lean_ctor_set(v___x_1939_, 3, v_res_1923_);
lean_ctor_set(v___x_1939_, 4, v_res_1926_);
lean_ctor_set(v___x_1939_, 5, v_res_1929_);
lean_ctor_set(v___x_1939_, 6, v_res_1932_);
lean_ctor_set(v___x_1939_, 7, v_res_1935_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v___x_1939_);
v___x_1941_ = v___x_1937_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_pos_1934_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
lean_object* v_pos_1944_; lean_object* v_err_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_res_1932_);
lean_dec(v_res_1929_);
lean_dec(v_res_1926_);
lean_dec(v_res_1923_);
lean_dec(v_res_1920_);
lean_dec(v_res_1917_);
lean_dec(v_res_1906_);
v_pos_1944_ = lean_ctor_get(v___x_1933_, 0);
v_err_1945_ = lean_ctor_get(v___x_1933_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1933_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_err_1945_);
lean_inc(v_pos_1944_);
lean_dec(v___x_1933_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_pos_1944_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_err_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_pos_1953_; lean_object* v_err_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_res_1929_);
lean_dec(v_res_1926_);
lean_dec(v_res_1923_);
lean_dec(v_res_1920_);
lean_dec(v_res_1917_);
lean_dec(v_res_1906_);
v_pos_1953_ = lean_ctor_get(v___x_1930_, 0);
v_err_1954_ = lean_ctor_get(v___x_1930_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1930_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_err_1954_);
lean_inc(v_pos_1953_);
lean_dec(v___x_1930_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_pos_1953_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_err_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_pos_1962_; lean_object* v_err_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_res_1926_);
lean_dec(v_res_1923_);
lean_dec(v_res_1920_);
lean_dec(v_res_1917_);
lean_dec(v_res_1906_);
v_pos_1962_ = lean_ctor_get(v___x_1927_, 0);
v_err_1963_ = lean_ctor_get(v___x_1927_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1927_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_err_1963_);
lean_inc(v_pos_1962_);
lean_dec(v___x_1927_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_pos_1962_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_err_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_object* v_pos_1971_; lean_object* v_err_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v_res_1923_);
lean_dec(v_res_1920_);
lean_dec(v_res_1917_);
lean_dec_ref(v___x_1914_);
lean_dec(v_res_1906_);
v_pos_1971_ = lean_ctor_get(v___x_1924_, 0);
v_err_1972_ = lean_ctor_get(v___x_1924_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1924_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_err_1972_);
lean_inc(v_pos_1971_);
lean_dec(v___x_1924_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_pos_1971_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_err_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_pos_1980_; lean_object* v_err_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_res_1920_);
lean_dec(v_res_1917_);
lean_dec_ref(v___x_1914_);
lean_dec(v_res_1906_);
v_pos_1980_ = lean_ctor_get(v___x_1921_, 0);
v_err_1981_ = lean_ctor_get(v___x_1921_, 1);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1921_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_err_1981_);
lean_inc(v_pos_1980_);
lean_dec(v___x_1921_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_pos_1980_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_err_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v_pos_1989_; lean_object* v_err_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_res_1917_);
lean_dec_ref(v___x_1914_);
lean_dec(v_res_1906_);
v_pos_1989_ = lean_ctor_get(v___x_1918_, 0);
v_err_1990_ = lean_ctor_get(v___x_1918_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1918_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_err_1990_);
lean_inc(v_pos_1989_);
lean_dec(v___x_1918_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_pos_1989_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_err_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_object* v_pos_1998_; lean_object* v_err_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v___x_1914_);
lean_dec(v_res_1906_);
v_pos_1998_ = lean_ctor_get(v___x_1915_, 0);
v_err_1999_ = lean_ctor_get(v___x_1915_, 1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1915_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_err_1999_);
lean_inc(v_pos_1998_);
lean_dec(v___x_1915_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_pos_1998_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_err_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v_pos_2007_; lean_object* v_err_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
v_pos_2007_ = lean_ctor_get(v___x_1905_, 0);
v_err_2008_ = lean_ctor_get(v___x_1905_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1905_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_err_2008_);
lean_inc(v_pos_2007_);
lean_dec(v___x_1905_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_pos_2007_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_err_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(lean_object* v_as_2016_, size_t v_sz_2017_, size_t v_i_2018_, lean_object* v_b_2019_, lean_object* v___y_2020_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_usize_dec_lt(v_i_2018_, v_sz_2017_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___y_2020_);
lean_ctor_set(v___x_2022_, 1, v_b_2019_);
return v___x_2022_;
}
else
{
lean_object* v_a_2023_; uint8_t v___x_2024_; uint32_t v___x_2025_; lean_object* v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; 
v_a_2023_ = lean_array_uget_borrowed(v_as_2016_, v_i_2018_);
v___x_2024_ = lean_unbox(v_a_2023_);
v___x_2025_ = lean_uint8_to_uint32(v___x_2024_);
v___x_2026_ = lean_string_push(v_b_2019_, v___x_2025_);
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_2018_, v___x_2027_);
v_i_2018_ = v___x_2028_;
v_b_2019_ = v___x_2026_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1___boxed(lean_object* v_as_2030_, lean_object* v_sz_2031_, lean_object* v_i_2032_, lean_object* v_b_2033_, lean_object* v___y_2034_){
_start:
{
size_t v_sz_boxed_2035_; size_t v_i_boxed_2036_; lean_object* v_res_2037_; 
v_sz_boxed_2035_ = lean_unbox_usize(v_sz_2031_);
lean_dec(v_sz_2031_);
v_i_boxed_2036_ = lean_unbox_usize(v_i_2032_);
lean_dec(v_i_2032_);
v_res_2037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_as_2030_, v_sz_boxed_2035_, v_i_boxed_2036_, v_b_2033_, v___y_2034_);
lean_dec_ref(v_as_2030_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(lean_object* v_acc_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_array_2043_; lean_object* v_idx_2044_; lean_object* v_pos_2046_; lean_object* v_idx_2047_; lean_object* v_err_2048_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_array_2043_ = lean_ctor_get(v_a_2042_, 0);
v_idx_2044_ = lean_ctor_get(v_a_2042_, 1);
lean_inc(v_idx_2044_);
v___x_2054_ = lean_byte_array_size(v_array_2043_);
v___x_2055_ = lean_nat_dec_lt(v_idx_2044_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_box(0);
lean_inc(v_idx_2044_);
v_pos_2046_ = v_a_2042_;
v_idx_2047_ = v_idx_2044_;
v_err_2048_ = v___x_2056_;
goto v___jp_2045_;
}
else
{
uint8_t v___x_2057_; uint8_t v_c_2058_; uint8_t v___x_2059_; 
v___x_2057_ = 10;
v_c_2058_ = lean_byte_array_fget(v_array_2043_, v_idx_2044_);
v___x_2059_ = lean_uint8_dec_eq(v_c_2058_, v___x_2057_);
if (v___x_2059_ == 0)
{
if (v___x_2055_ == 0)
{
goto v___jp_2052_;
}
else
{
lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2071_; 
lean_inc_ref(v_array_2043_);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_a_2042_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; lean_object* v_unused_2073_; 
v_unused_2072_ = lean_ctor_get(v_a_2042_, 1);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v_a_2042_, 0);
lean_dec(v_unused_2073_);
v___x_2061_ = v_a_2042_;
v_isShared_2062_ = v_isSharedCheck_2071_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v_a_2042_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2071_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v_it_x27_2066_; 
v___x_2063_ = lean_unsigned_to_nat(1u);
v___x_2064_ = lean_nat_add(v_idx_2044_, v___x_2063_);
lean_dec(v_idx_2044_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v___x_2064_);
v_it_x27_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_array_2043_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2064_);
v_it_x27_2066_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_box(v_c_2058_);
v___x_2068_ = lean_array_push(v_acc_2041_, v___x_2067_);
v_acc_2041_ = v___x_2068_;
v_a_2042_ = v_it_x27_2066_;
goto _start;
}
}
}
}
else
{
goto v___jp_2052_;
}
}
v___jp_2045_:
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_nat_dec_eq(v_idx_2044_, v_idx_2047_);
lean_dec(v_idx_2047_);
lean_dec(v_idx_2044_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
lean_dec_ref(v_acc_2041_);
v___x_2050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_pos_2046_);
lean_ctor_set(v___x_2050_, 1, v_err_2048_);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; 
lean_dec(v_err_2048_);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v_pos_2046_);
lean_ctor_set(v___x_2051_, 1, v_acc_2041_);
return v___x_2051_;
}
}
v___jp_2052_:
{
lean_object* v___x_2053_; 
v___x_2053_ = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1));
lean_inc(v_idx_2044_);
v_pos_2046_ = v_a_2042_;
v_idx_2047_ = v_idx_2044_;
v_err_2048_ = v___x_2053_;
goto v___jp_2045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(lean_object* v_a_2076_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_a_2076_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_pos_2078_; lean_object* v_res_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2126_; 
v_pos_2078_ = lean_ctor_get(v___x_2077_, 0);
v_res_2079_ = lean_ctor_get(v___x_2077_, 1);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2081_ = v___x_2077_;
v_isShared_2082_ = v_isSharedCheck_2126_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_res_2079_);
lean_inc(v_pos_2078_);
lean_dec(v___x_2077_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2126_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
uint8_t v___x_2083_; uint8_t v___x_2084_; uint8_t v___x_2085_; 
v___x_2083_ = 10;
v___x_2084_ = lean_unbox(v_res_2079_);
lean_dec(v_res_2079_);
v___x_2085_ = lean_uint8_dec_eq(v___x_2084_, v___x_2083_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_box(0);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v___x_2086_);
v___x_2088_ = v___x_2081_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_pos_2078_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_del_object(v___x_2081_);
v___x_2090_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0));
v___x_2091_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(v___x_2090_, v_pos_2078_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_pos_2092_; lean_object* v_res_2093_; lean_object* v___x_2094_; size_t v_sz_2095_; size_t v___x_2096_; lean_object* v___x_2097_; 
v_pos_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_pos_2092_);
v_res_2093_ = lean_ctor_get(v___x_2091_, 1);
lean_inc(v_res_2093_);
lean_dec_ref(v___x_2091_);
v___x_2094_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0));
v_sz_2095_ = lean_array_size(v_res_2093_);
v___x_2096_ = ((size_t)0ULL);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_res_2093_, v_sz_2095_, v___x_2096_, v___x_2094_, v_pos_2092_);
lean_dec(v_res_2093_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_pos_2098_; lean_object* v_res_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2107_; 
v_pos_2098_ = lean_ctor_get(v___x_2097_, 0);
v_res_2099_ = lean_ctor_get(v___x_2097_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2101_ = v___x_2097_;
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_res_2099_);
lean_inc(v_pos_2098_);
lean_dec(v___x_2097_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v_res_2099_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 1, v___x_2103_);
v___x_2105_ = v___x_2101_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_pos_2098_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
else
{
lean_object* v_pos_2108_; lean_object* v_err_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
v_pos_2108_ = lean_ctor_get(v___x_2097_, 0);
v_err_2109_ = lean_ctor_get(v___x_2097_, 1);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2097_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_err_2109_);
lean_inc(v_pos_2108_);
lean_dec(v___x_2097_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_pos_2108_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_err_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_pos_2117_; lean_object* v_err_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
v_pos_2117_ = lean_ctor_get(v___x_2091_, 0);
v_err_2118_ = lean_ctor_get(v___x_2091_, 1);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2091_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_err_2118_);
lean_inc(v_pos_2117_);
lean_dec(v___x_2091_);
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
}
}
else
{
lean_object* v_pos_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2135_; 
v_pos_2127_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; 
v_unused_2136_ = lean_ctor_get(v___x_2077_, 1);
lean_dec(v_unused_2136_);
v___x_2129_ = v___x_2077_;
v_isShared_2130_ = v_isSharedCheck_2135_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_pos_2127_);
lean_dec(v___x_2077_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2135_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = lean_box(0);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v___x_2131_);
v___x_2133_ = v___x_2129_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_pos_2127_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(lean_object* v_a_2137_){
_start:
{
lean_object* v_pos_2139_; lean_object* v_err_2140_; lean_object* v___x_2156_; 
lean_inc_ref(v_a_2137_);
v___x_2156_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(v_a_2137_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_res_2157_; lean_object* v_pos_2158_; uint32_t v_isutcnt_2159_; uint32_t v_isstdcnt_2160_; uint32_t v_leapcnt_2161_; uint32_t v_timecnt_2162_; uint32_t v_typecnt_2163_; uint32_t v_charcnt_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v_res_2157_ = lean_ctor_get(v___x_2156_, 1);
lean_inc(v_res_2157_);
v_pos_2158_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_pos_2158_);
lean_dec_ref(v___x_2156_);
v_isutcnt_2159_ = lean_ctor_get_uint32(v_res_2157_, 0);
v_isstdcnt_2160_ = lean_ctor_get_uint32(v_res_2157_, 4);
v_leapcnt_2161_ = lean_ctor_get_uint32(v_res_2157_, 8);
v_timecnt_2162_ = lean_ctor_get_uint32(v_res_2157_, 12);
v_typecnt_2163_ = lean_ctor_get_uint32(v_res_2157_, 16);
v_charcnt_2164_ = lean_ctor_get_uint32(v_res_2157_, 20);
v___x_2165_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64), 1, 0);
lean_inc_ref(v___x_2165_);
v___x_2166_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_2165_, v_timecnt_2162_, v_pos_2158_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_pos_2167_; lean_object* v_res_2168_; lean_object* v___x_2169_; 
v_pos_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_pos_2167_);
v_res_2168_ = lean_ctor_get(v___x_2166_, 1);
lean_inc(v_res_2168_);
lean_dec_ref(v___x_2166_);
v___x_2169_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_2162_, v_pos_2167_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_pos_2170_; lean_object* v_res_2171_; lean_object* v___x_2172_; 
v_pos_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_pos_2170_);
v_res_2171_ = lean_ctor_get(v___x_2169_, 1);
lean_inc(v_res_2171_);
lean_dec_ref(v___x_2169_);
v___x_2172_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_2163_, v_pos_2170_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_pos_2173_; lean_object* v_res_2174_; lean_object* v___x_2175_; 
v_pos_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_pos_2173_);
v_res_2174_ = lean_ctor_get(v___x_2172_, 1);
lean_inc(v_res_2174_);
lean_dec_ref(v___x_2172_);
v___x_2175_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_2174_, v_charcnt_2164_, v_pos_2173_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_pos_2176_; lean_object* v_res_2177_; lean_object* v___x_2178_; 
v_pos_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_pos_2176_);
v_res_2177_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_res_2177_);
lean_dec_ref(v___x_2175_);
v___x_2178_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_2165_, v_leapcnt_2161_, v_pos_2176_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_pos_2179_; lean_object* v_res_2180_; lean_object* v___x_2181_; 
v_pos_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_pos_2179_);
v_res_2180_ = lean_ctor_get(v___x_2178_, 1);
lean_inc(v_res_2180_);
lean_dec_ref(v___x_2178_);
v___x_2181_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_2160_, v_pos_2179_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_pos_2182_; lean_object* v_res_2183_; lean_object* v___x_2184_; 
v_pos_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_pos_2182_);
v_res_2183_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_res_2183_);
lean_dec_ref(v___x_2181_);
v___x_2184_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_2159_, v_pos_2182_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_pos_2185_; lean_object* v_res_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2207_; 
v_pos_2185_ = lean_ctor_get(v___x_2184_, 0);
v_res_2186_ = lean_ctor_get(v___x_2184_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2188_ = v___x_2184_;
v_isShared_2189_ = v_isSharedCheck_2207_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_res_2186_);
lean_inc(v_pos_2185_);
lean_dec(v___x_2184_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2207_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(v_pos_2185_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_pos_2191_; lean_object* v_res_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v_a_2137_);
v_pos_2191_ = lean_ctor_get(v___x_2190_, 0);
v_res_2192_ = lean_ctor_get(v___x_2190_, 1);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2194_ = v___x_2190_;
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_res_2192_);
lean_inc(v_pos_2191_);
lean_dec(v___x_2190_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2196_, 0, v_res_2157_);
lean_ctor_set(v___x_2196_, 1, v_res_2168_);
lean_ctor_set(v___x_2196_, 2, v_res_2171_);
lean_ctor_set(v___x_2196_, 3, v_res_2174_);
lean_ctor_set(v___x_2196_, 4, v_res_2177_);
lean_ctor_set(v___x_2196_, 5, v_res_2180_);
lean_ctor_set(v___x_2196_, 6, v_res_2183_);
lean_ctor_set(v___x_2196_, 7, v_res_2186_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 1, v_res_2192_);
lean_ctor_set(v___x_2188_, 0, v___x_2196_);
v___x_2198_ = v___x_2188_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_res_2192_);
v___x_2198_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v___x_2199_);
v___x_2201_ = v___x_2194_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_pos_2191_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
lean_object* v_pos_2205_; lean_object* v_err_2206_; 
lean_del_object(v___x_2188_);
lean_dec(v_res_2186_);
lean_dec(v_res_2183_);
lean_dec(v_res_2180_);
lean_dec(v_res_2177_);
lean_dec(v_res_2174_);
lean_dec(v_res_2171_);
lean_dec(v_res_2168_);
lean_dec(v_res_2157_);
v_pos_2205_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_pos_2205_);
v_err_2206_ = lean_ctor_get(v___x_2190_, 1);
lean_inc(v_err_2206_);
lean_dec_ref(v___x_2190_);
v_pos_2139_ = v_pos_2205_;
v_err_2140_ = v_err_2206_;
goto v___jp_2138_;
}
}
}
else
{
lean_object* v_pos_2208_; lean_object* v_err_2209_; 
lean_dec(v_res_2183_);
lean_dec(v_res_2180_);
lean_dec(v_res_2177_);
lean_dec(v_res_2174_);
lean_dec(v_res_2171_);
lean_dec(v_res_2168_);
lean_dec(v_res_2157_);
v_pos_2208_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_pos_2208_);
v_err_2209_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_err_2209_);
lean_dec_ref(v___x_2184_);
v_pos_2139_ = v_pos_2208_;
v_err_2140_ = v_err_2209_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_pos_2210_; lean_object* v_err_2211_; 
lean_dec(v_res_2180_);
lean_dec(v_res_2177_);
lean_dec(v_res_2174_);
lean_dec(v_res_2171_);
lean_dec(v_res_2168_);
lean_dec(v_res_2157_);
v_pos_2210_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_pos_2210_);
v_err_2211_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_err_2211_);
lean_dec_ref(v___x_2181_);
v_pos_2139_ = v_pos_2210_;
v_err_2140_ = v_err_2211_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_pos_2212_; lean_object* v_err_2213_; 
lean_dec(v_res_2177_);
lean_dec(v_res_2174_);
lean_dec(v_res_2171_);
lean_dec(v_res_2168_);
lean_dec(v_res_2157_);
v_pos_2212_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_pos_2212_);
v_err_2213_ = lean_ctor_get(v___x_2178_, 1);
lean_inc(v_err_2213_);
lean_dec_ref(v___x_2178_);
v_pos_2139_ = v_pos_2212_;
v_err_2140_ = v_err_2213_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_pos_2214_; lean_object* v_err_2215_; 
lean_dec(v_res_2174_);
lean_dec(v_res_2171_);
lean_dec(v_res_2168_);
lean_dec_ref(v___x_2165_);
lean_dec(v_res_2157_);
v_pos_2214_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_pos_2214_);
v_err_2215_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_err_2215_);
lean_dec_ref(v___x_2175_);
v_pos_2139_ = v_pos_2214_;
v_err_2140_ = v_err_2215_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_pos_2216_; lean_object* v_err_2217_; 
lean_dec(v_res_2171_);
lean_dec(v_res_2168_);
lean_dec_ref(v___x_2165_);
lean_dec(v_res_2157_);
v_pos_2216_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_pos_2216_);
v_err_2217_ = lean_ctor_get(v___x_2172_, 1);
lean_inc(v_err_2217_);
lean_dec_ref(v___x_2172_);
v_pos_2139_ = v_pos_2216_;
v_err_2140_ = v_err_2217_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_pos_2218_; lean_object* v_err_2219_; 
lean_dec(v_res_2168_);
lean_dec_ref(v___x_2165_);
lean_dec(v_res_2157_);
v_pos_2218_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_pos_2218_);
v_err_2219_ = lean_ctor_get(v___x_2169_, 1);
lean_inc(v_err_2219_);
lean_dec_ref(v___x_2169_);
v_pos_2139_ = v_pos_2218_;
v_err_2140_ = v_err_2219_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_pos_2220_; lean_object* v_err_2221_; 
lean_dec_ref(v___x_2165_);
lean_dec(v_res_2157_);
v_pos_2220_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_pos_2220_);
v_err_2221_ = lean_ctor_get(v___x_2166_, 1);
lean_inc(v_err_2221_);
lean_dec_ref(v___x_2166_);
v_pos_2139_ = v_pos_2220_;
v_err_2140_ = v_err_2221_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_pos_2222_; lean_object* v_err_2223_; 
v_pos_2222_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_pos_2222_);
v_err_2223_ = lean_ctor_get(v___x_2156_, 1);
lean_inc(v_err_2223_);
lean_dec_ref(v___x_2156_);
v_pos_2139_ = v_pos_2222_;
v_err_2140_ = v_err_2223_;
goto v___jp_2138_;
}
v___jp_2138_:
{
lean_object* v_idx_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2154_; 
v_idx_2141_ = lean_ctor_get(v_a_2137_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_a_2137_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_a_2137_, 0);
lean_dec(v_unused_2155_);
v___x_2143_ = v_a_2137_;
v_isShared_2144_ = v_isSharedCheck_2154_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_idx_2141_);
lean_dec(v_a_2137_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2154_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_idx_2145_; uint8_t v___x_2146_; 
v_idx_2145_ = lean_ctor_get(v_pos_2139_, 1);
v___x_2146_ = lean_nat_dec_eq(v_idx_2141_, v_idx_2145_);
lean_dec(v_idx_2141_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2148_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set_tag(v___x_2143_, 1);
lean_ctor_set(v___x_2143_, 1, v_err_2140_);
lean_ctor_set(v___x_2143_, 0, v_pos_2139_);
v___x_2148_ = v___x_2143_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_pos_2139_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_err_2140_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_dec(v_err_2140_);
v___x_2150_ = lean_box(0);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 1, v___x_2150_);
lean_ctor_set(v___x_2143_, 0, v_pos_2139_);
v___x_2152_ = v___x_2143_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_pos_2139_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_parse(lean_object* v_a_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(v_a_2224_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_pos_2226_; lean_object* v_res_2227_; lean_object* v___x_2228_; 
v_pos_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_pos_2226_);
v_res_2227_ = lean_ctor_get(v___x_2225_, 1);
lean_inc(v_res_2227_);
lean_dec_ref(v___x_2225_);
v___x_2228_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(v_pos_2226_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_pos_2229_; lean_object* v_res_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2238_; 
v_pos_2229_ = lean_ctor_get(v___x_2228_, 0);
v_res_2230_ = lean_ctor_get(v___x_2228_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2232_ = v___x_2228_;
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_res_2230_);
lean_inc(v_pos_2229_);
lean_dec(v___x_2228_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_res_2227_);
lean_ctor_set(v___x_2234_, 1, v_res_2230_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v___x_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_pos_2229_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
else
{
lean_object* v_pos_2239_; lean_object* v_err_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_res_2227_);
v_pos_2239_ = lean_ctor_get(v___x_2228_, 0);
v_err_2240_ = lean_ctor_get(v___x_2228_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2228_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_err_2240_);
lean_inc(v_pos_2239_);
lean_dec(v___x_2228_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_pos_2239_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_err_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_pos_2248_; lean_object* v_err_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
v_pos_2248_ = lean_ctor_get(v___x_2225_, 0);
v_err_2249_ = lean_ctor_get(v___x_2225_, 1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2225_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_err_2249_);
lean_inc(v_pos_2248_);
lean_dec(v___x_2225_);
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
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_TzIf(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_TimeZone_TZif_instInhabitedHeader_default = _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default);
l_Std_Time_TimeZone_TZif_instInhabitedHeader = _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedHeader);
l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default = _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default);
l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType = _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType);
l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default = _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default);
l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond = _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond);
l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default = _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default);
l_Std_Time_TimeZone_TZif_instInhabitedTZifV1 = _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1);
l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default = _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default);
l_Std_Time_TimeZone_TZif_instInhabitedTZifV2 = _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV2);
l_Std_Time_TimeZone_TZif_instInhabitedTZif_default = _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZif_default);
l_Std_Time_TimeZone_TZif_instInhabitedTZif = _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif();
lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZif);
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
