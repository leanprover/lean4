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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static uint8_t _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0(void){
_start:
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_uint8_of_nat(v___x_320_);
return v___x_321_;
}
}
static uint32_t _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1(void){
_start:
{
lean_object* v___x_322_; uint32_t v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_uint32_of_nat(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2(void){
_start:
{
uint32_t v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_uint32_once(&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1, &l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1);
v___x_325_ = lean_uint8_once(&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0);
v___x_326_ = lean_alloc_ctor(0, 0, 25);
lean_ctor_set_uint8(v___x_326_, 24, v___x_325_);
lean_ctor_set_uint32(v___x_326_, 0, v___x_324_);
lean_ctor_set_uint32(v___x_326_, 4, v___x_324_);
lean_ctor_set_uint32(v___x_326_, 8, v___x_324_);
lean_ctor_set_uint32(v___x_326_, 12, v___x_324_);
lean_ctor_set_uint32(v___x_326_, 16, v___x_324_);
lean_ctor_set_uint32(v___x_326_, 20, v___x_324_);
return v___x_326_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2, &l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2);
return v___x_327_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_Time_TimeZone_TZif_instInhabitedHeader_default;
return v___x_328_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(13u);
v___x_339_ = lean_nat_to_int(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(9u);
v___x_344_ = lean_nat_to_int(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(21u);
v___x_349_ = lean_nat_to_int(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_nat_to_int(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(lean_object* v_x_352_){
_start:
{
lean_object* v_gmtOffset_353_; uint8_t v_isDst_354_; uint8_t v_abbreviationIndex_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___y_360_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_gmtOffset_353_ = lean_ctor_get(v_x_352_, 0);
v_isDst_354_ = lean_ctor_get_uint8(v_x_352_, sizeof(void*)*1);
v_abbreviationIndex_355_ = lean_ctor_get_uint8(v_x_352_, sizeof(void*)*1 + 1);
v___x_356_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_357_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3));
v___x_358_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_398_ = lean_int_dec_lt(v_gmtOffset_353_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = l_Int_repr(v_gmtOffset_353_);
v___x_400_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
v___y_360_ = v___x_400_;
goto v___jp_359_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = l_Int_repr(v_gmtOffset_353_);
v___x_402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
v___x_403_ = l_Repr_addAppParen(v___x_402_, v___x_396_);
v___y_360_ = v___x_403_;
goto v___jp_359_;
}
v___jp_359_:
{
lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_361_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_358_);
lean_ctor_set(v___x_361_, 1, v___y_360_);
v___x_362_ = 0;
v___x_363_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*1, v___x_362_);
v___x_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_357_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_box(1);
v___x_368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6));
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_356_);
v___x_372_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7);
v___x_373_ = l_Bool_repr___redArg(v_isDst_354_);
v___x_374_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*1, v___x_362_);
v___x_376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_371_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_365_);
v___x_378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v___x_367_);
v___x_379_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9));
v___x_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_356_);
v___x_382_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10);
v___x_383_ = lean_uint8_to_nat(v_abbreviationIndex_355_);
v___x_384_ = l_Nat_reprFast(v___x_383_);
v___x_385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
v___x_386_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_382_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*1, v___x_362_);
v___x_388_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_381_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_390_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_388_);
v___x_392_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_391_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_389_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*1, v___x_362_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___boxed(lean_object* v_x_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_x_404_);
lean_dec_ref(v_x_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(lean_object* v_x_406_, lean_object* v_prec_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_x_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___boxed(lean_object* v_x_409_, lean_object* v_prec_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(v_x_409_, v_prec_410_);
lean_dec(v_prec_410_);
lean_dec_ref(v_x_409_);
return v_res_411_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0(void){
_start:
{
uint8_t v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = lean_uint8_once(&l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0);
v___x_415_ = 0;
v___x_416_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_417_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_415_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1 + 1, v___x_414_);
return v___x_417_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default(void){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0);
return v___x_418_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType(void){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default;
return v___x_419_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(18u);
v___x_430_ = lean_nat_to_int(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(14u);
v___x_435_ = lean_nat_to_int(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(lean_object* v_x_436_){
_start:
{
lean_object* v_transitionTime_437_; lean_object* v_correction_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_492_; 
v_transitionTime_437_ = lean_ctor_get(v_x_436_, 0);
v_correction_438_ = lean_ctor_get(v_x_436_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_492_ == 0)
{
v___x_440_ = v_x_436_;
v_isShared_441_ = v_isSharedCheck_492_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_correction_438_);
lean_inc(v_transitionTime_437_);
lean_dec(v_x_436_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_492_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint8_t v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___y_463_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_459_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_460_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3));
v___x_461_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_486_ = lean_int_dec_lt(v_transitionTime_437_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = l_Int_repr(v_transitionTime_437_);
lean_dec(v_transitionTime_437_);
v___x_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___y_463_ = v___x_488_;
goto v___jp_462_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = l_Int_repr(v_transitionTime_437_);
lean_dec(v_transitionTime_437_);
v___x_490_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
v___x_491_ = l_Repr_addAppParen(v___x_490_, v___x_484_);
v___y_463_ = v___x_491_;
goto v___jp_462_;
}
v___jp_442_:
{
lean_object* v___x_448_; 
lean_inc(v___y_444_);
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 4);
lean_ctor_set(v___x_440_, 1, v___y_446_);
lean_ctor_set(v___x_440_, 0, v___y_444_);
v___x_448_ = v___x_440_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___y_444_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___y_446_);
v___x_448_ = v_reuseFailAlloc_458_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_449_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*1, v___y_443_);
v___x_450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_450_, 0, v___y_445_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_452_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_450_);
v___x_454_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_451_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*1, v___y_443_);
return v___x_457_;
}
}
v___jp_462_:
{
lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_461_);
lean_ctor_set(v___x_464_, 1, v___y_463_);
v___x_465_ = 0;
v___x_466_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*1, v___x_465_);
v___x_467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_460_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = lean_box(1);
v___x_471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6));
v___x_473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_459_);
v___x_475_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_478_ = lean_int_dec_lt(v_correction_438_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = l_Int_repr(v_correction_438_);
lean_dec(v_correction_438_);
v___x_480_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
v___y_443_ = v___x_465_;
v___y_444_ = v___x_475_;
v___y_445_ = v___x_474_;
v___y_446_ = v___x_480_;
goto v___jp_442_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = l_Int_repr(v_correction_438_);
lean_dec(v_correction_438_);
v___x_482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___x_483_ = l_Repr_addAppParen(v___x_482_, v___x_476_);
v___y_443_ = v___x_465_;
v___y_444_ = v___x_475_;
v___y_445_ = v___x_474_;
v___y_446_ = v___x_483_;
goto v___jp_442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr(lean_object* v_x_493_, lean_object* v_prec_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_x_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___boxed(lean_object* v_x_496_, lean_object* v_prec_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr(v_x_496_, v_prec_497_);
lean_dec(v_prec_497_);
return v_res_498_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default(void){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0);
return v___x_503_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond(void){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default;
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_dec(v_x_505_);
return v_x_506_;
}
else
{
lean_object* v_head_508_; lean_object* v_tail_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_520_; 
v_head_508_ = lean_ctor_get(v_x_507_, 0);
v_tail_509_ = lean_ctor_get(v_x_507_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_507_);
if (v_isSharedCheck_520_ == 0)
{
v___x_511_ = v_x_507_;
v_isShared_512_ = v_isSharedCheck_520_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_tail_509_);
lean_inc(v_head_508_);
lean_dec(v_x_507_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_520_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
lean_inc(v_x_505_);
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 5);
lean_ctor_set(v___x_511_, 1, v_x_505_);
lean_ctor_set(v___x_511_, 0, v_x_506_);
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_x_506_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_x_505_);
v___x_514_ = v_reuseFailAlloc_519_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_unbox(v_head_508_);
lean_dec(v_head_508_);
v___x_516_ = l_Bool_repr___redArg(v___x_515_);
v___x_517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_514_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v_x_506_ = v___x_517_;
v_x_507_ = v_tail_509_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16(lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
lean_dec(v_x_521_);
return v_x_522_;
}
else
{
lean_object* v_head_524_; lean_object* v_tail_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_536_; 
v_head_524_ = lean_ctor_get(v_x_523_, 0);
v_tail_525_ = lean_ctor_get(v_x_523_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_523_);
if (v_isSharedCheck_536_ == 0)
{
v___x_527_ = v_x_523_;
v_isShared_528_ = v_isSharedCheck_536_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_tail_525_);
lean_inc(v_head_524_);
lean_dec(v_x_523_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_536_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
lean_inc(v_x_521_);
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 5);
lean_ctor_set(v___x_527_, 1, v_x_521_);
lean_ctor_set(v___x_527_, 0, v_x_522_);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_x_522_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_x_521_);
v___x_530_ = v_reuseFailAlloc_535_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_531_ = lean_unbox(v_head_524_);
lean_dec(v_head_524_);
v___x_532_ = l_Bool_repr___redArg(v___x_531_);
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_530_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(v_x_521_, v___x_533_, v_tail_525_);
return v___x_534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
if (lean_obj_tag(v_x_537_) == 0)
{
lean_object* v___x_539_; 
lean_dec(v_x_538_);
v___x_539_ = lean_box(0);
return v___x_539_;
}
else
{
lean_object* v_tail_540_; 
v_tail_540_ = lean_ctor_get(v_x_537_, 1);
if (lean_obj_tag(v_tail_540_) == 0)
{
lean_object* v_head_541_; uint8_t v___x_542_; lean_object* v___x_543_; 
lean_dec(v_x_538_);
v_head_541_ = lean_ctor_get(v_x_537_, 0);
lean_inc(v_head_541_);
lean_dec_ref(v_x_537_);
v___x_542_ = lean_unbox(v_head_541_);
lean_dec(v_head_541_);
v___x_543_ = l_Bool_repr___redArg(v___x_542_);
return v___x_543_;
}
else
{
lean_object* v_head_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
lean_inc(v_tail_540_);
v_head_544_ = lean_ctor_get(v_x_537_, 0);
lean_inc(v_head_544_);
lean_dec_ref(v_x_537_);
v___x_545_ = lean_unbox(v_head_544_);
lean_dec(v_head_544_);
v___x_546_ = l_Bool_repr___redArg(v___x_545_);
v___x_547_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16(v_x_538_, v___x_546_, v_tail_540_);
return v___x_547_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0));
v___x_554_ = lean_string_length(v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3);
v___x_556_ = lean_nat_to_int(v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(lean_object* v_xs_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_array_get_size(v_xs_564_);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_nat_dec_eq(v___x_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_568_ = lean_array_to_list(v_xs_564_);
v___x_569_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_570_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(v___x_568_, v___x_569_);
v___x_571_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_572_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_570_);
v___x_574_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_571_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = l_Std_Format_fill(v___x_576_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; 
lean_dec_ref(v_xs_564_);
v___x_578_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(lean_object* v___y_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = l_String_quote(v___y_579_);
v___x_581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_dec(v_x_582_);
return v_x_583_;
}
else
{
lean_object* v_head_585_; lean_object* v_tail_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_597_; 
v_head_585_ = lean_ctor_get(v_x_584_, 0);
v_tail_586_ = lean_ctor_get(v_x_584_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_597_ == 0)
{
v___x_588_ = v_x_584_;
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_tail_586_);
lean_inc(v_head_585_);
lean_dec(v_x_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
lean_inc(v_x_582_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 5);
lean_ctor_set(v___x_588_, 1, v_x_582_);
lean_ctor_set(v___x_588_, 0, v_x_583_);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_x_583_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_x_582_);
v___x_591_ = v_reuseFailAlloc_596_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = l_String_quote(v_head_585_);
v___x_593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___x_594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_591_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v_x_583_ = v___x_594_;
v_x_584_ = v_tail_586_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10(lean_object* v_x_598_, lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_dec(v_x_598_);
return v_x_599_;
}
else
{
lean_object* v_head_601_; lean_object* v_tail_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_613_; 
v_head_601_ = lean_ctor_get(v_x_600_, 0);
v_tail_602_ = lean_ctor_get(v_x_600_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_x_600_);
if (v_isSharedCheck_613_ == 0)
{
v___x_604_ = v_x_600_;
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_tail_602_);
lean_inc(v_head_601_);
lean_dec(v_x_600_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_613_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
lean_inc(v_x_598_);
if (v_isShared_605_ == 0)
{
lean_ctor_set_tag(v___x_604_, 5);
lean_ctor_set(v___x_604_, 1, v_x_598_);
lean_ctor_set(v___x_604_, 0, v_x_599_);
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_x_599_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_x_598_);
v___x_607_ = v_reuseFailAlloc_612_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_608_ = l_String_quote(v_head_601_);
v___x_609_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_607_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(v_x_598_, v___x_610_, v_tail_602_);
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
lean_object* v___x_616_; 
lean_dec(v_x_615_);
v___x_616_ = lean_box(0);
return v___x_616_;
}
else
{
lean_object* v_tail_617_; 
v_tail_617_ = lean_ctor_get(v_x_614_, 1);
if (lean_obj_tag(v_tail_617_) == 0)
{
lean_object* v_head_618_; lean_object* v___x_619_; 
lean_dec(v_x_615_);
v_head_618_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_head_618_);
lean_dec_ref(v_x_614_);
v___x_619_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(v_head_618_);
return v___x_619_;
}
else
{
lean_object* v_head_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
lean_inc(v_tail_617_);
v_head_620_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_head_620_);
lean_dec_ref(v_x_614_);
v___x_621_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(v_head_620_);
v___x_622_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10(v_x_615_, v___x_621_, v_tail_617_);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(lean_object* v_xs_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_624_ = lean_array_get_size(v_xs_623_);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_nat_dec_eq(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_627_ = lean_array_to_list(v_xs_623_);
v___x_628_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_629_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(v___x_627_, v___x_628_);
v___x_630_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_631_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_629_);
v___x_633_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_630_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Std_Format_fill(v___x_635_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; 
lean_dec_ref(v_xs_623_);
v___x_637_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
if (lean_obj_tag(v_x_640_) == 0)
{
lean_dec(v_x_638_);
return v_x_639_;
}
else
{
lean_object* v_head_641_; lean_object* v_tail_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_655_; 
v_head_641_ = lean_ctor_get(v_x_640_, 0);
v_tail_642_ = lean_ctor_get(v_x_640_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_640_);
if (v_isSharedCheck_655_ == 0)
{
v___x_644_ = v_x_640_;
v_isShared_645_ = v_isSharedCheck_655_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_tail_642_);
lean_inc(v_head_641_);
lean_dec(v_x_640_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_655_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
lean_inc(v_x_638_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 5);
lean_ctor_set(v___x_644_, 1, v_x_638_);
lean_ctor_set(v___x_644_, 0, v_x_639_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_x_639_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_x_638_);
v___x_647_ = v_reuseFailAlloc_654_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_648_ = lean_unbox(v_head_641_);
lean_dec(v_head_641_);
v___x_649_ = lean_uint8_to_nat(v___x_648_);
v___x_650_ = l_Nat_reprFast(v___x_649_);
v___x_651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_647_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v_x_639_ = v___x_652_;
v_x_640_ = v_tail_642_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_dec(v_x_656_);
return v_x_657_;
}
else
{
lean_object* v_head_659_; lean_object* v_tail_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_673_; 
v_head_659_ = lean_ctor_get(v_x_658_, 0);
v_tail_660_ = lean_ctor_get(v_x_658_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_673_ == 0)
{
v___x_662_ = v_x_658_;
v_isShared_663_ = v_isSharedCheck_673_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_tail_660_);
lean_inc(v_head_659_);
lean_dec(v_x_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_673_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
lean_inc(v_x_656_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 5);
lean_ctor_set(v___x_662_, 1, v_x_656_);
lean_ctor_set(v___x_662_, 0, v_x_657_);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_x_657_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_x_656_);
v___x_665_ = v_reuseFailAlloc_672_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
uint8_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_666_ = lean_unbox(v_head_659_);
lean_dec(v_head_659_);
v___x_667_ = lean_uint8_to_nat(v___x_666_);
v___x_668_ = l_Nat_reprFast(v___x_667_);
v___x_669_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
v___x_670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_665_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(v_x_656_, v___x_670_, v_tail_660_);
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(uint8_t v___y_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_uint8_to_nat(v___y_674_);
v___x_676_ = l_Nat_reprFast(v___x_675_);
v___x_677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0___boxed(lean_object* v___y_678_){
_start:
{
uint8_t v___y_1967__boxed_679_; lean_object* v_res_680_; 
v___y_1967__boxed_679_ = lean_unbox(v___y_678_);
v_res_680_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___y_1967__boxed_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
if (lean_obj_tag(v_x_681_) == 0)
{
lean_object* v___x_683_; 
lean_dec(v_x_682_);
v___x_683_ = lean_box(0);
return v___x_683_;
}
else
{
lean_object* v_tail_684_; 
v_tail_684_ = lean_ctor_get(v_x_681_, 1);
if (lean_obj_tag(v_tail_684_) == 0)
{
lean_object* v_head_685_; uint8_t v___x_686_; lean_object* v___x_687_; 
lean_dec(v_x_682_);
v_head_685_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_head_685_);
lean_dec_ref(v_x_681_);
v___x_686_ = lean_unbox(v_head_685_);
lean_dec(v_head_685_);
v___x_687_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_686_);
return v___x_687_;
}
else
{
lean_object* v_head_688_; uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_inc(v_tail_684_);
v_head_688_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_head_688_);
lean_dec_ref(v_x_681_);
v___x_689_ = lean_unbox(v_head_688_);
lean_dec(v_head_688_);
v___x_690_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_689_);
v___x_691_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(v_x_682_, v___x_690_, v_tail_684_);
return v___x_691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(lean_object* v_xs_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_693_ = lean_array_get_size(v_xs_692_);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_nat_dec_eq(v___x_693_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_696_ = lean_array_to_list(v_xs_692_);
v___x_697_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_698_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(v___x_696_, v___x_697_);
v___x_699_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_700_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_698_);
v___x_702_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_699_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Std_Format_fill(v___x_704_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; 
lean_dec_ref(v_xs_692_);
v___x_706_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(lean_object* v_x_707_, lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
lean_dec(v_x_707_);
return v_x_708_;
}
else
{
lean_object* v_head_710_; lean_object* v_tail_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_730_; 
v_head_710_ = lean_ctor_get(v_x_709_, 0);
v_tail_711_ = lean_ctor_get(v_x_709_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_709_);
if (v_isSharedCheck_730_ == 0)
{
v___x_713_ = v_x_709_;
v_isShared_714_ = v_isSharedCheck_730_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_tail_711_);
lean_inc(v_head_710_);
lean_dec(v_x_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_730_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
lean_inc(v_x_707_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 5);
lean_ctor_set(v___x_713_, 1, v_x_707_);
lean_ctor_set(v___x_713_, 0, v_x_708_);
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_x_708_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_x_707_);
v___x_716_ = v_reuseFailAlloc_729_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_719_ = lean_int_dec_lt(v_head_710_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = l_Int_repr(v_head_710_);
lean_dec(v_head_710_);
v___x_721_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_716_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v_x_708_ = v___x_722_;
v_x_709_ = v_tail_711_;
goto _start;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = l_Int_repr(v_head_710_);
lean_dec(v_head_710_);
v___x_725_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
v___x_726_ = l_Repr_addAppParen(v___x_725_, v___x_717_);
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_716_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v_x_708_ = v___x_727_;
v_x_709_ = v_tail_711_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 0)
{
lean_dec(v_x_731_);
return v_x_732_;
}
else
{
lean_object* v_head_734_; lean_object* v_tail_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_754_; 
v_head_734_ = lean_ctor_get(v_x_733_, 0);
v_tail_735_ = lean_ctor_get(v_x_733_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_754_ == 0)
{
v___x_737_ = v_x_733_;
v_isShared_738_ = v_isSharedCheck_754_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_tail_735_);
lean_inc(v_head_734_);
lean_dec(v_x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_754_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
lean_inc(v_x_731_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 5);
lean_ctor_set(v___x_737_, 1, v_x_731_);
lean_ctor_set(v___x_737_, 0, v_x_732_);
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_x_732_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_x_731_);
v___x_740_ = v_reuseFailAlloc_753_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_743_ = lean_int_dec_lt(v_head_734_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_744_ = l_Int_repr(v_head_734_);
lean_dec(v_head_734_);
v___x_745_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
v___x_746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_740_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_731_, v___x_746_, v_tail_735_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_748_ = l_Int_repr(v_head_734_);
lean_dec(v_head_734_);
v___x_749_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
v___x_750_ = l_Repr_addAppParen(v___x_749_, v___x_741_);
v___x_751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_740_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_731_, v___x_751_, v_tail_735_);
return v___x_752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(lean_object* v___y_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
v___x_758_ = lean_int_dec_lt(v___y_755_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = l_Int_repr(v___y_755_);
v___x_760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = l_Int_repr(v___y_755_);
v___x_762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___x_763_ = l_Repr_addAppParen(v___x_762_, v___x_756_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0___boxed(lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v___y_764_);
lean_dec(v___y_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v___x_768_; 
lean_dec(v_x_767_);
v___x_768_ = lean_box(0);
return v___x_768_;
}
else
{
lean_object* v_tail_769_; 
v_tail_769_ = lean_ctor_get(v_x_766_, 1);
if (lean_obj_tag(v_tail_769_) == 0)
{
lean_object* v_head_770_; lean_object* v___x_771_; 
lean_dec(v_x_767_);
v_head_770_ = lean_ctor_get(v_x_766_, 0);
lean_inc(v_head_770_);
lean_dec_ref(v_x_766_);
v___x_771_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_770_);
lean_dec(v_head_770_);
return v___x_771_;
}
else
{
lean_object* v_head_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
lean_inc(v_tail_769_);
v_head_772_ = lean_ctor_get(v_x_766_, 0);
lean_inc(v_head_772_);
lean_dec_ref(v_x_766_);
v___x_773_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_772_);
lean_dec(v_head_772_);
v___x_774_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(v_x_767_, v___x_773_, v_tail_769_);
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(lean_object* v_xs_775_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_776_ = lean_array_get_size(v_xs_775_);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_nat_dec_eq(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_779_ = lean_array_to_list(v_xs_775_);
v___x_780_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_781_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(v___x_779_, v___x_780_);
v___x_782_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_783_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v___x_781_);
v___x_785_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_782_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Std_Format_fill(v___x_787_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; 
lean_dec_ref(v_xs_775_);
v___x_789_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_dec(v_x_790_);
return v_x_791_;
}
else
{
lean_object* v_head_793_; lean_object* v_tail_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_804_; 
v_head_793_ = lean_ctor_get(v_x_792_, 0);
v_tail_794_ = lean_ctor_get(v_x_792_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_792_);
if (v_isSharedCheck_804_ == 0)
{
v___x_796_ = v_x_792_;
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_tail_794_);
lean_inc(v_head_793_);
lean_dec(v_x_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
lean_inc(v_x_790_);
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 5);
lean_ctor_set(v___x_796_, 1, v_x_790_);
lean_ctor_set(v___x_796_, 0, v_x_791_);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_x_791_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_x_790_);
v___x_799_ = v_reuseFailAlloc_803_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_793_);
lean_dec(v_head_793_);
v___x_801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v_x_791_ = v___x_801_;
v_x_792_ = v_tail_794_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_dec(v_x_805_);
return v_x_806_;
}
else
{
lean_object* v_head_808_; lean_object* v_tail_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_819_; 
v_head_808_ = lean_ctor_get(v_x_807_, 0);
v_tail_809_ = lean_ctor_get(v_x_807_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_807_);
if (v_isSharedCheck_819_ == 0)
{
v___x_811_ = v_x_807_;
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_tail_809_);
lean_inc(v_head_808_);
lean_dec(v_x_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
lean_inc(v_x_805_);
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 5);
lean_ctor_set(v___x_811_, 1, v_x_805_);
lean_ctor_set(v___x_811_, 0, v_x_806_);
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_x_806_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_x_805_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_808_);
lean_dec(v_head_808_);
v___x_816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(v_x_805_, v___x_816_, v_tail_809_);
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
lean_object* v___x_822_; 
lean_dec(v_x_821_);
v___x_822_ = lean_box(0);
return v___x_822_;
}
else
{
lean_object* v_tail_823_; 
v_tail_823_ = lean_ctor_get(v_x_820_, 1);
if (lean_obj_tag(v_tail_823_) == 0)
{
lean_object* v_head_824_; lean_object* v___x_825_; 
lean_dec(v_x_821_);
v_head_824_ = lean_ctor_get(v_x_820_, 0);
lean_inc(v_head_824_);
lean_dec_ref(v_x_820_);
v___x_825_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_824_);
lean_dec(v_head_824_);
return v___x_825_;
}
else
{
lean_object* v_head_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_inc(v_tail_823_);
v_head_826_ = lean_ctor_get(v_x_820_, 0);
lean_inc(v_head_826_);
lean_dec_ref(v_x_820_);
v___x_827_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_826_);
lean_dec(v_head_826_);
v___x_828_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(v_x_821_, v___x_827_, v_tail_823_);
return v___x_828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(lean_object* v_xs_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_830_ = lean_array_get_size(v_xs_829_);
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_nat_dec_eq(v___x_830_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_833_ = lean_array_to_list(v_xs_829_);
v___x_834_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_835_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(v___x_833_, v___x_834_);
v___x_836_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_837_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_835_);
v___x_839_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_836_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Std_Format_fill(v___x_841_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; 
lean_dec_ref(v_xs_829_);
v___x_843_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
if (lean_obj_tag(v_x_846_) == 0)
{
lean_dec(v_x_844_);
return v_x_845_;
}
else
{
lean_object* v_head_847_; lean_object* v_tail_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_858_; 
v_head_847_ = lean_ctor_get(v_x_846_, 0);
v_tail_848_ = lean_ctor_get(v_x_846_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_x_846_);
if (v_isSharedCheck_858_ == 0)
{
v___x_850_ = v_x_846_;
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_tail_848_);
lean_inc(v_head_847_);
lean_dec(v_x_846_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
lean_inc(v_x_844_);
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 5);
lean_ctor_set(v___x_850_, 1, v_x_844_);
lean_ctor_set(v___x_850_, 0, v_x_845_);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_x_845_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_x_844_);
v___x_853_ = v_reuseFailAlloc_857_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_847_);
v___x_855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v_x_845_ = v___x_855_;
v_x_846_ = v_tail_848_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_dec(v_x_859_);
return v_x_860_;
}
else
{
lean_object* v_head_862_; lean_object* v_tail_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_873_; 
v_head_862_ = lean_ctor_get(v_x_861_, 0);
v_tail_863_ = lean_ctor_get(v_x_861_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_x_861_);
if (v_isSharedCheck_873_ == 0)
{
v___x_865_ = v_x_861_;
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_tail_863_);
lean_inc(v_head_862_);
lean_dec(v_x_861_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
lean_inc(v_x_859_);
if (v_isShared_866_ == 0)
{
lean_ctor_set_tag(v___x_865_, 5);
lean_ctor_set(v___x_865_, 1, v_x_859_);
lean_ctor_set(v___x_865_, 0, v_x_860_);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_x_860_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_x_859_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_862_);
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(v_x_859_, v___x_870_, v_tail_863_);
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_874_) == 0)
{
lean_object* v___x_876_; 
lean_dec(v_x_875_);
v___x_876_ = lean_box(0);
return v___x_876_;
}
else
{
lean_object* v_tail_877_; 
v_tail_877_ = lean_ctor_get(v_x_874_, 1);
if (lean_obj_tag(v_tail_877_) == 0)
{
lean_object* v_head_878_; lean_object* v___x_879_; 
lean_dec(v_x_875_);
v_head_878_ = lean_ctor_get(v_x_874_, 0);
lean_inc(v_head_878_);
lean_dec_ref(v_x_874_);
v___x_879_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_878_);
return v___x_879_;
}
else
{
lean_object* v_head_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_inc(v_tail_877_);
v_head_880_ = lean_ctor_get(v_x_874_, 0);
lean_inc(v_head_880_);
lean_dec_ref(v_x_874_);
v___x_881_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_880_);
v___x_882_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(v_x_875_, v___x_881_, v_tail_877_);
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(lean_object* v_xs_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_884_ = lean_array_get_size(v_xs_883_);
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_nat_dec_eq(v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_887_ = lean_array_to_list(v_xs_883_);
v___x_888_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1));
v___x_889_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(v___x_887_, v___x_888_);
v___x_890_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
v___x_891_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5));
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v___x_889_);
v___x_893_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6));
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_890_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = l_Std_Format_fill(v___x_895_);
return v___x_896_;
}
else
{
lean_object* v___x_897_; 
lean_dec_ref(v_xs_883_);
v___x_897_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8));
return v___x_897_;
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_unsigned_to_nat(10u);
v___x_908_ = lean_nat_to_int(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_unsigned_to_nat(19u);
v___x_913_ = lean_nat_to_int(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(17u);
v___x_924_ = lean_nat_to_int(v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(15u);
v___x_929_ = lean_nat_to_int(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(lean_object* v_x_936_){
_start:
{
lean_object* v_header_937_; lean_object* v_transitionTimes_938_; lean_object* v_transitionIndices_939_; lean_object* v_localTimeTypes_940_; lean_object* v_abbreviations_941_; lean_object* v_leapSeconds_942_; lean_object* v_stdWallIndicators_943_; lean_object* v_utLocalIndicators_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_header_937_ = lean_ctor_get(v_x_936_, 0);
lean_inc_ref(v_header_937_);
v_transitionTimes_938_ = lean_ctor_get(v_x_936_, 1);
lean_inc_ref(v_transitionTimes_938_);
v_transitionIndices_939_ = lean_ctor_get(v_x_936_, 2);
lean_inc_ref(v_transitionIndices_939_);
v_localTimeTypes_940_ = lean_ctor_get(v_x_936_, 3);
lean_inc_ref(v_localTimeTypes_940_);
v_abbreviations_941_ = lean_ctor_get(v_x_936_, 4);
lean_inc_ref(v_abbreviations_941_);
v_leapSeconds_942_ = lean_ctor_get(v_x_936_, 5);
lean_inc_ref(v_leapSeconds_942_);
v_stdWallIndicators_943_ = lean_ctor_get(v_x_936_, 6);
lean_inc_ref(v_stdWallIndicators_943_);
v_utLocalIndicators_944_ = lean_ctor_get(v_x_936_, 7);
lean_inc_ref(v_utLocalIndicators_944_);
lean_dec_ref(v_x_936_);
v___x_945_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_946_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3));
v___x_947_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4);
v___x_948_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_header_937_);
lean_dec_ref(v_header_937_);
v___x_949_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = 0;
v___x_951_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1, v___x_950_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_946_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_box(1);
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6));
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_945_);
v___x_960_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7);
v___x_961_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(v_transitionTimes_938_);
v___x_962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*1, v___x_950_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_959_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_953_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_955_);
v___x_967_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9));
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_945_);
v___x_970_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10, &l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10);
v___x_971_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(v_transitionIndices_939_);
v___x_972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*1, v___x_950_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_969_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_953_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_955_);
v___x_977_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11));
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_945_);
v___x_980_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4);
v___x_981_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(v_localTimeTypes_940_);
v___x_982_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*1, v___x_950_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_979_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_953_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_955_);
v___x_987_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13));
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_945_);
v___x_990_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14);
v___x_991_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(v_abbreviations_941_);
v___x_992_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1, v___x_950_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_989_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_953_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_955_);
v___x_997_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16));
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_945_);
v___x_1000_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17);
v___x_1001_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(v_leapSeconds_942_);
v___x_1002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set_uint8(v___x_1003_, sizeof(void*)*1, v___x_950_);
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_999_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_953_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_955_);
v___x_1007_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19));
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_945_);
v___x_1010_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(v_stdWallIndicators_943_);
v___x_1011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_970_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*1, v___x_950_);
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1009_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_953_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_955_);
v___x_1016_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21));
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_945_);
v___x_1019_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(v_utLocalIndicators_944_);
v___x_1020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_970_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set_uint8(v___x_1021_, sizeof(void*)*1, v___x_950_);
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1018_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1024_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1022_);
v___x_1026_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1023_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set_uint8(v___x_1029_, sizeof(void*)*1, v___x_950_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(lean_object* v_x_1030_, lean_object* v_prec_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_x_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___boxed(lean_object* v_x_1033_, lean_object* v_prec_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(v_x_1033_, v_prec_1034_);
lean_dec(v_prec_1034_);
return v_res_1035_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0));
v___x_1041_ = l_Std_Time_TimeZone_TZif_instInhabitedHeader_default;
v___x_1042_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_1040_);
lean_ctor_set(v___x_1042_, 2, v___x_1040_);
lean_ctor_set(v___x_1042_, 3, v___x_1040_);
lean_ctor_set(v___x_1042_, 4, v___x_1040_);
lean_ctor_set(v___x_1042_, 5, v___x_1040_);
lean_ctor_set(v___x_1042_, 6, v___x_1040_);
lean_ctor_set(v___x_1042_, 7, v___x_1040_);
return v___x_1042_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default(void){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1, &l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1);
return v___x_1043_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1(void){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1));
return v___x_1053_;
}
else
{
lean_object* v_val_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1065_; 
v_val_1054_ = lean_ctor_get(v_x_1051_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1056_ = v_x_1051_;
v_isShared_1057_ = v_isSharedCheck_1065_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_val_1054_);
lean_dec(v_x_1051_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1065_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1058_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3));
v___x_1059_ = l_String_quote(v_val_1054_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set_tag(v___x_1056_, 3);
lean_ctor_set(v___x_1056_, 0, v___x_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1058_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = l_Repr_addAppParen(v___x_1062_, v_x_1052_);
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___boxed(lean_object* v_x_1066_, lean_object* v_x_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(v_x_1066_, v_x_1067_);
lean_dec(v_x_1067_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(lean_object* v_x_1081_){
_start:
{
lean_object* v_toTZifV1_1082_; lean_object* v_footer_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1117_; 
v_toTZifV1_1082_ = lean_ctor_get(v_x_1081_, 0);
v_footer_1083_ = lean_ctor_get(v_x_1081_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_x_1081_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1085_ = v_x_1081_;
v_isShared_1086_ = v_isSharedCheck_1117_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_footer_1083_);
lean_inc(v_toTZifV1_1082_);
lean_dec(v_x_1081_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1117_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1087_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_1088_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3));
v___x_1089_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14);
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_toTZifV1_1082_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 4);
lean_ctor_set(v___x_1085_, 1, v___x_1091_);
lean_ctor_set(v___x_1085_, 0, v___x_1089_);
v___x_1093_ = v___x_1085_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1094_ = 0;
v___x_1095_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1088_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_box(1);
v___x_1100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5));
v___x_1102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___x_1087_);
v___x_1104_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4);
v___x_1105_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(v_footer_1083_, v___x_1090_);
v___x_1106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*1, v___x_1094_);
v___x_1108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1103_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1110_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1108_);
v___x_1112_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1109_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set_uint8(v___x_1115_, sizeof(void*)*1, v___x_1094_);
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(lean_object* v_x_1118_, lean_object* v_prec_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_x_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___boxed(lean_object* v_x_1121_, lean_object* v_prec_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(v_x_1121_, v_prec_1122_);
lean_dec(v_prec_1122_);
return v_res_1123_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1, &l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default(void){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0);
return v___x_1129_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2(void){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default;
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1131_) == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1));
return v___x_1133_;
}
else
{
lean_object* v_val_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_val_1134_ = lean_ctor_get(v_x_1131_, 0);
lean_inc(v_val_1134_);
lean_dec_ref(v_x_1131_);
v___x_1135_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3));
v___x_1136_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_val_1134_);
v___x_1137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Repr_addAppParen(v___x_1137_, v_x_1132_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0___boxed(lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(v_x_1139_, v_x_1140_);
lean_dec(v_x_1140_);
return v_res_1141_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_unsigned_to_nat(6u);
v___x_1152_ = lean_nat_to_int(v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(lean_object* v_x_1156_){
_start:
{
lean_object* v_v1_1157_; lean_object* v_v2_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1191_; 
v_v1_1157_ = lean_ctor_get(v_x_1156_, 0);
v_v2_1158_ = lean_ctor_get(v_x_1156_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_x_1156_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1160_ = v_x_1156_;
v_isShared_1161_ = v_isSharedCheck_1191_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_v2_1158_);
lean_inc(v_v1_1157_);
lean_dec(v_x_1156_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1191_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1162_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5));
v___x_1163_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3));
v___x_1164_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4, &l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4);
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_v1_1157_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 4);
lean_ctor_set(v___x_1160_, 1, v___x_1166_);
lean_ctor_set(v___x_1160_, 0, v___x_1164_);
v___x_1168_ = v___x_1160_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1169_ = 0;
v___x_1170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set_uint8(v___x_1170_, sizeof(void*)*1, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1163_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9));
v___x_1173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_box(1);
v___x_1175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6));
v___x_1177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v___x_1162_);
v___x_1179_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(v_v2_1158_, v___x_1165_);
v___x_1180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1164_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*1, v___x_1169_);
v___x_1182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1178_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25, &l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once, _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25);
v___x_1184_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26));
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1182_);
v___x_1186_ = ((lean_object*)(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27));
v___x_1187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1183_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*1, v___x_1169_);
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr(lean_object* v_x_1192_, lean_object* v_prec_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(v_x_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_instReprTZif_repr___boxed(lean_object* v_x_1195_, lean_object* v_prec_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr(v_x_1195_, v_prec_1196_);
lean_dec(v_prec_1196_);
return v_res_1197_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___x_1200_);
return v___x_1202_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_obj_once(&l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0, &l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_once, _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0);
return v___x_1203_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif(void){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Std_Time_TimeZone_TZif_instInhabitedTZif_default;
return v___x_1204_;
}
}
static lean_object* _init_l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = l_instInhabitedUInt32;
v___x_1206_ = lean_box_uint32(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT uint32_t l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(lean_object* v_msg_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; uint32_t v___x_1210_; 
v___x_1208_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1;
v___x_1209_ = lean_panic_fn_borrowed(v___x_1208_, v_msg_1207_);
v___x_1210_ = lean_unbox_uint32(v___x_1209_);
lean_dec(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed(lean_object* v_msg_1211_){
_start:
{
uint32_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v_msg_1211_);
v_r_1213_ = lean_box_uint32(v_res_1212_);
return v_r_1213_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1217_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2));
v___x_1218_ = lean_unsigned_to_nat(2u);
v___x_1219_ = lean_unsigned_to_nat(181u);
v___x_1220_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1));
v___x_1221_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0));
v___x_1222_ = l_mkPanicMessageWithDecl(v___x_1221_, v___x_1220_, v___x_1219_, v___x_1218_, v___x_1217_);
return v___x_1222_;
}
}
LEAN_EXPORT uint32_t l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(lean_object* v_bs_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1224_ = lean_byte_array_size(v_bs_1223_);
v___x_1225_ = lean_unsigned_to_nat(4u);
v___x_1226_ = lean_nat_dec_eq(v___x_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; uint32_t v___x_1228_; 
v___x_1227_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3);
v___x_1228_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v___x_1227_);
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; uint8_t v___x_1230_; uint32_t v___x_1231_; uint32_t v___x_1232_; uint32_t v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; uint32_t v___x_1236_; uint32_t v___x_1237_; uint32_t v___x_1238_; uint32_t v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; uint32_t v___x_1242_; uint32_t v___x_1243_; uint32_t v___x_1244_; uint32_t v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; uint32_t v___x_1248_; uint32_t v___x_1249_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_byte_array_get(v_bs_1223_, v___x_1229_);
v___x_1231_ = lean_uint8_to_uint32(v___x_1230_);
v___x_1232_ = 24;
v___x_1233_ = lean_uint32_shift_left(v___x_1231_, v___x_1232_);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_byte_array_get(v_bs_1223_, v___x_1234_);
v___x_1236_ = lean_uint8_to_uint32(v___x_1235_);
v___x_1237_ = 16;
v___x_1238_ = lean_uint32_shift_left(v___x_1236_, v___x_1237_);
v___x_1239_ = lean_uint32_lor(v___x_1233_, v___x_1238_);
v___x_1240_ = lean_unsigned_to_nat(2u);
v___x_1241_ = lean_byte_array_get(v_bs_1223_, v___x_1240_);
v___x_1242_ = lean_uint8_to_uint32(v___x_1241_);
v___x_1243_ = 8;
v___x_1244_ = lean_uint32_shift_left(v___x_1242_, v___x_1243_);
v___x_1245_ = lean_uint32_lor(v___x_1239_, v___x_1244_);
v___x_1246_ = lean_unsigned_to_nat(3u);
v___x_1247_ = lean_byte_array_get(v_bs_1223_, v___x_1246_);
v___x_1248_ = lean_uint8_to_uint32(v___x_1247_);
v___x_1249_ = lean_uint32_lor(v___x_1245_, v___x_1248_);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___boxed(lean_object* v_bs_1250_){
_start:
{
uint32_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_1250_);
lean_dec_ref(v_bs_1250_);
v_r_1252_ = lean_box_uint32(v_res_1251_);
return v_r_1252_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_unsigned_to_nat(31u);
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = lean_nat_shiftl(v___x_1254_, v___x_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(lean_object* v_bs_1256_){
_start:
{
uint32_t v___x_1257_; lean_object* v_n_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1257_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_1256_);
v_n_1258_ = lean_uint32_to_nat(v___x_1257_);
v___x_1259_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0);
v___x_1260_ = lean_nat_dec_lt(v_n_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_cstr_to_nat("4294967296");
v___x_1262_ = lean_nat_sub(v___x_1261_, v_n_1258_);
lean_dec(v_n_1258_);
v___x_1263_ = l_Int_negOfNat(v___x_1262_);
lean_dec(v___x_1262_);
return v___x_1263_;
}
else
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_nat_to_int(v_n_1258_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___boxed(lean_object* v_bs_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(v_bs_1265_);
lean_dec_ref(v_bs_1265_);
return v_res_1266_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_unsigned_to_nat(63u);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = lean_nat_shiftl(v___x_1268_, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1(void){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(lean_object* v_bs_1271_){
_start:
{
uint64_t v___x_1272_; lean_object* v_n_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1272_ = l_ByteArray_toUInt64BE_x21(v_bs_1271_);
v_n_1273_ = lean_uint64_to_nat(v___x_1272_);
v___x_1274_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0);
v___x_1275_ = lean_nat_dec_lt(v_n_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1);
v___x_1277_ = lean_nat_sub(v___x_1276_, v_n_1273_);
lean_dec(v_n_1273_);
v___x_1278_ = l_Int_negOfNat(v___x_1277_);
lean_dec(v___x_1277_);
return v___x_1278_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_nat_to_int(v_n_1273_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___boxed(lean_object* v_bs_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(v_bs_1280_);
lean_dec_ref(v_bs_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(lean_object* v_upperBound_1282_, lean_object* v_p_1283_, lean_object* v_a_1284_, lean_object* v_b_1285_, lean_object* v___y_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_lt(v_a_1284_, v_upperBound_1282_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
lean_dec(v_a_1284_);
lean_dec_ref(v_p_1283_);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___y_1286_);
lean_ctor_set(v___x_1288_, 1, v_b_1285_);
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; 
lean_inc_ref(v_p_1283_);
v___x_1289_ = lean_apply_1(v_p_1283_, v___y_1286_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_pos_1290_; lean_object* v_res_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_pos_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_pos_1290_);
v_res_1291_ = lean_ctor_get(v___x_1289_, 1);
lean_inc(v_res_1291_);
lean_dec_ref(v___x_1289_);
v___x_1292_ = lean_array_push(v_b_1285_, v_res_1291_);
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_nat_add(v_a_1284_, v___x_1293_);
lean_dec(v_a_1284_);
v_a_1284_ = v___x_1294_;
v_b_1285_ = v___x_1292_;
v___y_1286_ = v_pos_1290_;
goto _start;
}
else
{
lean_object* v_pos_1296_; lean_object* v_err_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_b_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_p_1283_);
v_pos_1296_ = lean_ctor_get(v___x_1289_, 0);
v_err_1297_ = lean_ctor_get(v___x_1289_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1289_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_err_1297_);
lean_inc(v_pos_1296_);
lean_dec(v___x_1289_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_pos_1296_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_err_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg___boxed(lean_object* v_upperBound_1305_, lean_object* v_p_1306_, lean_object* v_a_1307_, lean_object* v_b_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_1305_, v_p_1306_, v_a_1307_, v_b_1308_, v___y_1309_);
lean_dec(v_upperBound_1305_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(lean_object* v_n_1313_, lean_object* v_p_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v___x_1316_; lean_object* v_result_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_unsigned_to_nat(0u);
v_result_1317_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0));
v___x_1318_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_n_1313_, v_p_1314_, v___x_1316_, v_result_1317_, v_a_1315_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___boxed(lean_object* v_n_1319_, lean_object* v_p_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v_n_1319_, v_p_1320_, v_a_1321_);
lean_dec(v_n_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(lean_object* v_00_u03b1_1323_, lean_object* v_n_1324_, lean_object* v_p_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v_n_1324_, v_p_1325_, v_a_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___boxed(lean_object* v_00_u03b1_1328_, lean_object* v_n_1329_, lean_object* v_p_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(v_00_u03b1_1328_, v_n_1329_, v_p_1330_, v_a_1331_);
lean_dec(v_n_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(lean_object* v_00_u03b1_1333_, lean_object* v_upperBound_1334_, lean_object* v_p_1335_, lean_object* v_inst_1336_, lean_object* v_R_1337_, lean_object* v_a_1338_, lean_object* v_b_1339_, lean_object* v_c_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_1334_, v_p_1335_, v_a_1338_, v_b_1339_, v___y_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_upperBound_1344_, lean_object* v_p_1345_, lean_object* v_inst_1346_, lean_object* v_R_1347_, lean_object* v_a_1348_, lean_object* v_b_1349_, lean_object* v_c_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(v_00_u03b1_1343_, v_upperBound_1344_, v_p_1345_, v_inst_1346_, v_R_1347_, v_a_1348_, v_b_1349_, v_c_1350_, v___y_1351_);
lean_dec(v_upperBound_1344_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu64(lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_unsigned_to_nat(8u);
v___x_1355_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1354_, v_a_1353_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_pos_1356_; lean_object* v_res_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1367_; 
v_pos_1356_ = lean_ctor_get(v___x_1355_, 0);
v_res_1357_ = lean_ctor_get(v___x_1355_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1359_ = v___x_1355_;
v_isShared_1360_ = v_isSharedCheck_1367_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_res_1357_);
lean_inc(v_pos_1356_);
lean_dec(v___x_1355_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1367_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; uint64_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1361_ = l_ByteSlice_toByteArray(v_res_1357_);
v___x_1362_ = l_ByteArray_toUInt64LE_x21(v___x_1361_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = lean_box_uint64(v___x_1362_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___x_1363_);
v___x_1365_ = v___x_1359_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_pos_1356_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v_pos_1368_; lean_object* v_err_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_pos_1368_ = lean_ctor_get(v___x_1355_, 0);
v_err_1369_ = lean_ctor_get(v___x_1355_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1355_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_err_1369_);
lean_inc(v_pos_1368_);
lean_dec(v___x_1355_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_pos_1368_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_err_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64(lean_object* v_a_1377_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_unsigned_to_nat(8u);
v___x_1379_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1378_, v_a_1377_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_pos_1380_; lean_object* v_res_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1390_; 
v_pos_1380_ = lean_ctor_get(v___x_1379_, 0);
v_res_1381_ = lean_ctor_get(v___x_1379_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1383_ = v___x_1379_;
v_isShared_1384_ = v_isSharedCheck_1390_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_res_1381_);
lean_inc(v_pos_1380_);
lean_dec(v___x_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1390_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = l_ByteSlice_toByteArray(v_res_1381_);
v___x_1386_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(v___x_1385_);
lean_dec_ref(v___x_1385_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1386_);
v___x_1388_ = v___x_1383_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_pos_1380_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
else
{
lean_object* v_pos_1391_; lean_object* v_err_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
v_pos_1391_ = lean_ctor_get(v___x_1379_, 0);
v_err_1392_ = lean_ctor_get(v___x_1379_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1379_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_err_1392_);
lean_inc(v_pos_1391_);
lean_dec(v___x_1379_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_pos_1391_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_err_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(lean_object* v_a_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_unsigned_to_nat(4u);
v___x_1402_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1401_, v_a_1400_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_pos_1403_; lean_object* v_res_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1414_; 
v_pos_1403_ = lean_ctor_get(v___x_1402_, 0);
v_res_1404_ = lean_ctor_get(v___x_1402_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1406_ = v___x_1402_;
v_isShared_1407_ = v_isSharedCheck_1414_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_res_1404_);
lean_inc(v_pos_1403_);
lean_dec(v___x_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1414_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; uint32_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1408_ = l_ByteSlice_toByteArray(v_res_1404_);
v___x_1409_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v___x_1408_);
lean_dec_ref(v___x_1408_);
v___x_1410_ = lean_box_uint32(v___x_1409_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v___x_1410_);
v___x_1412_ = v___x_1406_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_pos_1403_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_object* v_pos_1415_; lean_object* v_err_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_pos_1415_ = lean_ctor_get(v___x_1402_, 0);
v_err_1416_ = lean_ctor_get(v___x_1402_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1402_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_err_1416_);
lean_inc(v_pos_1415_);
lean_dec(v___x_1402_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_pos_1415_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_err_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(lean_object* v_a_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_unsigned_to_nat(4u);
v___x_1426_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1425_, v_a_1424_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_pos_1427_; lean_object* v_res_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1437_; 
v_pos_1427_ = lean_ctor_get(v___x_1426_, 0);
v_res_1428_ = lean_ctor_get(v___x_1426_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1430_ = v___x_1426_;
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_res_1428_);
lean_inc(v_pos_1427_);
lean_dec(v___x_1426_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1432_ = l_ByteSlice_toByteArray(v_res_1428_);
v___x_1433_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(v___x_1432_);
lean_dec_ref(v___x_1432_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 1, v___x_1433_);
v___x_1435_ = v___x_1430_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_pos_1427_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v_pos_1438_; lean_object* v_err_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_pos_1438_ = lean_ctor_get(v___x_1426_, 0);
v_err_1439_ = lean_ctor_get(v___x_1426_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1426_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_err_1439_);
lean_inc(v_pos_1438_);
lean_dec(v___x_1426_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_pos_1438_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_err_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(lean_object* v_a_1447_){
_start:
{
lean_object* v_array_1448_; lean_object* v_idx_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_array_1448_ = lean_ctor_get(v_a_1447_, 0);
v_idx_1449_ = lean_ctor_get(v_a_1447_, 1);
v___x_1450_ = lean_byte_array_size(v_array_1448_);
v___x_1451_ = lean_nat_dec_lt(v_idx_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_box(0);
v___x_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1453_, 0, v_a_1447_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
return v___x_1453_;
}
else
{
lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1465_; 
lean_inc(v_idx_1449_);
lean_inc_ref(v_array_1448_);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_a_1447_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; lean_object* v_unused_1467_; 
v_unused_1466_ = lean_ctor_get(v_a_1447_, 1);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_a_1447_, 0);
lean_dec(v_unused_1467_);
v___x_1455_ = v_a_1447_;
v_isShared_1456_ = v_isSharedCheck_1465_;
goto v_resetjp_1454_;
}
else
{
lean_dec(v_a_1447_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1465_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
uint8_t v_c_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_it_x27_1461_; 
v_c_1457_ = lean_byte_array_fget(v_array_1448_, v_idx_1449_);
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = lean_nat_add(v_idx_1449_, v___x_1458_);
lean_dec(v_idx_1449_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v___x_1459_);
v_it_x27_1461_ = v___x_1455_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_array_1448_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1459_);
v_it_x27_1461_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_box(v_c_1457_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_it_x27_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
return v___x_1463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_a_1468_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_pos_1470_; lean_object* v_res_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1488_; 
v_pos_1470_ = lean_ctor_get(v___x_1469_, 0);
v_res_1471_ = lean_ctor_get(v___x_1469_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1473_ = v___x_1469_;
v_isShared_1474_ = v_isSharedCheck_1488_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_res_1471_);
lean_inc(v_pos_1470_);
lean_dec(v___x_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1488_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
uint8_t v___x_1475_; uint8_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = 0;
v___x_1476_ = lean_unbox(v_res_1471_);
lean_dec(v_res_1471_);
v___x_1477_ = lean_uint8_dec_eq(v___x_1476_, v___x_1475_);
if (v___x_1477_ == 0)
{
uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1478_ = 1;
v___x_1479_ = lean_box(v___x_1478_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1479_);
v___x_1481_ = v___x_1473_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_pos_1470_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
else
{
uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1483_ = 0;
v___x_1484_ = lean_box(v___x_1483_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1484_);
v___x_1486_ = v___x_1473_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_pos_1470_);
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
else
{
lean_object* v_pos_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1497_; 
v_pos_1489_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v___x_1469_, 1);
lean_dec(v_unused_1498_);
v___x_1491_ = v___x_1469_;
v_isShared_1492_ = v_isSharedCheck_1497_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_pos_1489_);
lean_dec(v___x_1469_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1497_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1493_ = lean_box(0);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1493_);
v___x_1495_ = v___x_1491_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_pos_1489_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17));
v___x_1500_ = lean_string_to_utf8(v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(lean_object* v_a_1501_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0, &l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0_once, _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0);
v___x_1503_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_1502_, v_a_1501_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_pos_1504_; lean_object* v___x_1505_; 
v_pos_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_pos_1504_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_pos_1504_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_pos_1506_; lean_object* v_res_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_pos_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_pos_1506_);
v_res_1507_ = lean_ctor_get(v___x_1505_, 1);
lean_inc(v_res_1507_);
lean_dec_ref(v___x_1505_);
v___x_1508_ = lean_unsigned_to_nat(15u);
v___x_1509_ = l_Std_Internal_Parsec_ByteArray_take(v___x_1508_, v_pos_1506_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_pos_1510_; lean_object* v___x_1511_; 
v_pos_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_pos_1510_);
lean_dec_ref(v___x_1509_);
v___x_1511_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1510_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_pos_1512_; lean_object* v_res_1513_; lean_object* v___x_1514_; 
v_pos_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_pos_1512_);
v_res_1513_ = lean_ctor_get(v___x_1511_, 1);
lean_inc(v_res_1513_);
lean_dec_ref(v___x_1511_);
v___x_1514_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1512_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_pos_1515_; lean_object* v_res_1516_; lean_object* v___x_1517_; 
v_pos_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_pos_1515_);
v_res_1516_ = lean_ctor_get(v___x_1514_, 1);
lean_inc(v_res_1516_);
lean_dec_ref(v___x_1514_);
v___x_1517_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1515_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_pos_1518_; lean_object* v_res_1519_; lean_object* v___x_1520_; 
v_pos_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_pos_1518_);
v_res_1519_ = lean_ctor_get(v___x_1517_, 1);
lean_inc(v_res_1519_);
lean_dec_ref(v___x_1517_);
v___x_1520_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1518_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_pos_1521_; lean_object* v_res_1522_; lean_object* v___x_1523_; 
v_pos_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_pos_1521_);
v_res_1522_ = lean_ctor_get(v___x_1520_, 1);
lean_inc(v_res_1522_);
lean_dec_ref(v___x_1520_);
v___x_1523_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1521_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_pos_1524_; lean_object* v_res_1525_; lean_object* v___x_1526_; 
v_pos_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_pos_1524_);
v_res_1525_ = lean_ctor_get(v___x_1523_, 1);
lean_inc(v_res_1525_);
lean_dec_ref(v___x_1523_);
v___x_1526_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_1524_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_pos_1527_; lean_object* v_res_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1543_; 
v_pos_1527_ = lean_ctor_get(v___x_1526_, 0);
v_res_1528_ = lean_ctor_get(v___x_1526_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1530_ = v___x_1526_;
v_isShared_1531_ = v_isSharedCheck_1543_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_res_1528_);
lean_inc(v_pos_1527_);
lean_dec(v___x_1526_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1543_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; uint32_t v___x_1534_; uint32_t v___x_1535_; uint32_t v___x_1536_; uint32_t v___x_1537_; uint32_t v___x_1538_; uint32_t v___x_1539_; lean_object* v___x_1541_; 
v___x_1532_ = lean_alloc_ctor(0, 0, 25);
v___x_1533_ = lean_unbox(v_res_1507_);
lean_dec(v_res_1507_);
lean_ctor_set_uint8(v___x_1532_, 24, v___x_1533_);
v___x_1534_ = lean_unbox_uint32(v_res_1513_);
lean_dec(v_res_1513_);
lean_ctor_set_uint32(v___x_1532_, 0, v___x_1534_);
v___x_1535_ = lean_unbox_uint32(v_res_1516_);
lean_dec(v_res_1516_);
lean_ctor_set_uint32(v___x_1532_, 4, v___x_1535_);
v___x_1536_ = lean_unbox_uint32(v_res_1519_);
lean_dec(v_res_1519_);
lean_ctor_set_uint32(v___x_1532_, 8, v___x_1536_);
v___x_1537_ = lean_unbox_uint32(v_res_1522_);
lean_dec(v_res_1522_);
lean_ctor_set_uint32(v___x_1532_, 12, v___x_1537_);
v___x_1538_ = lean_unbox_uint32(v_res_1525_);
lean_dec(v_res_1525_);
lean_ctor_set_uint32(v___x_1532_, 16, v___x_1538_);
v___x_1539_ = lean_unbox_uint32(v_res_1528_);
lean_dec(v_res_1528_);
lean_ctor_set_uint32(v___x_1532_, 20, v___x_1539_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v___x_1532_);
v___x_1541_ = v___x_1530_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_pos_1527_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v___x_1532_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
else
{
lean_object* v_pos_1544_; lean_object* v_err_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_res_1525_);
lean_dec(v_res_1522_);
lean_dec(v_res_1519_);
lean_dec(v_res_1516_);
lean_dec(v_res_1513_);
lean_dec(v_res_1507_);
v_pos_1544_ = lean_ctor_get(v___x_1526_, 0);
v_err_1545_ = lean_ctor_get(v___x_1526_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1526_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_err_1545_);
lean_inc(v_pos_1544_);
lean_dec(v___x_1526_);
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
lean_dec(v_res_1522_);
lean_dec(v_res_1519_);
lean_dec(v_res_1516_);
lean_dec(v_res_1513_);
lean_dec(v_res_1507_);
v_pos_1553_ = lean_ctor_get(v___x_1523_, 0);
v_err_1554_ = lean_ctor_get(v___x_1523_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1523_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_err_1554_);
lean_inc(v_pos_1553_);
lean_dec(v___x_1523_);
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
lean_dec(v_res_1519_);
lean_dec(v_res_1516_);
lean_dec(v_res_1513_);
lean_dec(v_res_1507_);
v_pos_1562_ = lean_ctor_get(v___x_1520_, 0);
v_err_1563_ = lean_ctor_get(v___x_1520_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1520_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_err_1563_);
lean_inc(v_pos_1562_);
lean_dec(v___x_1520_);
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
lean_dec(v_res_1516_);
lean_dec(v_res_1513_);
lean_dec(v_res_1507_);
v_pos_1571_ = lean_ctor_get(v___x_1517_, 0);
v_err_1572_ = lean_ctor_get(v___x_1517_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1517_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_err_1572_);
lean_inc(v_pos_1571_);
lean_dec(v___x_1517_);
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
lean_dec(v_res_1513_);
lean_dec(v_res_1507_);
v_pos_1580_ = lean_ctor_get(v___x_1514_, 0);
v_err_1581_ = lean_ctor_get(v___x_1514_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1514_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_err_1581_);
lean_inc(v_pos_1580_);
lean_dec(v___x_1514_);
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
lean_dec(v_res_1507_);
v_pos_1589_ = lean_ctor_get(v___x_1511_, 0);
v_err_1590_ = lean_ctor_get(v___x_1511_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1511_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_err_1590_);
lean_inc(v_pos_1589_);
lean_dec(v___x_1511_);
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
lean_object* v_pos_1598_; lean_object* v_err_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_res_1507_);
v_pos_1598_ = lean_ctor_get(v___x_1509_, 0);
v_err_1599_ = lean_ctor_get(v___x_1509_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1509_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_err_1599_);
lean_inc(v_pos_1598_);
lean_dec(v___x_1509_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_pos_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_err_1599_);
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
lean_object* v_pos_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1615_; 
v_pos_1607_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1505_, 1);
lean_dec(v_unused_1616_);
v___x_1609_ = v___x_1505_;
v_isShared_1610_ = v_isSharedCheck_1615_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_pos_1607_);
lean_dec(v___x_1505_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1615_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_box(0);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 1, v___x_1611_);
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_pos_1607_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_pos_1617_; lean_object* v_err_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
v_pos_1617_ = lean_ctor_get(v___x_1503_, 0);
v_err_1618_ = lean_ctor_get(v___x_1503_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1503_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_err_1618_);
lean_inc(v_pos_1617_);
lean_dec(v___x_1503_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_pos_1617_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_err_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType(lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(v_a_1626_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_pos_1628_; lean_object* v_res_1629_; lean_object* v___x_1630_; 
v_pos_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_pos_1628_);
v_res_1629_ = lean_ctor_get(v___x_1627_, 1);
lean_inc(v_res_1629_);
lean_dec_ref(v___x_1627_);
v___x_1630_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(v_pos_1628_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_pos_1631_; lean_object* v_res_1632_; lean_object* v___x_1633_; 
v_pos_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_pos_1631_);
v_res_1632_ = lean_ctor_get(v___x_1630_, 1);
lean_inc(v_res_1632_);
lean_dec_ref(v___x_1630_);
v___x_1633_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_pos_1631_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_pos_1634_; lean_object* v_res_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1645_; 
v_pos_1634_ = lean_ctor_get(v___x_1633_, 0);
v_res_1635_ = lean_ctor_get(v___x_1633_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1637_ = v___x_1633_;
v_isShared_1638_ = v_isSharedCheck_1645_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_res_1635_);
lean_inc(v_pos_1634_);
lean_dec(v___x_1633_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1645_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; uint8_t v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1643_; 
v___x_1639_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1639_, 0, v_res_1629_);
v___x_1640_ = lean_unbox(v_res_1632_);
lean_dec(v_res_1632_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*1, v___x_1640_);
v___x_1641_ = lean_unbox(v_res_1635_);
lean_dec(v_res_1635_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*1 + 1, v___x_1641_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 1, v___x_1639_);
v___x_1643_ = v___x_1637_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_pos_1634_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v___x_1639_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
else
{
lean_object* v_pos_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_res_1632_);
lean_dec(v_res_1629_);
v_pos_1646_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v___x_1633_, 1);
lean_dec(v_unused_1655_);
v___x_1648_ = v___x_1633_;
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_pos_1646_);
lean_dec(v___x_1633_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_box(0);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_pos_1646_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_object* v_pos_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_res_1629_);
v_pos_1656_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v___x_1630_, 1);
lean_dec(v_unused_1665_);
v___x_1658_ = v___x_1630_;
v_isShared_1659_ = v_isSharedCheck_1664_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_pos_1656_);
lean_dec(v___x_1630_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1664_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_box(0);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v___x_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_pos_1656_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_pos_1666_; lean_object* v_err_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
v_pos_1666_ = lean_ctor_get(v___x_1627_, 0);
v_err_1667_ = lean_ctor_get(v___x_1627_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1627_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_err_1667_);
lean_inc(v_pos_1666_);
lean_dec(v___x_1627_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_pos_1666_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_err_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond(lean_object* v_p_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_apply_1(v_p_1675_, v_a_1676_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_pos_1678_; lean_object* v_res_1679_; lean_object* v___x_1680_; 
v_pos_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_pos_1678_);
v_res_1679_ = lean_ctor_get(v___x_1677_, 1);
lean_inc(v_res_1679_);
lean_dec_ref(v___x_1677_);
v___x_1680_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(v_pos_1678_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_pos_1681_; lean_object* v_res_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1690_; 
v_pos_1681_ = lean_ctor_get(v___x_1680_, 0);
v_res_1682_ = lean_ctor_get(v___x_1680_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1684_ = v___x_1680_;
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_res_1682_);
lean_inc(v_pos_1681_);
lean_dec(v___x_1680_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_res_1679_);
lean_ctor_set(v___x_1686_, 1, v_res_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_pos_1681_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
lean_object* v_pos_1691_; lean_object* v_err_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_res_1679_);
v_pos_1691_ = lean_ctor_get(v___x_1680_, 0);
v_err_1692_ = lean_ctor_get(v___x_1680_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1680_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_err_1692_);
lean_inc(v_pos_1691_);
lean_dec(v___x_1680_);
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
else
{
lean_object* v_pos_1700_; lean_object* v_err_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
v_pos_1700_ = lean_ctor_get(v___x_1677_, 0);
v_err_1701_ = lean_ctor_get(v___x_1677_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1677_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_err_1701_);
lean_inc(v_pos_1700_);
lean_dec(v___x_1677_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_pos_1700_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_err_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(lean_object* v_size_1709_, uint32_t v_n_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_uint32_to_nat(v_n_1710_);
v___x_1713_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1712_, v_size_1709_, v_a_1711_);
lean_dec(v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes___boxed(lean_object* v_size_1714_, lean_object* v_n_1715_, lean_object* v_a_1716_){
_start:
{
uint32_t v_n_boxed_1717_; lean_object* v_res_1718_; 
v_n_boxed_1717_ = lean_unbox_uint32(v_n_1715_);
lean_dec(v_n_1715_);
v_res_1718_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v_size_1714_, v_n_boxed_1717_, v_a_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(uint32_t v_n_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_uint32_to_nat(v_n_1719_);
v___x_1722_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8), 1, 0);
v___x_1723_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1721_, v___x_1722_, v_a_1720_);
lean_dec(v___x_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices___boxed(lean_object* v_n_1724_, lean_object* v_a_1725_){
_start:
{
uint32_t v_n_boxed_1726_; lean_object* v_res_1727_; 
v_n_boxed_1726_ = lean_unbox_uint32(v_n_1724_);
lean_dec(v_n_1724_);
v_res_1727_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_n_boxed_1726_, v_a_1725_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(uint32_t v_n_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1730_ = lean_uint32_to_nat(v_n_1728_);
v___x_1731_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType), 1, 0);
v___x_1732_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1730_, v___x_1731_, v_a_1729_);
lean_dec(v___x_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes___boxed(lean_object* v_n_1733_, lean_object* v_a_1734_){
_start:
{
uint32_t v_n_boxed_1735_; lean_object* v_res_1736_; 
v_n_boxed_1735_ = lean_unbox_uint32(v_n_1733_);
lean_dec(v_n_1733_);
v_res_1736_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_n_boxed_1735_, v_a_1734_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(lean_object* v_upperBound_1738_, lean_object* v_res_1739_, lean_object* v_a_1740_, lean_object* v_b_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_nat_dec_lt(v_a_1740_, v_upperBound_1738_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_dec(v_a_1740_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___y_1742_);
lean_ctor_set(v___x_1744_, 1, v_b_1741_);
return v___x_1744_;
}
else
{
lean_object* v_fst_1745_; lean_object* v_snd_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1771_; 
v_fst_1745_ = lean_ctor_get(v_b_1741_, 0);
v_snd_1746_ = lean_ctor_get(v_b_1741_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_b_1741_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1748_ = v_b_1741_;
v_isShared_1749_ = v_isSharedCheck_1771_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snd_1746_);
lean_inc(v_fst_1745_);
lean_dec(v_b_1741_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1771_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; 
v___x_1750_ = l_instInhabitedUInt8;
v___x_1751_ = lean_box(v___x_1750_);
v___x_1752_ = lean_array_get(v___x_1751_, v_res_1739_, v_a_1740_);
lean_dec(v___x_1751_);
v___x_1753_ = 0;
v___x_1754_ = lean_unbox(v___x_1752_);
v___x_1755_ = lean_uint8_dec_eq(v___x_1754_, v___x_1753_);
if (v___x_1755_ == 0)
{
uint8_t v___x_1756_; uint32_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1756_ = lean_unbox(v___x_1752_);
lean_dec(v___x_1752_);
v___x_1757_ = lean_uint8_to_uint32(v___x_1756_);
v___x_1758_ = lean_string_push(v_snd_1746_, v___x_1757_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v___x_1758_);
v___x_1760_ = v___x_1748_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_fst_1745_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_unsigned_to_nat(1u);
v___x_1762_ = lean_nat_add(v_a_1740_, v___x_1761_);
lean_dec(v_a_1740_);
v_a_1740_ = v___x_1762_;
v_b_1741_ = v___x_1760_;
goto _start;
}
}
else
{
lean_object* v_current_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec(v___x_1752_);
lean_dec(v_a_1740_);
v_current_1765_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0));
v___x_1766_ = lean_array_push(v_fst_1745_, v_snd_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v_current_1765_);
lean_ctor_set(v___x_1748_, 0, v___x_1766_);
v___x_1768_ = v___x_1748_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_current_1765_);
v___x_1768_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___y_1742_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
return v___x_1769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___boxed(lean_object* v_upperBound_1772_, lean_object* v_res_1773_, lean_object* v_a_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_1772_, v_res_1773_, v_a_1774_, v_b_1775_, v___y_1776_);
lean_dec_ref(v_res_1773_);
lean_dec(v_upperBound_1772_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(lean_object* v___x_1778_, lean_object* v_res_1779_, lean_object* v_as_1780_, size_t v_sz_1781_, size_t v_i_1782_, lean_object* v_b_1783_, lean_object* v___y_1784_){
_start:
{
uint8_t v___x_1785_; 
v___x_1785_ = lean_usize_dec_lt(v_i_1782_, v_sz_1781_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___y_1784_);
lean_ctor_set(v___x_1786_, 1, v_b_1783_);
return v___x_1786_;
}
else
{
lean_object* v_a_1787_; uint8_t v_abbreviationIndex_1788_; lean_object* v_fst_1789_; lean_object* v_snd_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1813_; 
v_a_1787_ = lean_array_uget_borrowed(v_as_1780_, v_i_1782_);
v_abbreviationIndex_1788_ = lean_ctor_get_uint8(v_a_1787_, sizeof(void*)*1 + 1);
v_fst_1789_ = lean_ctor_get(v_b_1783_, 0);
v_snd_1790_ = lean_ctor_get(v_b_1783_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_b_1783_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1792_ = v_b_1783_;
v_isShared_1793_ = v_isSharedCheck_1813_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_snd_1790_);
lean_inc(v_fst_1789_);
lean_dec(v_b_1783_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1813_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1794_ = lean_uint8_to_nat(v_abbreviationIndex_1788_);
if (v_isShared_1793_ == 0)
{
v___x_1796_ = v___x_1792_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_fst_1789_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_snd_1790_);
v___x_1796_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v___x_1778_, v_res_1779_, v___x_1794_, v___x_1796_, v___y_1784_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_res_1798_; lean_object* v_pos_1799_; lean_object* v_fst_1800_; lean_object* v_snd_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1811_; 
v_res_1798_ = lean_ctor_get(v___x_1797_, 1);
lean_inc(v_res_1798_);
v_pos_1799_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_pos_1799_);
lean_dec_ref(v___x_1797_);
v_fst_1800_ = lean_ctor_get(v_res_1798_, 0);
v_snd_1801_ = lean_ctor_get(v_res_1798_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_res_1798_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1803_ = v_res_1798_;
v_isShared_1804_ = v_isSharedCheck_1811_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_snd_1801_);
lean_inc(v_fst_1800_);
lean_dec(v_res_1798_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1811_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_fst_1800_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_snd_1801_);
v___x_1806_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
size_t v___x_1807_; size_t v___x_1808_; 
v___x_1807_ = ((size_t)1ULL);
v___x_1808_ = lean_usize_add(v_i_1782_, v___x_1807_);
v_i_1782_ = v___x_1808_;
v_b_1783_ = v___x_1806_;
v___y_1784_ = v_pos_1799_;
goto _start;
}
}
}
else
{
return v___x_1797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1___boxed(lean_object* v___x_1814_, lean_object* v_res_1815_, lean_object* v_as_1816_, lean_object* v_sz_1817_, lean_object* v_i_1818_, lean_object* v_b_1819_, lean_object* v___y_1820_){
_start:
{
size_t v_sz_boxed_1821_; size_t v_i_boxed_1822_; lean_object* v_res_1823_; 
v_sz_boxed_1821_ = lean_unbox_usize(v_sz_1817_);
lean_dec(v_sz_1817_);
v_i_boxed_1822_ = lean_unbox_usize(v_i_1818_);
lean_dec(v_i_1818_);
v_res_1823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_1814_, v_res_1815_, v_as_1816_, v_sz_boxed_1821_, v_i_boxed_1822_, v_b_1819_, v___y_1820_);
lean_dec_ref(v_as_1816_);
lean_dec_ref(v_res_1815_);
lean_dec(v___x_1814_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(lean_object* v_times_1829_, uint32_t v_n_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = lean_uint32_to_nat(v_n_1830_);
v___x_1833_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8), 1, 0);
v___x_1834_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1832_, v___x_1833_, v_a_1831_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_pos_1835_; lean_object* v_res_1836_; lean_object* v___x_1837_; size_t v_sz_1838_; size_t v___x_1839_; lean_object* v___x_1840_; 
v_pos_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_pos_1835_);
v_res_1836_ = lean_ctor_get(v___x_1834_, 1);
lean_inc(v_res_1836_);
lean_dec_ref(v___x_1834_);
v___x_1837_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1));
v_sz_1838_ = lean_array_size(v_times_1829_);
v___x_1839_ = ((size_t)0ULL);
v___x_1840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_1832_, v_res_1836_, v_times_1829_, v_sz_1838_, v___x_1839_, v___x_1837_, v_pos_1835_);
lean_dec(v_res_1836_);
lean_dec(v___x_1832_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_res_1841_; lean_object* v_pos_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1850_; 
v_res_1841_ = lean_ctor_get(v___x_1840_, 1);
v_pos_1842_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1844_ = v___x_1840_;
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_res_1841_);
lean_inc(v_pos_1842_);
lean_dec(v___x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v_fst_1846_; lean_object* v___x_1848_; 
v_fst_1846_ = lean_ctor_get(v_res_1841_, 0);
lean_inc(v_fst_1846_);
lean_dec(v_res_1841_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v_fst_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_pos_1842_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_fst_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_object* v_pos_1851_; lean_object* v_err_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_pos_1851_ = lean_ctor_get(v___x_1840_, 0);
v_err_1852_ = lean_ctor_get(v___x_1840_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1840_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_err_1852_);
lean_inc(v_pos_1851_);
lean_dec(v___x_1840_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_pos_1851_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_err_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_pos_1860_; lean_object* v_err_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v___x_1832_);
v_pos_1860_ = lean_ctor_get(v___x_1834_, 0);
v_err_1861_ = lean_ctor_get(v___x_1834_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1834_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_err_1861_);
lean_inc(v_pos_1860_);
lean_dec(v___x_1834_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_pos_1860_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_err_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___boxed(lean_object* v_times_1869_, lean_object* v_n_1870_, lean_object* v_a_1871_){
_start:
{
uint32_t v_n_boxed_1872_; lean_object* v_res_1873_; 
v_n_boxed_1872_ = lean_unbox_uint32(v_n_1870_);
lean_dec(v_n_1870_);
v_res_1873_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_times_1869_, v_n_boxed_1872_, v_a_1871_);
lean_dec_ref(v_times_1869_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(lean_object* v_upperBound_1874_, lean_object* v_res_1875_, lean_object* v_inst_1876_, lean_object* v_R_1877_, lean_object* v_a_1878_, lean_object* v_b_1879_, lean_object* v_c_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_1874_, v_res_1875_, v_a_1878_, v_b_1879_, v___y_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___boxed(lean_object* v_upperBound_1883_, lean_object* v_res_1884_, lean_object* v_inst_1885_, lean_object* v_R_1886_, lean_object* v_a_1887_, lean_object* v_b_1888_, lean_object* v_c_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(v_upperBound_1883_, v_res_1884_, v_inst_1885_, v_R_1886_, v_a_1887_, v_b_1888_, v_c_1889_, v___y_1890_);
lean_dec_ref(v_res_1884_);
lean_dec(v_upperBound_1883_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(lean_object* v_size_1892_, uint32_t v_n_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_uint32_to_nat(v_n_1893_);
v___x_1896_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond), 2, 1);
lean_closure_set(v___x_1896_, 0, v_size_1892_);
v___x_1897_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1895_, v___x_1896_, v_a_1894_);
lean_dec(v___x_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds___boxed(lean_object* v_size_1898_, lean_object* v_n_1899_, lean_object* v_a_1900_){
_start:
{
uint32_t v_n_boxed_1901_; lean_object* v_res_1902_; 
v_n_boxed_1901_ = lean_unbox_uint32(v_n_1899_);
lean_dec(v_n_1899_);
v_res_1902_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v_size_1898_, v_n_boxed_1901_, v_a_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(uint32_t v_n_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = lean_uint32_to_nat(v_n_1903_);
v___x_1906_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool), 1, 0);
v___x_1907_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_1905_, v___x_1906_, v_a_1904_);
lean_dec(v___x_1905_);
return v___x_1907_;
}
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
lean_dec_ref(v___x_1913_);
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
lean_dec_ref(v___x_1923_);
v___x_1926_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_1919_, v_pos_1924_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_pos_1927_; lean_object* v_res_1928_; lean_object* v___x_1929_; 
v_pos_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_pos_1927_);
v_res_1928_ = lean_ctor_get(v___x_1926_, 1);
lean_inc(v_res_1928_);
lean_dec_ref(v___x_1926_);
v___x_1929_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_1920_, v_pos_1927_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_pos_1930_; lean_object* v_res_1931_; lean_object* v___x_1932_; 
v_pos_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_pos_1930_);
v_res_1931_ = lean_ctor_get(v___x_1929_, 1);
lean_inc(v_res_1931_);
lean_dec_ref(v___x_1929_);
v___x_1932_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_1931_, v_charcnt_1921_, v_pos_1930_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_pos_1933_; lean_object* v_res_1934_; lean_object* v___x_1935_; 
v_pos_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_pos_1933_);
v_res_1934_ = lean_ctor_get(v___x_1932_, 1);
lean_inc(v_res_1934_);
lean_dec_ref(v___x_1932_);
v___x_1935_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_1922_, v_leapcnt_1918_, v_pos_1933_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_pos_1936_; lean_object* v_res_1937_; lean_object* v___x_1938_; 
v_pos_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_pos_1936_);
v_res_1937_ = lean_ctor_get(v___x_1935_, 1);
lean_inc(v_res_1937_);
lean_dec_ref(v___x_1935_);
v___x_1938_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_1917_, v_pos_1936_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_pos_1939_; lean_object* v_res_1940_; lean_object* v___x_1941_; 
v_pos_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_pos_1939_);
v_res_1940_ = lean_ctor_get(v___x_1938_, 1);
lean_inc(v_res_1940_);
lean_dec_ref(v___x_1938_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(lean_object* v_as_2024_, size_t v_sz_2025_, size_t v_i_2026_, lean_object* v_b_2027_, lean_object* v___y_2028_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1___boxed(lean_object* v_as_2038_, lean_object* v_sz_2039_, lean_object* v_i_2040_, lean_object* v_b_2041_, lean_object* v___y_2042_){
_start:
{
size_t v_sz_boxed_2043_; size_t v_i_boxed_2044_; lean_object* v_res_2045_; 
v_sz_boxed_2043_ = lean_unbox_usize(v_sz_2039_);
lean_dec(v_sz_2039_);
v_i_boxed_2044_ = lean_unbox_usize(v_i_2040_);
lean_dec(v_i_2040_);
v_res_2045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_as_2038_, v_sz_boxed_2043_, v_i_boxed_2044_, v_b_2041_, v___y_2042_);
lean_dec_ref(v_as_2038_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(lean_object* v_acc_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_array_2051_; lean_object* v_idx_2052_; lean_object* v_pos_2054_; lean_object* v_idx_2055_; lean_object* v_err_2056_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_array_2051_ = lean_ctor_get(v_a_2050_, 0);
v_idx_2052_ = lean_ctor_get(v_a_2050_, 1);
lean_inc(v_idx_2052_);
v___x_2062_ = lean_byte_array_size(v_array_2051_);
v___x_2063_ = lean_nat_dec_lt(v_idx_2052_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_box(0);
lean_inc(v_idx_2052_);
v_pos_2054_ = v_a_2050_;
v_idx_2055_ = v_idx_2052_;
v_err_2056_ = v___x_2064_;
goto v___jp_2053_;
}
else
{
uint8_t v___x_2065_; uint8_t v_c_2066_; uint8_t v___x_2067_; 
v___x_2065_ = 10;
v_c_2066_ = lean_byte_array_fget(v_array_2051_, v_idx_2052_);
v___x_2067_ = lean_uint8_dec_eq(v_c_2066_, v___x_2065_);
if (v___x_2067_ == 0)
{
if (v___x_2063_ == 0)
{
goto v___jp_2060_;
}
else
{
lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2079_; 
lean_inc_ref(v_array_2051_);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_a_2050_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; lean_object* v_unused_2081_; 
v_unused_2080_ = lean_ctor_get(v_a_2050_, 1);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v_a_2050_, 0);
lean_dec(v_unused_2081_);
v___x_2069_ = v_a_2050_;
v_isShared_2070_ = v_isSharedCheck_2079_;
goto v_resetjp_2068_;
}
else
{
lean_dec(v_a_2050_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2079_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_it_x27_2074_; 
v___x_2071_ = lean_unsigned_to_nat(1u);
v___x_2072_ = lean_nat_add(v_idx_2052_, v___x_2071_);
lean_dec(v_idx_2052_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 1, v___x_2072_);
v_it_x27_2074_ = v___x_2069_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_array_2051_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2072_);
v_it_x27_2074_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_box(v_c_2066_);
v___x_2076_ = lean_array_push(v_acc_2049_, v___x_2075_);
v_acc_2049_ = v___x_2076_;
v_a_2050_ = v_it_x27_2074_;
goto _start;
}
}
}
}
else
{
goto v___jp_2060_;
}
}
v___jp_2053_:
{
uint8_t v___x_2057_; 
v___x_2057_ = lean_nat_dec_eq(v_idx_2052_, v_idx_2055_);
lean_dec(v_idx_2055_);
lean_dec(v_idx_2052_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; 
lean_dec_ref(v_acc_2049_);
lean_inc(v_err_2056_);
v___x_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2058_, 0, v_pos_2054_);
lean_ctor_set(v___x_2058_, 1, v_err_2056_);
return v___x_2058_;
}
else
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v_pos_2054_);
lean_ctor_set(v___x_2059_, 1, v_acc_2049_);
return v___x_2059_;
}
}
v___jp_2060_:
{
lean_object* v___x_2061_; 
v___x_2061_ = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1));
lean_inc(v_idx_2052_);
v_pos_2054_ = v_a_2050_;
v_idx_2055_ = v_idx_2052_;
v_err_2056_ = v___x_2061_;
goto v___jp_2053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(lean_object* v_a_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(v_a_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_pos_2086_; lean_object* v_res_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2134_; 
v_pos_2086_ = lean_ctor_get(v___x_2085_, 0);
v_res_2087_ = lean_ctor_get(v___x_2085_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2089_ = v___x_2085_;
v_isShared_2090_ = v_isSharedCheck_2134_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_res_2087_);
lean_inc(v_pos_2086_);
lean_dec(v___x_2085_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2134_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
uint8_t v___x_2091_; uint8_t v___x_2092_; uint8_t v___x_2093_; 
v___x_2091_ = 10;
v___x_2092_ = lean_unbox(v_res_2087_);
lean_dec(v_res_2087_);
v___x_2093_ = lean_uint8_dec_eq(v___x_2092_, v___x_2091_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = lean_box(0);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v___x_2094_);
v___x_2096_ = v___x_2089_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_pos_2086_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_del_object(v___x_2089_);
v___x_2098_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0));
v___x_2099_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(v___x_2098_, v_pos_2086_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_pos_2100_; lean_object* v_res_2101_; lean_object* v___x_2102_; size_t v_sz_2103_; size_t v___x_2104_; lean_object* v___x_2105_; 
v_pos_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_pos_2100_);
v_res_2101_ = lean_ctor_get(v___x_2099_, 1);
lean_inc(v_res_2101_);
lean_dec_ref(v___x_2099_);
v___x_2102_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0));
v_sz_2103_ = lean_array_size(v_res_2101_);
v___x_2104_ = ((size_t)0ULL);
v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_res_2101_, v_sz_2103_, v___x_2104_, v___x_2102_, v_pos_2100_);
lean_dec(v_res_2101_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_pos_2106_; lean_object* v_res_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2115_; 
v_pos_2106_ = lean_ctor_get(v___x_2105_, 0);
v_res_2107_ = lean_ctor_get(v___x_2105_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2109_ = v___x_2105_;
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_res_2107_);
lean_inc(v_pos_2106_);
lean_dec(v___x_2105_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_res_2107_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v___x_2111_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_pos_2106_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
else
{
lean_object* v_pos_2116_; lean_object* v_err_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
v_pos_2116_ = lean_ctor_get(v___x_2105_, 0);
v_err_2117_ = lean_ctor_get(v___x_2105_, 1);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2105_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_err_2117_);
lean_inc(v_pos_2116_);
lean_dec(v___x_2105_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_pos_2116_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_err_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_pos_2125_; lean_object* v_err_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
v_pos_2125_ = lean_ctor_get(v___x_2099_, 0);
v_err_2126_ = lean_ctor_get(v___x_2099_, 1);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2099_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_err_2126_);
lean_inc(v_pos_2125_);
lean_dec(v___x_2099_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_pos_2125_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_err_2126_);
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
}
else
{
lean_object* v_pos_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2143_; 
v_pos_2135_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v___x_2085_, 1);
lean_dec(v_unused_2144_);
v___x_2137_ = v___x_2085_;
v_isShared_2138_ = v_isSharedCheck_2143_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_pos_2135_);
lean_dec(v___x_2085_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2143_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = lean_box(0);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 1, v___x_2139_);
v___x_2141_ = v___x_2137_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_pos_2135_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(lean_object* v_a_2145_){
_start:
{
lean_object* v_pos_2147_; lean_object* v_err_2148_; lean_object* v___x_2164_; 
lean_inc_ref(v_a_2145_);
v___x_2164_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(v_a_2145_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_res_2165_; lean_object* v_pos_2166_; uint32_t v_isutcnt_2167_; uint32_t v_isstdcnt_2168_; uint32_t v_leapcnt_2169_; uint32_t v_timecnt_2170_; uint32_t v_typecnt_2171_; uint32_t v_charcnt_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_res_2165_ = lean_ctor_get(v___x_2164_, 1);
lean_inc(v_res_2165_);
v_pos_2166_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_pos_2166_);
lean_dec_ref(v___x_2164_);
v_isutcnt_2167_ = lean_ctor_get_uint32(v_res_2165_, 0);
v_isstdcnt_2168_ = lean_ctor_get_uint32(v_res_2165_, 4);
v_leapcnt_2169_ = lean_ctor_get_uint32(v_res_2165_, 8);
v_timecnt_2170_ = lean_ctor_get_uint32(v_res_2165_, 12);
v_typecnt_2171_ = lean_ctor_get_uint32(v_res_2165_, 16);
v_charcnt_2172_ = lean_ctor_get_uint32(v_res_2165_, 20);
v___x_2173_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64), 1, 0);
lean_inc_ref(v___x_2173_);
v___x_2174_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_2173_, v_timecnt_2170_, v_pos_2166_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_pos_2175_; lean_object* v_res_2176_; lean_object* v___x_2177_; 
v_pos_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_pos_2175_);
v_res_2176_ = lean_ctor_get(v___x_2174_, 1);
lean_inc(v_res_2176_);
lean_dec_ref(v___x_2174_);
v___x_2177_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_2170_, v_pos_2175_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_pos_2178_; lean_object* v_res_2179_; lean_object* v___x_2180_; 
v_pos_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_pos_2178_);
v_res_2179_ = lean_ctor_get(v___x_2177_, 1);
lean_inc(v_res_2179_);
lean_dec_ref(v___x_2177_);
v___x_2180_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_2171_, v_pos_2178_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_pos_2181_; lean_object* v_res_2182_; lean_object* v___x_2183_; 
v_pos_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_pos_2181_);
v_res_2182_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_res_2182_);
lean_dec_ref(v___x_2180_);
v___x_2183_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_2182_, v_charcnt_2172_, v_pos_2181_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_pos_2184_; lean_object* v_res_2185_; lean_object* v___x_2186_; 
v_pos_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_pos_2184_);
v_res_2185_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_res_2185_);
lean_dec_ref(v___x_2183_);
v___x_2186_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_2173_, v_leapcnt_2169_, v_pos_2184_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_pos_2187_; lean_object* v_res_2188_; lean_object* v___x_2189_; 
v_pos_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_pos_2187_);
v_res_2188_ = lean_ctor_get(v___x_2186_, 1);
lean_inc(v_res_2188_);
lean_dec_ref(v___x_2186_);
v___x_2189_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_2168_, v_pos_2187_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_pos_2190_; lean_object* v_res_2191_; lean_object* v___x_2192_; 
v_pos_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_pos_2190_);
v_res_2191_ = lean_ctor_get(v___x_2189_, 1);
lean_inc(v_res_2191_);
lean_dec_ref(v___x_2189_);
v___x_2192_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_2167_, v_pos_2190_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_pos_2193_; lean_object* v_res_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2215_; 
v_pos_2193_ = lean_ctor_get(v___x_2192_, 0);
v_res_2194_ = lean_ctor_get(v___x_2192_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2196_ = v___x_2192_;
v_isShared_2197_ = v_isSharedCheck_2215_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_res_2194_);
lean_inc(v_pos_2193_);
lean_dec(v___x_2192_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2215_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; 
v___x_2198_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(v_pos_2193_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_pos_2199_; lean_object* v_res_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref(v_a_2145_);
v_pos_2199_ = lean_ctor_get(v___x_2198_, 0);
v_res_2200_ = lean_ctor_get(v___x_2198_, 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2202_ = v___x_2198_;
v_isShared_2203_ = v_isSharedCheck_2212_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_res_2200_);
lean_inc(v_pos_2199_);
lean_dec(v___x_2198_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2212_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2204_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2204_, 0, v_res_2165_);
lean_ctor_set(v___x_2204_, 1, v_res_2176_);
lean_ctor_set(v___x_2204_, 2, v_res_2179_);
lean_ctor_set(v___x_2204_, 3, v_res_2182_);
lean_ctor_set(v___x_2204_, 4, v_res_2185_);
lean_ctor_set(v___x_2204_, 5, v_res_2188_);
lean_ctor_set(v___x_2204_, 6, v_res_2191_);
lean_ctor_set(v___x_2204_, 7, v_res_2194_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 1, v_res_2200_);
lean_ctor_set(v___x_2196_, 0, v___x_2204_);
v___x_2206_ = v___x_2196_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_res_2200_);
v___x_2206_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 1, v___x_2207_);
v___x_2209_ = v___x_2202_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_pos_2199_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_pos_2213_; lean_object* v_err_2214_; 
lean_del_object(v___x_2196_);
lean_dec(v_res_2194_);
lean_dec(v_res_2191_);
lean_dec(v_res_2188_);
lean_dec(v_res_2185_);
lean_dec(v_res_2182_);
lean_dec(v_res_2179_);
lean_dec(v_res_2176_);
lean_dec(v_res_2165_);
v_pos_2213_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_pos_2213_);
v_err_2214_ = lean_ctor_get(v___x_2198_, 1);
lean_inc(v_err_2214_);
lean_dec_ref(v___x_2198_);
v_pos_2147_ = v_pos_2213_;
v_err_2148_ = v_err_2214_;
goto v___jp_2146_;
}
}
}
else
{
lean_object* v_pos_2216_; lean_object* v_err_2217_; 
lean_dec(v_res_2191_);
lean_dec(v_res_2188_);
lean_dec(v_res_2185_);
lean_dec(v_res_2182_);
lean_dec(v_res_2179_);
lean_dec(v_res_2176_);
lean_dec(v_res_2165_);
v_pos_2216_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_pos_2216_);
v_err_2217_ = lean_ctor_get(v___x_2192_, 1);
lean_inc(v_err_2217_);
lean_dec_ref(v___x_2192_);
v_pos_2147_ = v_pos_2216_;
v_err_2148_ = v_err_2217_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_pos_2218_; lean_object* v_err_2219_; 
lean_dec(v_res_2188_);
lean_dec(v_res_2185_);
lean_dec(v_res_2182_);
lean_dec(v_res_2179_);
lean_dec(v_res_2176_);
lean_dec(v_res_2165_);
v_pos_2218_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_pos_2218_);
v_err_2219_ = lean_ctor_get(v___x_2189_, 1);
lean_inc(v_err_2219_);
lean_dec_ref(v___x_2189_);
v_pos_2147_ = v_pos_2218_;
v_err_2148_ = v_err_2219_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_pos_2220_; lean_object* v_err_2221_; 
lean_dec(v_res_2185_);
lean_dec(v_res_2182_);
lean_dec(v_res_2179_);
lean_dec(v_res_2176_);
lean_dec(v_res_2165_);
v_pos_2220_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_pos_2220_);
v_err_2221_ = lean_ctor_get(v___x_2186_, 1);
lean_inc(v_err_2221_);
lean_dec_ref(v___x_2186_);
v_pos_2147_ = v_pos_2220_;
v_err_2148_ = v_err_2221_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_pos_2222_; lean_object* v_err_2223_; 
lean_dec(v_res_2182_);
lean_dec(v_res_2179_);
lean_dec(v_res_2176_);
lean_dec_ref(v___x_2173_);
lean_dec(v_res_2165_);
v_pos_2222_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_pos_2222_);
v_err_2223_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_err_2223_);
lean_dec_ref(v___x_2183_);
v_pos_2147_ = v_pos_2222_;
v_err_2148_ = v_err_2223_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_pos_2224_; lean_object* v_err_2225_; 
lean_dec(v_res_2179_);
lean_dec(v_res_2176_);
lean_dec_ref(v___x_2173_);
lean_dec(v_res_2165_);
v_pos_2224_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_pos_2224_);
v_err_2225_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_err_2225_);
lean_dec_ref(v___x_2180_);
v_pos_2147_ = v_pos_2224_;
v_err_2148_ = v_err_2225_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_pos_2226_; lean_object* v_err_2227_; 
lean_dec(v_res_2176_);
lean_dec_ref(v___x_2173_);
lean_dec(v_res_2165_);
v_pos_2226_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_pos_2226_);
v_err_2227_ = lean_ctor_get(v___x_2177_, 1);
lean_inc(v_err_2227_);
lean_dec_ref(v___x_2177_);
v_pos_2147_ = v_pos_2226_;
v_err_2148_ = v_err_2227_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_pos_2228_; lean_object* v_err_2229_; 
lean_dec_ref(v___x_2173_);
lean_dec(v_res_2165_);
v_pos_2228_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_pos_2228_);
v_err_2229_ = lean_ctor_get(v___x_2174_, 1);
lean_inc(v_err_2229_);
lean_dec_ref(v___x_2174_);
v_pos_2147_ = v_pos_2228_;
v_err_2148_ = v_err_2229_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_pos_2230_; lean_object* v_err_2231_; 
v_pos_2230_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_pos_2230_);
v_err_2231_ = lean_ctor_get(v___x_2164_, 1);
lean_inc(v_err_2231_);
lean_dec_ref(v___x_2164_);
v_pos_2147_ = v_pos_2230_;
v_err_2148_ = v_err_2231_;
goto v___jp_2146_;
}
v___jp_2146_:
{
lean_object* v_idx_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2162_; 
v_idx_2149_ = lean_ctor_get(v_a_2145_, 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_a_2145_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; 
v_unused_2163_ = lean_ctor_get(v_a_2145_, 0);
lean_dec(v_unused_2163_);
v___x_2151_ = v_a_2145_;
v_isShared_2152_ = v_isSharedCheck_2162_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_idx_2149_);
lean_dec(v_a_2145_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2162_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v_idx_2153_; uint8_t v___x_2154_; 
v_idx_2153_ = lean_ctor_get(v_pos_2147_, 1);
v___x_2154_ = lean_nat_dec_eq(v_idx_2149_, v_idx_2153_);
lean_dec(v_idx_2149_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2156_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set_tag(v___x_2151_, 1);
lean_ctor_set(v___x_2151_, 1, v_err_2148_);
lean_ctor_set(v___x_2151_, 0, v_pos_2147_);
v___x_2156_ = v___x_2151_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_pos_2147_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_err_2148_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_dec(v_err_2148_);
v___x_2158_ = lean_box(0);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v___x_2158_);
lean_ctor_set(v___x_2151_, 0, v_pos_2147_);
v___x_2160_ = v___x_2151_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_pos_2147_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_TZif_parse(lean_object* v_a_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(v_a_2232_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_pos_2234_; lean_object* v_res_2235_; lean_object* v___x_2236_; 
v_pos_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_pos_2234_);
v_res_2235_ = lean_ctor_get(v___x_2233_, 1);
lean_inc(v_res_2235_);
lean_dec_ref(v___x_2233_);
v___x_2236_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(v_pos_2234_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_pos_2237_; lean_object* v_res_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2246_; 
v_pos_2237_ = lean_ctor_get(v___x_2236_, 0);
v_res_2238_ = lean_ctor_get(v___x_2236_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2240_ = v___x_2236_;
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_res_2238_);
lean_inc(v_pos_2237_);
lean_dec(v___x_2236_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v_res_2235_);
lean_ctor_set(v___x_2242_, 1, v_res_2238_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 1, v___x_2242_);
v___x_2244_ = v___x_2240_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_pos_2237_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
lean_object* v_pos_2247_; lean_object* v_err_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v_res_2235_);
v_pos_2247_ = lean_ctor_get(v___x_2236_, 0);
v_err_2248_ = lean_ctor_get(v___x_2236_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2236_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_err_2248_);
lean_inc(v_pos_2247_);
lean_dec(v___x_2236_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_pos_2247_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_err_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
else
{
lean_object* v_pos_2256_; lean_object* v_err_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
v_pos_2256_ = lean_ctor_get(v___x_2233_, 0);
v_err_2257_ = lean_ctor_get(v___x_2233_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2233_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_err_2257_);
lean_inc(v_pos_2256_);
lean_dec(v___x_2233_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_pos_2256_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_err_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
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
