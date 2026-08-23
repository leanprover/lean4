// Lean compiler output
// Module: Lake.Util.Version
// Imports: public import Lean.Data.Json public import Lake.Util.Date public import Init.Control.Do import Init.Data.String.TakeDrop import Lean.Data.Trie import Init.Data.String.Search import Init.Omega import Init.Data.String.Length
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_String_Slice_beq(lean_object*, lean_object*);
lean_object* l_Lake_Date_toString(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Date_ofString_x3f(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lake_instReprDate_repr___redArg(lean_object*);
uint8_t l_Lake_instDecidableEqDate_decEq(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t l_String_decLE(lean_object*, lean_object*);
uint8_t l_Lake_instOrdDate_ord(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Util_Version_0__Lake_isWildVer(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_isWildVer___boxed(lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "invalid "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = " version: expected numeral, got '"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = " version: expected numeral or wildcard, got '"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "invalid version: '-' suffix cannot be empty"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "unexpected characters at end of version: "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_instInhabitedSemVerCore_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedSemVerCore_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedSemVerCore_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedSemVerCore_default = (const lean_object*)&l_Lake_instInhabitedSemVerCore_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedSemVerCore = (const lean_object*)&l_Lake_instInhabitedSemVerCore_default___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprSemVerCore_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "major"};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprSemVerCore_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__9_value;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "minor"};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__11_value;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "patch"};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__12_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__13_value;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lake_instReprSemVerCore_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__15;
static lean_once_cell_t l_Lake_instReprSemVerCore_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__16;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__14_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__18 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprSemVerCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprSemVerCore_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprSemVerCore___closed__0 = (const lean_object*)&l_Lake_instReprSemVerCore___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprSemVerCore = (const lean_object*)&l_Lake_instReprSemVerCore___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instOrdSemVerCore_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdSemVerCore_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instOrdSemVerCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instOrdSemVerCore_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instOrdSemVerCore___closed__0 = (const lean_object*)&l_Lake_instOrdSemVerCore___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instOrdSemVerCore = (const lean_object*)&l_Lake_instOrdSemVerCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instLT;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instLE;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_SemVerCore_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_instMin___closed__0 = (const lean_object*)&l_Lake_SemVerCore_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_SemVerCore_instMin = (const lean_object*)&l_Lake_SemVerCore_instMin___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_SemVerCore_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_instMax___closed__0 = (const lean_object*)&l_Lake_SemVerCore_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_SemVerCore_instMax = (const lean_object*)&l_Lake_SemVerCore_instMax___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid version core: "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "incorrect number of components: got "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ", expected 3"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid patch version: expected numeral, got '"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid minor version: expected numeral, got '"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid major version: expected numeral, got '"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SemVerCore_parse(lean_object*);
static const lean_string_object l_Lake_SemVerCore_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_SemVerCore_toString___closed__0 = (const lean_object*)&l_Lake_SemVerCore_toString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_toString(lean_object*);
static const lean_closure_object l_Lake_SemVerCore_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_instToString___closed__0 = (const lean_object*)&l_Lake_SemVerCore_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_SemVerCore_instToString = (const lean_object*)&l_Lake_SemVerCore_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instToJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_SemVerCore_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_instToJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_instToJson___closed__0 = (const lean_object*)&l_Lake_SemVerCore_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_SemVerCore_instToJson = (const lean_object*)&l_Lake_SemVerCore_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instFromJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_SemVerCore_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_instFromJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_instFromJson___closed__0 = (const lean_object*)&l_Lake_SemVerCore_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_SemVerCore_instFromJson = (const lean_object*)&l_Lake_SemVerCore_instFromJson___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedStdVer_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedSemVerCore_default___closed__0_value),((lean_object*)&l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value)}};
static const lean_object* l_Lake_instInhabitedStdVer_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedStdVer_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedStdVer_default = (const lean_object*)&l_Lake_instInhabitedStdVer_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedStdVer = (const lean_object*)&l_Lake_instInhabitedStdVer_default___closed__0_value;
static const lean_string_object l_Lake_instReprStdVer_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toSemVerCore"};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprStdVer_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprStdVer_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprStdVer_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprStdVer_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprStdVer_repr___redArg___closed__4;
static const lean_string_object l_Lake_instReprStdVer_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "specialDescr"};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprStdVer_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprStdVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprStdVer_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprStdVer___closed__0 = (const lean_object*)&l_Lake_instReprStdVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprStdVer = (const lean_object*)&l_Lake_instReprStdVer___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_StdVer_instCoeSemVerCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instCoeSemVerCore___closed__0 = (const lean_object*)&l_Lake_StdVer_instCoeSemVerCore___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instCoeSemVerCore = (const lean_object*)&l_Lake_StdVer_instCoeSemVerCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_ofSemVerCore(lean_object*);
static const lean_closure_object l_Lake_StdVer_instCoeSemVerCore__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_ofSemVerCore, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instCoeSemVerCore__1___closed__0 = (const lean_object*)&l_Lake_StdVer_instCoeSemVerCore__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instCoeSemVerCore__1 = (const lean_object*)&l_Lake_StdVer_instCoeSemVerCore__1___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_StdVer_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_compare___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_StdVer_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instOrd___closed__0 = (const lean_object*)&l_Lake_StdVer_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instOrd = (const lean_object*)&l_Lake_StdVer_instOrd___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_instLT;
LEAN_EXPORT lean_object* l_Lake_StdVer_instLE;
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_StdVer_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instMin___closed__0 = (const lean_object*)&l_Lake_StdVer_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instMin = (const lean_object*)&l_Lake_StdVer_instMin___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_StdVer_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instMax___closed__0 = (const lean_object*)&l_Lake_StdVer_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instMax = (const lean_object*)&l_Lake_StdVer_instMax___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_parseM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_parse(lean_object*);
static const lean_string_object l_Lake_StdVer_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_StdVer_toString___closed__0 = (const lean_object*)&l_Lake_StdVer_toString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_toString(lean_object*);
static const lean_closure_object l_Lake_StdVer_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instToString___closed__0 = (const lean_object*)&l_Lake_StdVer_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instToString = (const lean_object*)&l_Lake_StdVer_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_instToJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_StdVer_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_instToJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instToJson___closed__0 = (const lean_object*)&l_Lake_StdVer_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instToJson = (const lean_object*)&l_Lake_StdVer_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_instFromJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_StdVer_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_instFromJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instFromJson___closed__0 = (const lean_object*)&l_Lake_StdVer_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instFromJson = (const lean_object*)&l_Lake_StdVer_instFromJson___closed__0_value;
static const lean_string_object l_Lake_toolchainFileName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lean-toolchain"};
static const lean_object* l_Lake_toolchainFileName___closed__0 = (const lean_object*)&l_Lake_toolchainFileName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_toolchainFileName = (const lean_object*)&l_Lake_toolchainFileName___closed__0_value;
static const lean_string_object l_Lake_ToolchainVer_defaultOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "leanprover/lean4"};
static const lean_object* l_Lake_ToolchainVer_defaultOrigin___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_defaultOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_defaultOrigin = (const lean_object*)&l_Lake_ToolchainVer_defaultOrigin___closed__0_value;
static const lean_string_object l_Lake_ToolchainVer_prOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "leanprover/lean4-pr-releases"};
static const lean_object* l_Lake_ToolchainVer_prOrigin___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_prOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_prOrigin = (const lean_object*)&l_Lake_ToolchainVer_prOrigin___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ToolchainVer_release___override___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "leanprover/lean4:v"};
static const lean_object* l_Lake_ToolchainVer_release___override___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_release___override___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release___override(lean_object*);
static const lean_string_object l_Lake_ToolchainVer_nightly___override___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "leanprover/lean4:nightly-"};
static const lean_object* l_Lake_ToolchainVer_nightly___override___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_nightly___override___closed__0_value;
static const lean_string_object l_Lake_ToolchainVer_nightly___override___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "-rev"};
static const lean_object* l_Lake_ToolchainVer_nightly___override___closed__1 = (const lean_object*)&l_Lake_ToolchainVer_nightly___override___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly___override(lean_object*, lean_object*);
static const lean_string_object l_Lake_ToolchainVer_pr___override___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "leanprover/lean4-pr-releases:pr-release-"};
static const lean_object* l_Lake_ToolchainVer_pr___override___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_pr___override___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr___override(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other___override(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override___boxed(lean_object*);
static const lean_string_object l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprToolchainVer_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lake.ToolchainVer.release"};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__0 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__1 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__1_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__2 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__2_value;
static lean_once_cell_t l_Lake_instReprToolchainVer_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprToolchainVer_repr___closed__3;
static lean_once_cell_t l_Lake_instReprToolchainVer_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprToolchainVer_repr___closed__4;
static const lean_string_object l_Lake_instReprToolchainVer_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lake.ToolchainVer.nightly"};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__5 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__5_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__5_value)}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__6 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__7 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__7_value;
static const lean_string_object l_Lake_instReprToolchainVer_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ToolchainVer.pr"};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__8 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__8_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__8_value)}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__9 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__9_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__10 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__10_value;
static const lean_string_object l_Lake_instReprToolchainVer_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lake.ToolchainVer.other"};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__11 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__11_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__11_value)}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__12 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__12_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__13 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__13_value;
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprToolchainVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprToolchainVer_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprToolchainVer___closed__0 = (const lean_object*)&l_Lake_instReprToolchainVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprToolchainVer = (const lean_object*)&l_Lake_instReprToolchainVer___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_ToolchainVer_instCoeLeanVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ToolchainVer_release___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ToolchainVer_instCoeLeanVer___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_instCoeLeanVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_instCoeLeanVer = (const lean_object*)&l_Lake_ToolchainVer_instCoeLeanVer___closed__0_value;
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "nightly-"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pr-release-"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ToolchainVer_ofString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "-nightly"};
static const lean_object* l_Lake_ToolchainVer_ofString___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_ofString___closed__0_value;
static lean_once_cell_t l_Lake_ToolchainVer_ofString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ToolchainVer_ofString___closed__1;
static lean_once_cell_t l_Lake_ToolchainVer_ofString___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ToolchainVer_ofString___closed__2;
static const lean_string_object l_Lake_ToolchainVer_ofString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l_Lake_ToolchainVer_ofString___closed__3 = (const lean_object*)&l_Lake_ToolchainVer_ofString___closed__3_value;
static lean_once_cell_t l_Lake_ToolchainVer_ofString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ToolchainVer_ofString___closed__4;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofString(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_ToolchainVer_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ToolchainVer_toString___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ToolchainVer_instToString___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_instToString = (const lean_object*)&l_Lake_ToolchainVer_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_ToolchainVer_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ToolchainVer_instToJson___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ToolchainVer_instToJson___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_instToJson = (const lean_object*)&l_Lake_ToolchainVer_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instFromJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_ToolchainVer_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ToolchainVer_instFromJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ToolchainVer_instFromJson___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_instFromJson = (const lean_object*)&l_Lake_ToolchainVer_instFromJson___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_blt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instLT;
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_ble(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ble___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instLE;
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_normalizeToolchain(lean_object*);
static const lean_closure_object l_Lake_instDecodeVersionSemVerCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instDecodeVersionSemVerCore___closed__0 = (const lean_object*)&l_Lake_instDecodeVersionSemVerCore___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instDecodeVersionSemVerCore = (const lean_object*)&l_Lake_instDecodeVersionSemVerCore___closed__0_value;
static const lean_closure_object l_Lake_instDecodeVersionStdVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instDecodeVersionStdVer___closed__0 = (const lean_object*)&l_Lake_instDecodeVersionStdVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instDecodeVersionStdVer = (const lean_object*)&l_Lake_instDecodeVersionStdVer___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instDecodeVersionToolchainVer___lam__0(lean_object*);
static const lean_closure_object l_Lake_instDecodeVersionToolchainVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instDecodeVersionToolchainVer___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instDecodeVersionToolchainVer___closed__0 = (const lean_object*)&l_Lake_instDecodeVersionToolchainVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instDecodeVersionToolchainVer = (const lean_object*)&l_Lake_instDecodeVersionToolchainVer___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.lt"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__0 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__1 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__1_value;
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.le"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__2 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__3 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__3_value;
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.gt"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__4 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__5 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__5_value;
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.ge"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__6 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__6_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__7 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__7_value;
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.eq"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__8 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__8_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__8_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__9 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__9_value;
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.ne"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__10 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__10_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__10_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__11 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprComparatorOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprComparatorOp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprComparatorOp___closed__0 = (const lean_object*)&l_Lake_instReprComparatorOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprComparatorOp = (const lean_object*)&l_Lake_instReprComparatorOp___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instInhabitedComparatorOp_default;
LEAN_EXPORT uint8_t l_Lake_instInhabitedComparatorOp;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≠"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!="};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≥"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ">="};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<="};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8_value;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "(internal) comparison operator parse produced invalid position"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "expected comparison operator"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString___boxed(lean_object*);
static const lean_closure_object l_Lake_ComparatorOp_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ComparatorOp_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ComparatorOp_instToString___closed__0 = (const lean_object*)&l_Lake_ComparatorOp_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ComparatorOp_instToString = (const lean_object*)&l_Lake_ComparatorOp_instToString___closed__0_value;
static const lean_string_object l_Lake_instReprVerComparator_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ver"};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprVerComparator_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprVerComparator_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprVerComparator_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprVerComparator_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__4;
static const lean_string_object l_Lake_instReprVerComparator_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "op"};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprVerComparator_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprVerComparator_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprVerComparator_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "includeSuffixes"};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprVerComparator_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lake_instReprVerComparator_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprVerComparator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprVerComparator_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprVerComparator___closed__0 = (const lean_object*)&l_Lake_instReprVerComparator___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprVerComparator = (const lean_object*)&l_Lake_instReprVerComparator___closed__0_value;
static const lean_ctor_object l_Lake_VerComparator_wild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedSemVerCore_default___closed__0_value),((lean_object*)&l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value)}};
static const lean_object* l_Lake_VerComparator_wild___closed__0 = (const lean_object*)&l_Lake_VerComparator_wild___closed__0_value;
static const lean_ctor_object l_Lake_VerComparator_wild___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_VerComparator_wild___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_VerComparator_wild___closed__1 = (const lean_object*)&l_Lake_VerComparator_wild___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_VerComparator_wild = (const lean_object*)&l_Lake_VerComparator_wild___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_VerComparator_instInhabited = (const lean_object*)&l_Lake_VerComparator_wild___closed__1_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "invalid comparison: expected version after `"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerComparator_parse(lean_object*);
LEAN_EXPORT uint8_t l_Lake_VerComparator_test(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerComparator_test___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerComparator_toString(lean_object*);
static const lean_closure_object l_Lake_VerComparator_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_VerComparator_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_VerComparator_instToString___closed__0 = (const lean_object*)&l_Lake_VerComparator_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_VerComparator_instToString = (const lean_object*)&l_Lake_VerComparator_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprVerRange_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toString"};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprVerRange_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprVerRange_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprVerRange_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprVerRange_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerRange_repr___redArg___closed__4;
static const lean_string_object l_Lake_instReprVerRange_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "clauses"};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprVerRange_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprVerRange_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerRange_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprVerRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprVerRange_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprVerRange___closed__0 = (const lean_object*)&l_Lake_instReprVerRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprVerRange = (const lean_object*)&l_Lake_instReprVerRange___closed__0_value;
static const lean_array_object l_Lake_instInhabitedVerRange_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedVerRange_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedVerRange_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedVerRange_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value),((lean_object*)&l_Lake_instInhabitedVerRange_default___closed__0_value)}};
static const lean_object* l_Lake_instInhabitedVerRange_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedVerRange_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedVerRange_default = (const lean_object*)&l_Lake_instInhabitedVerRange_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedVerRange = (const lean_object*)&l_Lake_instInhabitedVerRange_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_VerRange_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_VerRange_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_VerRange_instToString___closed__0 = (const lean_object*)&l_Lake_VerRange_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_VerRange_instToString = (const lean_object*)&l_Lake_VerRange_instToString___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<empty>"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " || "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerRange_ofClauses(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_appendRange(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "invalid tilde range: incorrect number of components: got "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", expected 1-3"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "invalid caret range: incorrect number of components: got "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "invalid caret range: `^0.0.0` is degenerate; use `=0.0.0` instead"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "invalid patch version: components after a wildcard must be wildcards"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 183, .m_capacity = 183, .m_length = 180, .m_data = "invalid version range: bare versions are not supported; if you want to pin a specific version, use '=' before the full version; otherwise, use '≥' to support it and future versions"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "invalid minor version: components after a wildcard must be wildcards"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "invalid wildcard range: incorrect number of components: got "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "invalid wildcard range: wildcard versions do not support suffixes"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "expected version range"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "expected '|' after first '|'"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1_value;
static const lean_array_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "invalid tilde range: expected version after `~`"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "invalid caret range: expected version after `^`"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerRange_parse(lean_object*);
static const lean_closure_object l_Lake_VerRange_instDecodeVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_VerRange_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_VerRange_instDecodeVersion___closed__0 = (const lean_object*)&l_Lake_VerRange_instDecodeVersion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_VerRange_instDecodeVersion = (const lean_object*)&l_Lake_VerRange_instDecodeVersion___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerRange_test___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(lean_object* v_s_1_, lean_object* v_cs_2_, lean_object* v_iniPos_3_, lean_object* v_p_4_){
_start:
{
lean_object* v___x_8_; uint8_t v_decide_9_; 
v___x_8_ = lean_string_utf8_byte_size(v_s_1_);
v_decide_9_ = lean_nat_dec_eq(v_p_4_, v___x_8_);
if (v_decide_9_ == 0)
{
uint32_t v_c_10_; uint8_t v___y_23_; uint32_t v___x_28_; uint8_t v___x_29_; 
v_c_10_ = lean_string_utf8_get_fast(v_s_1_, v_p_4_);
v___x_28_ = 46;
v___x_29_ = lean_uint32_dec_eq(v_c_10_, v___x_28_);
if (v___x_29_ == 0)
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 65;
v___x_31_ = lean_uint32_dec_le(v___x_30_, v_c_10_);
if (v___x_31_ == 0)
{
v___y_23_ = v___x_31_;
goto v___jp_22_;
}
else
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 90;
v___x_33_ = lean_uint32_dec_le(v_c_10_, v___x_32_);
v___y_23_ = v___x_33_;
goto v___jp_22_;
}
}
else
{
lean_object* v_c_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
lean_inc(v_p_4_);
lean_inc_ref(v_s_1_);
v_c_34_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_34_, 0, v_s_1_);
lean_ctor_set(v_c_34_, 1, v_iniPos_3_);
lean_ctor_set(v_c_34_, 2, v_p_4_);
v___x_35_ = lean_array_push(v_cs_2_, v_c_34_);
v___x_36_ = lean_string_utf8_next_fast(v_s_1_, v_p_4_);
lean_dec(v_p_4_);
v_cs_2_ = v___x_35_;
v_iniPos_3_ = v___x_36_;
v_p_4_ = v___x_36_;
goto _start;
}
v___jp_11_:
{
uint32_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = 42;
v___x_13_ = lean_uint32_dec_eq(v_c_10_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v_c_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
lean_inc(v_p_4_);
v_c_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_14_, 0, v_s_1_);
lean_ctor_set(v_c_14_, 1, v_iniPos_3_);
lean_ctor_set(v_c_14_, 2, v_p_4_);
v___x_15_ = lean_array_push(v_cs_2_, v_c_14_);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v_p_4_);
return v___x_16_;
}
else
{
goto v___jp_5_;
}
}
v___jp_17_:
{
uint32_t v___x_18_; uint8_t v___x_19_; 
v___x_18_ = 48;
v___x_19_ = lean_uint32_dec_le(v___x_18_, v_c_10_);
if (v___x_19_ == 0)
{
goto v___jp_11_;
}
else
{
uint32_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = 57;
v___x_21_ = lean_uint32_dec_le(v_c_10_, v___x_20_);
if (v___x_21_ == 0)
{
goto v___jp_11_;
}
else
{
goto v___jp_5_;
}
}
}
v___jp_22_:
{
if (v___y_23_ == 0)
{
uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_24_ = 97;
v___x_25_ = lean_uint32_dec_le(v___x_24_, v_c_10_);
if (v___x_25_ == 0)
{
goto v___jp_17_;
}
else
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 122;
v___x_27_ = lean_uint32_dec_le(v_c_10_, v___x_26_);
if (v___x_27_ == 0)
{
goto v___jp_17_;
}
else
{
goto v___jp_5_;
}
}
}
else
{
goto v___jp_5_;
}
}
}
else
{
lean_object* v_c_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc(v_p_4_);
v_c_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_38_, 0, v_s_1_);
lean_ctor_set(v_c_38_, 1, v_iniPos_3_);
lean_ctor_set(v_c_38_, 2, v_p_4_);
v___x_39_ = lean_array_push(v_cs_2_, v_c_38_);
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v_p_4_);
return v___x_40_;
}
v___jp_5_:
{
lean_object* v___x_6_; 
v___x_6_ = lean_string_utf8_next_fast(v_s_1_, v_p_4_);
lean_dec(v_p_4_);
v_p_4_ = v___x_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents_go(lean_object* v_s_41_, lean_object* v_cs_42_, lean_object* v_iniPos_43_, lean_object* v_p_44_, lean_object* v_iniPos__le_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_41_, v_cs_42_, v_iniPos_43_, v_p_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents(lean_object* v_s_49_, lean_object* v_p_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_p_50_);
v___x_52_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_49_, v___x_51_, v_p_50_, v_p_50_);
return v___x_52_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Util_Version_0__Lake_isWildVer(lean_object* v_s_53_){
_start:
{
lean_object* v_str_54_; lean_object* v_startInclusive_55_; lean_object* v_endExclusive_56_; lean_object* v_p_57_; lean_object* v___x_58_; uint8_t v_decide_59_; 
v_str_54_ = lean_ctor_get(v_s_53_, 0);
v_startInclusive_55_ = lean_ctor_get(v_s_53_, 1);
v_endExclusive_56_ = lean_ctor_get(v_s_53_, 2);
v_p_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_nat_sub(v_endExclusive_56_, v_startInclusive_55_);
v_decide_59_ = lean_nat_dec_eq(v_p_57_, v___x_58_);
if (v_decide_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v_decide_62_; 
v___x_60_ = lean_string_utf8_next_fast(v_str_54_, v_startInclusive_55_);
v___x_61_ = lean_nat_sub(v___x_60_, v_startInclusive_55_);
v_decide_62_ = lean_nat_dec_eq(v___x_61_, v___x_58_);
lean_dec(v___x_58_);
lean_dec(v___x_61_);
if (v_decide_62_ == 0)
{
return v_decide_62_;
}
else
{
uint32_t v_c_63_; uint32_t v___x_64_; uint8_t v___x_65_; 
v_c_63_ = lean_string_utf8_get_fast(v_str_54_, v_startInclusive_55_);
v___x_64_ = 120;
v___x_65_ = lean_uint32_dec_eq(v_c_63_, v___x_64_);
if (v___x_65_ == 0)
{
uint32_t v___x_66_; uint8_t v___x_67_; 
v___x_66_ = 88;
v___x_67_ = lean_uint32_dec_eq(v_c_63_, v___x_66_);
if (v___x_67_ == 0)
{
uint32_t v___x_68_; uint8_t v___x_69_; 
v___x_68_ = 42;
v___x_69_ = lean_uint32_dec_eq(v_c_63_, v___x_68_);
return v___x_69_;
}
else
{
return v_decide_62_;
}
}
else
{
return v_decide_62_;
}
}
}
else
{
uint8_t v___x_70_; 
lean_dec(v___x_58_);
v___x_70_ = 0;
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_isWildVer___boxed(lean_object* v_s_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l___private_Lake_Util_Version_0__Lake_isWildVer(v_s_71_);
lean_dec_ref(v_s_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg(lean_object* v_what_77_, lean_object* v_s_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_String_Slice_toNat_x3f(v_s_78_);
if (lean_obj_tag(v___x_80_) == 1)
{
lean_object* v_val_81_; lean_object* v___x_82_; 
v_val_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_val_81_);
lean_dec_ref_known(v___x_80_, 1);
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v_val_81_);
lean_ctor_set(v___x_82_, 1, v_a_79_);
return v___x_82_;
}
else
{
lean_object* v_str_83_; lean_object* v_startInclusive_84_; lean_object* v_endExclusive_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v___x_80_);
v_str_83_ = lean_ctor_get(v_s_78_, 0);
v_startInclusive_84_ = lean_ctor_get(v_s_78_, 1);
v_endExclusive_85_ = lean_ctor_get(v_s_78_, 2);
v___x_86_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0));
v___x_87_ = lean_string_append(v___x_86_, v_what_77_);
v___x_88_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1));
v___x_89_ = lean_string_append(v___x_87_, v___x_88_);
v___x_90_ = lean_string_utf8_extract_fast(v_str_83_, v_startInclusive_84_, v_endExclusive_85_);
v___x_91_ = lean_string_append(v___x_89_, v___x_90_);
lean_dec_ref(v___x_90_);
v___x_92_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_93_ = lean_string_append(v___x_91_, v___x_92_);
v___x_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v_a_79_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___boxed(lean_object* v_what_95_, lean_object* v_s_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg(v_what_95_, v_s_96_, v_a_97_);
lean_dec_ref(v_s_96_);
lean_dec_ref(v_what_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat(lean_object* v_00_u03c3_99_, lean_object* v_what_100_, lean_object* v_s_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_String_Slice_toNat_x3f(v_s_101_);
if (lean_obj_tag(v___x_103_) == 1)
{
lean_object* v_val_104_; lean_object* v___x_105_; 
v_val_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_104_);
lean_dec_ref_known(v___x_103_, 1);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v_val_104_);
lean_ctor_set(v___x_105_, 1, v_a_102_);
return v___x_105_;
}
else
{
lean_object* v_str_106_; lean_object* v_startInclusive_107_; lean_object* v_endExclusive_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v___x_103_);
v_str_106_ = lean_ctor_get(v_s_101_, 0);
v_startInclusive_107_ = lean_ctor_get(v_s_101_, 1);
v_endExclusive_108_ = lean_ctor_get(v_s_101_, 2);
v___x_109_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0));
v___x_110_ = lean_string_append(v___x_109_, v_what_100_);
v___x_111_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1));
v___x_112_ = lean_string_append(v___x_110_, v___x_111_);
v___x_113_ = lean_string_utf8_extract_fast(v_str_106_, v_startInclusive_107_, v_endExclusive_108_);
v___x_114_ = lean_string_append(v___x_112_, v___x_113_);
lean_dec_ref(v___x_113_);
v___x_115_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_116_ = lean_string_append(v___x_114_, v___x_115_);
v___x_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_a_102_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___boxed(lean_object* v_00_u03c3_118_, lean_object* v_what_119_, lean_object* v_s_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lake_Util_Version_0__Lake_parseVerNat(v_00_u03c3_118_, v_what_119_, v_s_120_, v_a_121_);
lean_dec_ref(v_s_120_);
lean_dec_ref(v_what_119_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx(lean_object* v_x_123_){
_start:
{
switch(lean_obj_tag(v_x_123_))
{
case 0:
{
lean_object* v___x_124_; 
v___x_124_ = lean_unsigned_to_nat(0u);
return v___x_124_;
}
case 1:
{
lean_object* v___x_125_; 
v___x_125_ = lean_unsigned_to_nat(1u);
return v___x_125_;
}
default: 
{
lean_object* v___x_126_; 
v___x_126_ = lean_unsigned_to_nat(2u);
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___boxed(lean_object* v_x_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx(v_x_127_);
lean_dec(v_x_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(lean_object* v_t_129_, lean_object* v_k_130_){
_start:
{
if (lean_obj_tag(v_t_129_) == 2)
{
lean_object* v_n_131_; lean_object* v___x_132_; 
v_n_131_ = lean_ctor_get(v_t_129_, 0);
lean_inc(v_n_131_);
lean_dec_ref_known(v_t_129_, 1);
v___x_132_ = lean_apply_1(v_k_130_, v_n_131_);
return v___x_132_;
}
else
{
lean_dec(v_t_129_);
return v_k_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(lean_object* v_motive_133_, lean_object* v_ctorIdx_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_k_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_135_, v_k_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___boxed(lean_object* v_motive_139_, lean_object* v_ctorIdx_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_k_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(v_motive_139_, v_ctorIdx_140_, v_t_141_, v_h_142_, v_k_143_);
lean_dec(v_ctorIdx_140_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim___redArg(lean_object* v_t_145_, lean_object* v_none_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_145_, v_none_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim(lean_object* v_motive_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_none_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_149_, v_none_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim___redArg(lean_object* v_t_153_, lean_object* v_wild_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_153_, v_wild_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim(lean_object* v_motive_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_wild_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_157_, v_wild_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim___redArg(lean_object* v_t_161_, lean_object* v_nat_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_161_, v_nat_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim(lean_object* v_motive_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_nat_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_165_, v_nat_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(lean_object* v_what_170_, lean_object* v_s_x3f_171_, lean_object* v_a_172_){
_start:
{
if (lean_obj_tag(v_s_x3f_171_) == 1)
{
lean_object* v_val_173_; uint8_t v___x_174_; 
v_val_173_ = lean_ctor_get(v_s_x3f_171_, 0);
v___x_174_ = l___private_Lake_Util_Version_0__Lake_isWildVer(v_val_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
v___x_175_ = l_String_Slice_toNat_x3f(v_val_173_);
if (lean_obj_tag(v___x_175_) == 1)
{
lean_object* v_val_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_184_; 
v_val_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_184_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_val_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set_tag(v___x_178_, 2);
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_val_176_);
v___x_181_ = v_reuseFailAlloc_183_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_172_);
return v___x_182_;
}
}
}
else
{
lean_object* v_str_185_; lean_object* v_startInclusive_186_; lean_object* v_endExclusive_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v___x_175_);
v_str_185_ = lean_ctor_get(v_val_173_, 0);
v_startInclusive_186_ = lean_ctor_get(v_val_173_, 1);
v_endExclusive_187_ = lean_ctor_get(v_val_173_, 2);
v___x_188_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0));
v___x_189_ = lean_string_append(v___x_188_, v_what_170_);
v___x_190_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0));
v___x_191_ = lean_string_append(v___x_189_, v___x_190_);
v___x_192_ = lean_string_utf8_extract_fast(v_str_185_, v_startInclusive_186_, v_endExclusive_187_);
v___x_193_ = lean_string_append(v___x_191_, v___x_192_);
lean_dec_ref(v___x_192_);
v___x_194_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_195_ = lean_string_append(v___x_193_, v___x_194_);
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_172_);
return v___x_196_;
}
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_box(1);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v_a_172_);
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v_a_172_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___boxed(lean_object* v_what_201_, lean_object* v_s_x3f_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v_what_201_, v_s_x3f_202_, v_a_203_);
lean_dec(v_s_x3f_202_);
lean_dec_ref(v_what_201_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent(lean_object* v_00_u03c3_205_, lean_object* v_what_206_, lean_object* v_s_x3f_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v_what_206_, v_s_x3f_207_, v_a_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___boxed(lean_object* v_00_u03c3_210_, lean_object* v_what_211_, lean_object* v_s_x3f_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent(v_00_u03c3_210_, v_what_211_, v_s_x3f_212_, v_a_213_);
lean_dec(v_s_x3f_212_);
lean_dec_ref(v_what_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(lean_object* v_s_215_, lean_object* v_p_216_){
_start:
{
lean_object* v___x_217_; uint8_t v_decide_218_; 
v___x_217_ = lean_string_utf8_byte_size(v_s_215_);
v_decide_218_ = lean_nat_dec_eq(v_p_216_, v___x_217_);
if (v_decide_218_ == 0)
{
uint32_t v___x_219_; uint32_t v___x_220_; uint8_t v___x_221_; 
v___x_219_ = lean_string_utf8_get_fast(v_s_215_, v_p_216_);
v___x_220_ = 32;
v___x_221_ = lean_uint32_dec_eq(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
uint32_t v___x_222_; uint8_t v___x_223_; 
v___x_222_ = 9;
v___x_223_ = lean_uint32_dec_eq(v___x_219_, v___x_222_);
if (v___x_223_ == 0)
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 13;
v___x_225_ = lean_uint32_dec_eq(v___x_219_, v___x_224_);
if (v___x_225_ == 0)
{
uint32_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = 10;
v___x_227_ = lean_uint32_dec_eq(v___x_219_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
v___x_228_ = lean_string_utf8_next_fast(v_s_215_, v_p_216_);
lean_dec(v_p_216_);
v_p_216_ = v___x_228_;
goto _start;
}
else
{
return v_p_216_;
}
}
else
{
return v_p_216_;
}
}
else
{
return v_p_216_;
}
}
else
{
return v_p_216_;
}
}
else
{
return v_p_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace___boxed(lean_object* v_s_230_, lean_object* v_p_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(v_s_230_, v_p_231_);
lean_dec_ref(v_s_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(lean_object* v_s_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_235_; uint8_t v_decide_236_; 
v___x_235_ = lean_string_utf8_byte_size(v_s_233_);
v_decide_236_ = lean_nat_dec_eq(v_a_234_, v___x_235_);
if (v_decide_236_ == 0)
{
uint32_t v___x_237_; uint32_t v___x_238_; uint8_t v___x_239_; 
v___x_237_ = lean_string_utf8_get_fast(v_s_233_, v_a_234_);
v___x_238_ = 45;
v___x_239_ = lean_uint32_dec_eq(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_box(0);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v_a_234_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_242_ = lean_string_utf8_next_fast(v_s_233_, v_a_234_);
lean_dec(v_a_234_);
v___x_243_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(v_s_233_, v___x_242_);
v___x_244_ = lean_string_utf8_extract_fast(v_s_233_, v___x_242_, v___x_243_);
v___x_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_243_);
return v___x_246_;
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_a_234_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f___boxed(lean_object* v_s_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_249_, v_a_250_);
lean_dec_ref(v_s_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(lean_object* v_s_254_, lean_object* v_a_255_){
_start:
{
lean_object* v___x_256_; lean_object* v_a_257_; 
v___x_256_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_254_, v_a_255_);
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
if (lean_obj_tag(v_a_257_) == 1)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_273_; 
v_a_258_ = lean_ctor_get(v___x_256_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v___x_256_, 0);
lean_dec(v_unused_274_);
v___x_260_ = v___x_256_;
v_isShared_261_ = v_isSharedCheck_273_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_256_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_273_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v_val_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_val_262_ = lean_ctor_get(v_a_257_, 0);
lean_inc(v_val_262_);
lean_dec_ref_known(v_a_257_, 1);
v___x_263_ = lean_string_utf8_byte_size(v_val_262_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_nat_dec_eq(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v_val_262_);
v___x_267_ = v___x_260_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_val_262_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_a_258_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_271_; 
lean_dec(v_val_262_);
v___x_269_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0));
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 1);
lean_ctor_set(v___x_260_, 0, v___x_269_);
v___x_271_ = v___x_260_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_a_258_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_283_; 
lean_dec(v_a_257_);
v_a_275_ = lean_ctor_get(v___x_256_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v___x_256_, 0);
lean_dec(v_unused_284_);
v___x_277_ = v___x_256_;
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_256_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_279_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_279_);
v___x_281_ = v___x_277_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_a_275_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___boxed(lean_object* v_s_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_285_, v_a_286_);
lean_dec_ref(v_s_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(lean_object* v_s_289_, lean_object* v_x_290_, lean_object* v_startPos_291_, lean_object* v_endPos_292_){
_start:
{
lean_object* v___x_293_; 
lean_inc_ref(v_s_289_);
v___x_293_ = lean_apply_2(v_x_290_, v_s_289_, v_startPos_291_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v_a_295_; uint8_t v_decide_296_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
v_a_295_ = lean_ctor_get(v___x_293_, 1);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_293_, 2);
v_decide_296_ = lean_nat_dec_eq(v_a_295_, v_endPos_292_);
if (v_decide_296_ == 0)
{
lean_object* v_tail_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v_a_294_);
v_tail_297_ = lean_string_utf8_extract(v_s_289_, v_a_295_, v_endPos_292_);
lean_dec(v_a_295_);
lean_dec_ref(v_s_289_);
v___x_298_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_299_ = lean_string_append(v___x_298_, v_tail_297_);
lean_dec_ref(v_tail_297_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; 
lean_dec(v_a_295_);
lean_dec_ref(v_s_289_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v_a_294_);
return v___x_301_;
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_303_; 
lean_dec_ref(v_s_289_);
v_a_302_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_293_, 2);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v_a_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___boxed(lean_object* v_s_304_, lean_object* v_x_305_, lean_object* v_startPos_306_, lean_object* v_endPos_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_304_, v_x_305_, v_startPos_306_, v_endPos_307_);
lean_dec(v_endPos_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object* v_00_u03b1_309_, lean_object* v_s_310_, lean_object* v_x_311_, lean_object* v_startPos_312_, lean_object* v_endPos_313_){
_start:
{
lean_object* v___x_314_; 
lean_inc_ref(v_s_310_);
v___x_314_ = lean_apply_2(v_x_311_, v_s_310_, v_startPos_312_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v_a_316_; uint8_t v_decide_317_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
v_a_316_ = lean_ctor_get(v___x_314_, 1);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_314_, 2);
v_decide_317_ = lean_nat_dec_eq(v_a_316_, v_endPos_313_);
if (v_decide_317_ == 0)
{
lean_object* v_tail_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec(v_a_315_);
v_tail_318_ = lean_string_utf8_extract(v_s_310_, v_a_316_, v_endPos_313_);
lean_dec(v_a_316_);
lean_dec_ref(v_s_310_);
v___x_319_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_320_ = lean_string_append(v___x_319_, v_tail_318_);
lean_dec_ref(v_tail_318_);
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; 
lean_dec(v_a_316_);
lean_dec_ref(v_s_310_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v_a_315_);
return v___x_322_;
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_324_; 
lean_dec_ref(v_s_310_);
v_a_323_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_314_, 2);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v_a_323_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___boxed(lean_object* v_00_u03b1_325_, lean_object* v_s_326_, lean_object* v_x_327_, lean_object* v_startPos_328_, lean_object* v_endPos_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lake_Util_Version_0__Lake_runVerParse(v_00_u03b1_325_, v_s_326_, v_x_327_, v_startPos_328_, v_endPos_329_);
lean_dec(v_endPos_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprSemVerCore_repr_spec__0(lean_object* v_a_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lean_nat_to_int(v_a_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(9u);
v___x_351_ = lean_nat_to_int(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__0));
v___x_363_ = lean_string_length(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__15, &l_Lake_instReprSemVerCore_repr___redArg___closed__15_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15);
v___x_365_ = lean_nat_to_int(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___redArg(lean_object* v_x_370_){
_start:
{
lean_object* v_major_371_; lean_object* v_minor_372_; lean_object* v_patch_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_major_371_ = lean_ctor_get(v_x_370_, 0);
lean_inc(v_major_371_);
v_minor_372_ = lean_ctor_get(v_x_370_, 1);
lean_inc(v_minor_372_);
v_patch_373_ = lean_ctor_get(v_x_370_, 2);
lean_inc(v_patch_373_);
lean_dec_ref(v_x_370_);
v___x_374_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_375_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__6));
v___x_376_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__7, &l_Lake_instReprSemVerCore_repr___redArg___closed__7_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7);
v___x_377_ = l_Nat_reprFast(v_major_371_);
v___x_378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
v___x_379_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_376_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = 0;
v___x_381_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_380_);
v___x_382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_375_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_box(1);
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__11));
v___x_388_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_374_);
v___x_390_ = l_Nat_reprFast(v_minor_372_);
v___x_391_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
v___x_392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_376_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*1, v___x_380_);
v___x_394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_389_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_383_);
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_385_);
v___x_397_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__13));
v___x_398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_374_);
v___x_400_ = l_Nat_reprFast(v_patch_373_);
v___x_401_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
v___x_402_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_376_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v___x_380_);
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_399_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_406_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_404_);
v___x_408_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_405_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*1, v___x_380_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr(lean_object* v_x_412_, lean_object* v_prec_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lake_instReprSemVerCore_repr___redArg(v_x_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___boxed(lean_object* v_x_415_, lean_object* v_prec_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lake_instReprSemVerCore_repr(v_x_415_, v_prec_416_);
lean_dec(v_prec_416_);
return v_res_417_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore_decEq(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
lean_object* v_major_422_; lean_object* v_minor_423_; lean_object* v_patch_424_; lean_object* v_major_425_; lean_object* v_minor_426_; lean_object* v_patch_427_; uint8_t v___x_428_; 
v_major_422_ = lean_ctor_get(v_x_420_, 0);
v_minor_423_ = lean_ctor_get(v_x_420_, 1);
v_patch_424_ = lean_ctor_get(v_x_420_, 2);
v_major_425_ = lean_ctor_get(v_x_421_, 0);
v_minor_426_ = lean_ctor_get(v_x_421_, 1);
v_patch_427_ = lean_ctor_get(v_x_421_, 2);
v___x_428_ = lean_nat_dec_eq(v_major_422_, v_major_425_);
if (v___x_428_ == 0)
{
return v___x_428_;
}
else
{
uint8_t v___x_429_; 
v___x_429_ = lean_nat_dec_eq(v_minor_423_, v_minor_426_);
if (v___x_429_ == 0)
{
return v___x_429_;
}
else
{
uint8_t v___x_430_; 
v___x_430_ = lean_nat_dec_eq(v_patch_424_, v_patch_427_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore_decEq___boxed(lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_431_, v_x_432_);
lean_dec_ref(v_x_432_);
lean_dec_ref(v_x_431_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore(lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore___boxed(lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lake_instDecidableEqSemVerCore(v_x_438_, v_x_439_);
lean_dec_ref(v_x_439_);
lean_dec_ref(v_x_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdSemVerCore_ord(lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
lean_object* v_major_444_; lean_object* v_minor_445_; lean_object* v_patch_446_; lean_object* v_major_447_; lean_object* v_minor_448_; lean_object* v_patch_449_; uint8_t v___x_450_; 
v_major_444_ = lean_ctor_get(v_x_442_, 0);
v_minor_445_ = lean_ctor_get(v_x_442_, 1);
v_patch_446_ = lean_ctor_get(v_x_442_, 2);
v_major_447_ = lean_ctor_get(v_x_443_, 0);
v_minor_448_ = lean_ctor_get(v_x_443_, 1);
v_patch_449_ = lean_ctor_get(v_x_443_, 2);
v___x_450_ = lean_nat_dec_lt(v_major_444_, v_major_447_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = lean_nat_dec_eq(v_major_444_, v_major_447_);
if (v___x_451_ == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 2;
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = lean_nat_dec_lt(v_minor_445_, v_minor_448_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
v___x_454_ = lean_nat_dec_eq(v_minor_445_, v_minor_448_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
v___x_455_ = 2;
return v___x_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = lean_nat_dec_lt(v_patch_446_, v_patch_449_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
v___x_457_ = lean_nat_dec_eq(v_patch_446_, v_patch_449_);
if (v___x_457_ == 0)
{
uint8_t v___x_458_; 
v___x_458_ = 2;
return v___x_458_;
}
else
{
uint8_t v___x_459_; 
v___x_459_ = 1;
return v___x_459_;
}
}
else
{
uint8_t v___x_460_; 
v___x_460_ = 0;
return v___x_460_;
}
}
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
}
else
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdSemVerCore_ord___boxed(lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Lake_instOrdSemVerCore_ord(v_x_463_, v_x_464_);
lean_dec_ref(v_x_464_);
lean_dec_ref(v_x_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
static lean_object* _init_l_Lake_SemVerCore_instLT(void){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lean_box(0);
return v___x_469_;
}
}
static lean_object* _init_l_Lake_SemVerCore_instLE(void){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = lean_box(0);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0(lean_object* v_x_471_, lean_object* v_y_472_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = l_Lake_instOrdSemVerCore_ord(v_x_471_, v_y_472_);
if (v___x_473_ == 2)
{
lean_inc_ref(v_y_472_);
return v_y_472_;
}
else
{
lean_inc_ref(v_x_471_);
return v_x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0___boxed(lean_object* v_x_474_, lean_object* v_y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lake_SemVerCore_instMin___lam__0(v_x_474_, v_y_475_);
lean_dec_ref(v_y_475_);
lean_dec_ref(v_x_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0(lean_object* v_x_479_, lean_object* v_y_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = l_Lake_instOrdSemVerCore_ord(v_x_479_, v_y_480_);
if (v___x_481_ == 2)
{
lean_inc_ref(v_x_479_);
return v_x_479_;
}
else
{
lean_inc_ref(v_y_480_);
return v_y_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0___boxed(lean_object* v_x_482_, lean_object* v_y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lake_SemVerCore_instMax___lam__0(v_x_482_, v_y_483_);
lean_dec_ref(v_y_483_);
lean_dec_ref(v_x_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(lean_object* v_s_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_a_496_; lean_object* v_a_497_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_556_; 
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_494_);
v___x_503_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_493_, v___x_502_, v_a_494_, v_a_494_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_a_505_ = lean_ctor_get(v___x_503_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_556_ == 0)
{
v___x_507_ = v___x_503_;
v_isShared_508_ = v_isSharedCheck_556_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_556_;
goto v_resetjp_506_;
}
v___jp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0));
v___x_499_ = lean_string_append(v___x_498_, v_a_496_);
lean_dec_ref(v_a_496_);
v___x_500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v_a_497_);
return v___x_500_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_509_ = lean_array_get_size(v_a_504_);
v___x_510_ = lean_unsigned_to_nat(3u);
v___x_511_ = lean_nat_dec_eq(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_del_object(v___x_507_);
lean_dec(v_a_504_);
v___x_512_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1));
v___x_513_ = l_Nat_reprFast(v___x_509_);
v___x_514_ = lean_string_append(v___x_512_, v___x_513_);
lean_dec_ref(v___x_513_);
v___x_515_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2));
v___x_516_ = lean_string_append(v___x_514_, v___x_515_);
v_a_496_ = v___x_516_;
v_a_497_ = v_a_505_;
goto v___jp_495_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_array_fget_borrowed(v_a_504_, v___x_501_);
v___x_518_ = l_String_Slice_toNat_x3f(v___x_517_);
if (lean_obj_tag(v___x_518_) == 1)
{
lean_object* v_val_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_val_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v___x_518_, 1);
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_array_fget_borrowed(v_a_504_, v___x_520_);
v___x_522_ = l_String_Slice_toNat_x3f(v___x_521_);
if (lean_obj_tag(v___x_522_) == 1)
{
lean_object* v_val_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_val_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = lean_unsigned_to_nat(2u);
v___x_525_ = lean_array_fget(v_a_504_, v___x_524_);
lean_dec(v_a_504_);
v___x_526_ = l_String_Slice_toNat_x3f(v___x_525_);
if (lean_obj_tag(v___x_526_) == 1)
{
lean_object* v_val_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
lean_dec(v___x_525_);
v_val_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_val_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_528_, 0, v_val_519_);
lean_ctor_set(v___x_528_, 1, v_val_523_);
lean_ctor_set(v___x_528_, 2, v_val_527_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_528_);
v___x_530_ = v___x_507_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_a_505_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
else
{
lean_object* v_str_532_; lean_object* v_startInclusive_533_; lean_object* v_endExclusive_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec(v___x_526_);
lean_dec(v_val_523_);
lean_dec(v_val_519_);
lean_del_object(v___x_507_);
v_str_532_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_str_532_);
v_startInclusive_533_ = lean_ctor_get(v___x_525_, 1);
lean_inc(v_startInclusive_533_);
v_endExclusive_534_ = lean_ctor_get(v___x_525_, 2);
lean_inc(v_endExclusive_534_);
lean_dec(v___x_525_);
v___x_535_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_536_ = lean_string_utf8_extract_fast(v_str_532_, v_startInclusive_533_, v_endExclusive_534_);
lean_dec(v_endExclusive_534_);
lean_dec(v_startInclusive_533_);
lean_dec_ref(v_str_532_);
v___x_537_ = lean_string_append(v___x_535_, v___x_536_);
lean_dec_ref(v___x_536_);
v___x_538_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_539_ = lean_string_append(v___x_537_, v___x_538_);
v_a_496_ = v___x_539_;
v_a_497_ = v_a_505_;
goto v___jp_495_;
}
}
else
{
lean_object* v_str_540_; lean_object* v_startInclusive_541_; lean_object* v_endExclusive_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
lean_inc(v___x_521_);
lean_dec(v___x_522_);
lean_dec(v_val_519_);
lean_del_object(v___x_507_);
lean_dec(v_a_504_);
v_str_540_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_str_540_);
v_startInclusive_541_ = lean_ctor_get(v___x_521_, 1);
lean_inc(v_startInclusive_541_);
v_endExclusive_542_ = lean_ctor_get(v___x_521_, 2);
lean_inc(v_endExclusive_542_);
lean_dec(v___x_521_);
v___x_543_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_544_ = lean_string_utf8_extract_fast(v_str_540_, v_startInclusive_541_, v_endExclusive_542_);
lean_dec(v_endExclusive_542_);
lean_dec(v_startInclusive_541_);
lean_dec_ref(v_str_540_);
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
lean_dec_ref(v___x_544_);
v___x_546_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_547_ = lean_string_append(v___x_545_, v___x_546_);
v_a_496_ = v___x_547_;
v_a_497_ = v_a_505_;
goto v___jp_495_;
}
}
else
{
lean_object* v_str_548_; lean_object* v_startInclusive_549_; lean_object* v_endExclusive_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_inc(v___x_517_);
lean_dec(v___x_518_);
lean_del_object(v___x_507_);
lean_dec(v_a_504_);
v_str_548_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_str_548_);
v_startInclusive_549_ = lean_ctor_get(v___x_517_, 1);
lean_inc(v_startInclusive_549_);
v_endExclusive_550_ = lean_ctor_get(v___x_517_, 2);
lean_inc(v_endExclusive_550_);
lean_dec(v___x_517_);
v___x_551_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_552_ = lean_string_utf8_extract_fast(v_str_548_, v_startInclusive_549_, v_endExclusive_550_);
lean_dec(v_endExclusive_550_);
lean_dec(v_startInclusive_549_);
lean_dec_ref(v_str_548_);
v___x_553_ = lean_string_append(v___x_551_, v___x_552_);
lean_dec_ref(v___x_552_);
v___x_554_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_555_ = lean_string_append(v___x_553_, v___x_554_);
v_a_496_ = v___x_555_;
v_a_497_ = v_a_505_;
goto v___jp_495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_parse(lean_object* v_s_557_){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_string_utf8_byte_size(v_s_557_);
lean_inc_ref(v_s_557_);
v___x_560_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_557_, v___x_558_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v_a_562_; uint8_t v_decide_563_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
v_a_562_ = lean_ctor_get(v___x_560_, 1);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_560_, 2);
v_decide_563_ = lean_nat_dec_eq(v_a_562_, v___x_559_);
if (v_decide_563_ == 0)
{
lean_object* v_tail_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec(v_a_561_);
v_tail_564_ = lean_string_utf8_extract(v_s_557_, v_a_562_, v___x_559_);
lean_dec(v_a_562_);
lean_dec_ref(v_s_557_);
v___x_565_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_566_ = lean_string_append(v___x_565_, v_tail_564_);
lean_dec_ref(v_tail_564_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
else
{
lean_object* v___x_568_; 
lean_dec(v_a_562_);
lean_dec_ref(v_s_557_);
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v_a_561_);
return v___x_568_;
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_570_; 
lean_dec_ref(v_s_557_);
v_a_569_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_560_, 2);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v_a_569_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_toString(lean_object* v_ver_572_){
_start:
{
lean_object* v_major_573_; lean_object* v_minor_574_; lean_object* v_patch_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_major_573_ = lean_ctor_get(v_ver_572_, 0);
lean_inc(v_major_573_);
v_minor_574_ = lean_ctor_get(v_ver_572_, 1);
lean_inc(v_minor_574_);
v_patch_575_ = lean_ctor_get(v_ver_572_, 2);
lean_inc(v_patch_575_);
lean_dec_ref(v_ver_572_);
v___x_576_ = l_Nat_reprFast(v_major_573_);
v___x_577_ = ((lean_object*)(l_Lake_SemVerCore_toString___closed__0));
v___x_578_ = lean_string_append(v___x_576_, v___x_577_);
v___x_579_ = l_Nat_reprFast(v_minor_574_);
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
lean_dec_ref(v___x_579_);
v___x_581_ = lean_string_append(v___x_580_, v___x_577_);
v___x_582_ = l_Nat_reprFast(v_patch_575_);
v___x_583_ = lean_string_append(v___x_581_, v___x_582_);
lean_dec_ref(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instToJson___lam__0(lean_object* v_x_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_Lake_SemVerCore_toString(v_x_586_);
v___x_588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instFromJson___lam__0(lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Json_getStr_x3f(v_x_591_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_602_; 
v_a_601_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_592_, 1);
v___x_602_ = l_Lake_SemVerCore_parse(v_a_601_);
return v___x_602_;
}
}
}
static lean_object* _init_l_Lake_instReprStdVer_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_unsigned_to_nat(16u);
v___x_620_ = lean_nat_to_int(v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___redArg(lean_object* v_x_624_){
_start:
{
lean_object* v_toSemVerCore_625_; lean_object* v_specialDescr_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_659_; 
v_toSemVerCore_625_ = lean_ctor_get(v_x_624_, 0);
v_specialDescr_626_ = lean_ctor_get(v_x_624_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_624_);
if (v_isSharedCheck_659_ == 0)
{
v___x_628_ = v_x_624_;
v_isShared_629_ = v_isSharedCheck_659_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_specialDescr_626_);
lean_inc(v_toSemVerCore_625_);
lean_dec(v_x_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_659_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_630_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_631_ = ((lean_object*)(l_Lake_instReprStdVer_repr___redArg___closed__3));
v___x_632_ = lean_obj_once(&l_Lake_instReprStdVer_repr___redArg___closed__4, &l_Lake_instReprStdVer_repr___redArg___closed__4_once, _init_l_Lake_instReprStdVer_repr___redArg___closed__4);
v___x_633_ = l_Lake_instReprSemVerCore_repr___redArg(v_toSemVerCore_625_);
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 4);
lean_ctor_set(v___x_628_, 1, v___x_633_);
lean_ctor_set(v___x_628_, 0, v___x_632_);
v___x_635_ = v___x_628_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_633_);
v___x_635_ = v_reuseFailAlloc_658_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_636_ = 0;
v___x_637_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set_uint8(v___x_637_, sizeof(void*)*1, v___x_636_);
v___x_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_631_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_box(1);
v___x_642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = ((lean_object*)(l_Lake_instReprStdVer_repr___redArg___closed__6));
v___x_644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_630_);
v___x_646_ = l_String_quote(v_specialDescr_626_);
v___x_647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
v___x_648_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_632_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*1, v___x_636_);
v___x_650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_645_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_652_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_650_);
v___x_654_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_651_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*1, v___x_636_);
return v___x_657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr(lean_object* v_x_660_, lean_object* v_prec_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lake_instReprStdVer_repr___redArg(v_x_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___boxed(lean_object* v_x_663_, lean_object* v_prec_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lake_instReprStdVer_repr(v_x_663_, v_prec_664_);
lean_dec(v_prec_664_);
return v_res_665_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer_decEq(lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
lean_object* v_toSemVerCore_670_; lean_object* v_specialDescr_671_; lean_object* v_toSemVerCore_672_; lean_object* v_specialDescr_673_; uint8_t v___x_674_; 
v_toSemVerCore_670_ = lean_ctor_get(v_x_668_, 0);
v_specialDescr_671_ = lean_ctor_get(v_x_668_, 1);
v_toSemVerCore_672_ = lean_ctor_get(v_x_669_, 0);
v_specialDescr_673_ = lean_ctor_get(v_x_669_, 1);
v___x_674_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_670_, v_toSemVerCore_672_);
if (v___x_674_ == 0)
{
return v___x_674_;
}
else
{
uint8_t v___x_675_; 
v___x_675_ = lean_string_dec_eq(v_specialDescr_671_, v_specialDescr_673_);
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer_decEq___boxed(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Lake_instDecidableEqStdVer_decEq(v_x_676_, v_x_677_);
lean_dec_ref(v_x_677_);
lean_dec_ref(v_x_676_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer(lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = l_Lake_instDecidableEqStdVer_decEq(v_x_680_, v_x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer___boxed(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Lake_instDecidableEqStdVer(v_x_683_, v_x_684_);
lean_dec_ref(v_x_684_);
lean_dec_ref(v_x_683_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0(lean_object* v_self_687_){
_start:
{
lean_object* v_toSemVerCore_688_; 
v_toSemVerCore_688_ = lean_ctor_get(v_self_687_, 0);
lean_inc_ref(v_toSemVerCore_688_);
return v_toSemVerCore_688_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed(lean_object* v_self_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lake_StdVer_instCoeSemVerCore___lam__0(v_self_689_);
lean_dec_ref(v_self_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_ofSemVerCore(lean_object* v_ver_693_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_ver_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT uint8_t l_Lake_StdVer_compare(lean_object* v_a_698_, lean_object* v_b_699_){
_start:
{
lean_object* v_toSemVerCore_700_; lean_object* v_specialDescr_701_; lean_object* v_toSemVerCore_702_; lean_object* v_specialDescr_703_; uint8_t v___x_704_; 
v_toSemVerCore_700_ = lean_ctor_get(v_a_698_, 0);
v_specialDescr_701_ = lean_ctor_get(v_a_698_, 1);
v_toSemVerCore_702_ = lean_ctor_get(v_b_699_, 0);
v_specialDescr_703_ = lean_ctor_get(v_b_699_, 1);
v___x_704_ = l_Lake_instOrdSemVerCore_ord(v_toSemVerCore_700_, v_toSemVerCore_702_);
if (v___x_704_ == 1)
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_706_ = lean_string_dec_eq(v_specialDescr_701_, v___x_705_);
if (v___x_706_ == 0)
{
uint8_t v___x_707_; 
v___x_707_ = lean_string_dec_eq(v_specialDescr_703_, v___x_705_);
if (v___x_707_ == 0)
{
uint8_t v___x_708_; 
v___x_708_ = lean_string_compare(v_specialDescr_701_, v_specialDescr_703_);
return v___x_708_;
}
else
{
uint8_t v___x_709_; 
v___x_709_ = 0;
return v___x_709_;
}
}
else
{
uint8_t v___x_710_; 
v___x_710_ = lean_string_dec_eq(v_specialDescr_703_, v___x_705_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = 2;
return v___x_711_;
}
else
{
return v___x_704_;
}
}
}
else
{
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_compare___boxed(lean_object* v_a_712_, lean_object* v_b_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l_Lake_StdVer_compare(v_a_712_, v_b_713_);
lean_dec_ref(v_b_713_);
lean_dec_ref(v_a_712_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
static lean_object* _init_l_Lake_StdVer_instLT(void){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_box(0);
return v___x_718_;
}
}
static lean_object* _init_l_Lake_StdVer_instLE(void){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_box(0);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0(lean_object* v_x_720_, lean_object* v_y_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = l_Lake_StdVer_compare(v_x_720_, v_y_721_);
if (v___x_722_ == 2)
{
lean_inc_ref(v_y_721_);
return v_y_721_;
}
else
{
lean_inc_ref(v_x_720_);
return v_x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0___boxed(lean_object* v_x_723_, lean_object* v_y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lake_StdVer_instMin___lam__0(v_x_723_, v_y_724_);
lean_dec_ref(v_y_724_);
lean_dec_ref(v_x_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0(lean_object* v_x_728_, lean_object* v_y_729_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = l_Lake_StdVer_compare(v_x_728_, v_y_729_);
if (v___x_730_ == 2)
{
lean_inc_ref(v_x_728_);
return v_x_728_;
}
else
{
lean_inc_ref(v_y_729_);
return v_y_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0___boxed(lean_object* v_x_731_, lean_object* v_y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lake_StdVer_instMax___lam__0(v_x_731_, v_y_732_);
lean_dec_ref(v_y_732_);
lean_dec_ref(v_x_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parseM(lean_object* v_s_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_738_; 
lean_inc_ref(v_s_736_);
v___x_738_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_736_, v_a_737_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v_a_740_; lean_object* v___x_741_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
v_a_740_ = lean_ctor_get(v___x_738_, 1);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_738_, 2);
v___x_741_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_736_, v_a_740_);
lean_dec_ref(v_s_736_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_751_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_a_743_ = lean_ctor_get(v___x_741_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_751_ == 0)
{
v___x_745_ = v___x_741_;
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v_a_739_);
lean_ctor_set(v___x_747_, 1, v_a_742_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_a_743_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec(v_a_739_);
v_a_752_ = lean_ctor_get(v___x_741_, 0);
v_a_753_ = lean_ctor_get(v___x_741_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_741_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_inc(v_a_752_);
lean_dec(v___x_741_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_752_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v_s_736_);
v_a_761_ = lean_ctor_get(v___x_738_, 0);
v_a_762_ = lean_ctor_get(v___x_738_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_738_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_inc(v_a_761_);
lean_dec(v___x_738_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_761_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parse(lean_object* v_s_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = lean_string_utf8_byte_size(v_s_770_);
lean_inc_ref(v_s_770_);
v___x_773_ = l_Lake_StdVer_parseM(v_s_770_, v___x_771_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v_a_775_; uint8_t v_decide_776_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
v_a_775_ = lean_ctor_get(v___x_773_, 1);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_773_, 2);
v_decide_776_ = lean_nat_dec_eq(v_a_775_, v___x_772_);
if (v_decide_776_ == 0)
{
lean_object* v_tail_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec(v_a_774_);
v_tail_777_ = lean_string_utf8_extract(v_s_770_, v_a_775_, v___x_772_);
lean_dec(v_a_775_);
lean_dec_ref(v_s_770_);
v___x_778_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_779_ = lean_string_append(v___x_778_, v_tail_777_);
lean_dec_ref(v_tail_777_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
else
{
lean_object* v___x_781_; 
lean_dec(v_a_775_);
lean_dec_ref(v_s_770_);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v_a_774_);
return v___x_781_;
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_783_; 
lean_dec_ref(v_s_770_);
v_a_782_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_773_, 2);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v_a_782_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_toString(lean_object* v_ver_785_){
_start:
{
lean_object* v_toSemVerCore_786_; lean_object* v_specialDescr_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_toSemVerCore_786_ = lean_ctor_get(v_ver_785_, 0);
lean_inc_ref(v_toSemVerCore_786_);
v_specialDescr_787_ = lean_ctor_get(v_ver_785_, 1);
lean_inc_ref(v_specialDescr_787_);
lean_dec_ref(v_ver_785_);
v___x_788_ = lean_string_utf8_byte_size(v_specialDescr_787_);
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = lean_nat_dec_eq(v___x_788_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_791_ = l_Lake_SemVerCore_toString(v_toSemVerCore_786_);
v___x_792_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_793_ = lean_string_append(v___x_791_, v___x_792_);
v___x_794_ = lean_string_append(v___x_793_, v_specialDescr_787_);
lean_dec_ref(v_specialDescr_787_);
return v___x_794_;
}
else
{
lean_object* v___x_795_; 
lean_dec_ref(v_specialDescr_787_);
v___x_795_ = l_Lake_SemVerCore_toString(v_toSemVerCore_786_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instToJson___lam__0(lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = l_Lake_StdVer_toString(v_x_798_);
v___x_800_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instFromJson___lam__0(lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Json_getStr_x3f(v_x_803_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_814_; 
v_a_813_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_804_, 1);
v___x_814_ = l_Lake_StdVer_parse(v_a_813_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx(lean_object* v_x_823_){
_start:
{
switch(lean_obj_tag(v_x_823_))
{
case 0:
{
lean_object* v___x_824_; 
v___x_824_ = lean_unsigned_to_nat(0u);
return v___x_824_;
}
case 1:
{
lean_object* v___x_825_; 
v___x_825_ = lean_unsigned_to_nat(1u);
return v___x_825_;
}
case 2:
{
lean_object* v___x_826_; 
v___x_826_ = lean_unsigned_to_nat(2u);
return v___x_826_;
}
default: 
{
lean_object* v___x_827_; 
v___x_827_ = lean_unsigned_to_nat(3u);
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___boxed(lean_object* v_x_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lake_ToolchainVer_ctorIdx(v_x_828_);
lean_dec_ref(v_x_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___redArg(lean_object* v_t_830_, lean_object* v_k_831_){
_start:
{
switch(lean_obj_tag(v_t_830_))
{
case 1:
{
lean_object* v_date_832_; lean_object* v_rev_833_; lean_object* v___x_834_; 
v_date_832_ = lean_ctor_get(v_t_830_, 0);
lean_inc_ref(v_date_832_);
v_rev_833_ = lean_ctor_get(v_t_830_, 1);
lean_inc(v_rev_833_);
lean_dec_ref_known(v_t_830_, 2);
v___x_834_ = lean_apply_2(v_k_831_, v_date_832_, v_rev_833_);
return v___x_834_;
}
case 2:
{
lean_object* v_n_835_; lean_object* v___x_836_; 
v_n_835_ = lean_ctor_get(v_t_830_, 0);
lean_inc(v_n_835_);
lean_dec_ref_known(v_t_830_, 1);
v___x_836_ = lean_apply_1(v_k_831_, v_n_835_);
return v___x_836_;
}
default: 
{
lean_object* v_ver_837_; lean_object* v___x_838_; 
v_ver_837_ = lean_ctor_get(v_t_830_, 0);
lean_inc_ref(v_ver_837_);
lean_dec_ref(v_t_830_);
v___x_838_ = lean_apply_1(v_k_831_, v_ver_837_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim(lean_object* v_motive_839_, lean_object* v_ctorIdx_840_, lean_object* v_t_841_, lean_object* v_h_842_, lean_object* v_k_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_841_, v_k_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___boxed(lean_object* v_motive_845_, lean_object* v_ctorIdx_846_, lean_object* v_t_847_, lean_object* v_h_848_, lean_object* v_k_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lake_ToolchainVer_ctorElim(v_motive_845_, v_ctorIdx_846_, v_t_847_, v_h_848_, v_k_849_);
lean_dec(v_ctorIdx_846_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim___redArg(lean_object* v_t_851_, lean_object* v_release_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_851_, v_release_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim(lean_object* v_motive_854_, lean_object* v_t_855_, lean_object* v_h_856_, lean_object* v_release_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_855_, v_release_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim___redArg(lean_object* v_t_859_, lean_object* v_nightly_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_859_, v_nightly_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim(lean_object* v_motive_862_, lean_object* v_t_863_, lean_object* v_h_864_, lean_object* v_nightly_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_863_, v_nightly_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim___redArg(lean_object* v_t_867_, lean_object* v_pr_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_867_, v_pr_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim(lean_object* v_motive_870_, lean_object* v_t_871_, lean_object* v_h_872_, lean_object* v_pr_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_871_, v_pr_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim___redArg(lean_object* v_t_875_, lean_object* v_other_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_875_, v_other_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim(lean_object* v_motive_878_, lean_object* v_t_879_, lean_object* v_h_880_, lean_object* v_other_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_879_, v_other_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override___redArg(lean_object* v_t_883_, lean_object* v_release_884_, lean_object* v_nightly_885_, lean_object* v_pr_886_, lean_object* v_other_887_){
_start:
{
switch(lean_obj_tag(v_t_883_))
{
case 0:
{
lean_object* v_ver_888_; lean_object* v___x_889_; 
lean_dec(v_other_887_);
lean_dec(v_pr_886_);
lean_dec(v_nightly_885_);
v_ver_888_ = lean_ctor_get(v_t_883_, 1);
lean_inc_ref(v_ver_888_);
lean_dec_ref_known(v_t_883_, 2);
v___x_889_ = lean_apply_1(v_release_884_, v_ver_888_);
return v___x_889_;
}
case 1:
{
lean_object* v_date_890_; lean_object* v_rev_891_; lean_object* v___x_892_; 
lean_dec(v_other_887_);
lean_dec(v_pr_886_);
lean_dec(v_release_884_);
v_date_890_ = lean_ctor_get(v_t_883_, 1);
lean_inc_ref(v_date_890_);
v_rev_891_ = lean_ctor_get(v_t_883_, 2);
lean_inc(v_rev_891_);
lean_dec_ref_known(v_t_883_, 3);
v___x_892_ = lean_apply_2(v_nightly_885_, v_date_890_, v_rev_891_);
return v___x_892_;
}
case 2:
{
lean_object* v_n_893_; lean_object* v___x_894_; 
lean_dec(v_other_887_);
lean_dec(v_nightly_885_);
lean_dec(v_release_884_);
v_n_893_ = lean_ctor_get(v_t_883_, 1);
lean_inc(v_n_893_);
lean_dec_ref_known(v_t_883_, 2);
v___x_894_ = lean_apply_1(v_pr_886_, v_n_893_);
return v___x_894_;
}
default: 
{
lean_object* v_v_895_; lean_object* v___x_896_; 
lean_dec(v_pr_886_);
lean_dec(v_nightly_885_);
lean_dec(v_release_884_);
v_v_895_ = lean_ctor_get(v_t_883_, 1);
lean_inc_ref(v_v_895_);
lean_dec_ref_known(v_t_883_, 2);
v___x_896_ = lean_apply_1(v_other_887_, v_v_895_);
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override(lean_object* v_motive_897_, lean_object* v_t_898_, lean_object* v_release_899_, lean_object* v_nightly_900_, lean_object* v_pr_901_, lean_object* v_other_902_){
_start:
{
switch(lean_obj_tag(v_t_898_))
{
case 0:
{
lean_object* v_ver_903_; lean_object* v___x_904_; 
lean_dec(v_other_902_);
lean_dec(v_pr_901_);
lean_dec(v_nightly_900_);
v_ver_903_ = lean_ctor_get(v_t_898_, 1);
lean_inc_ref(v_ver_903_);
lean_dec_ref_known(v_t_898_, 2);
v___x_904_ = lean_apply_1(v_release_899_, v_ver_903_);
return v___x_904_;
}
case 1:
{
lean_object* v_date_905_; lean_object* v_rev_906_; lean_object* v___x_907_; 
lean_dec(v_other_902_);
lean_dec(v_pr_901_);
lean_dec(v_release_899_);
v_date_905_ = lean_ctor_get(v_t_898_, 1);
lean_inc_ref(v_date_905_);
v_rev_906_ = lean_ctor_get(v_t_898_, 2);
lean_inc(v_rev_906_);
lean_dec_ref_known(v_t_898_, 3);
v___x_907_ = lean_apply_2(v_nightly_900_, v_date_905_, v_rev_906_);
return v___x_907_;
}
case 2:
{
lean_object* v_n_908_; lean_object* v___x_909_; 
lean_dec(v_other_902_);
lean_dec(v_nightly_900_);
lean_dec(v_release_899_);
v_n_908_ = lean_ctor_get(v_t_898_, 1);
lean_inc(v_n_908_);
lean_dec_ref_known(v_t_898_, 2);
v___x_909_ = lean_apply_1(v_pr_901_, v_n_908_);
return v___x_909_;
}
default: 
{
lean_object* v_v_910_; lean_object* v___x_911_; 
lean_dec(v_pr_901_);
lean_dec(v_nightly_900_);
lean_dec(v_release_899_);
v_v_910_ = lean_ctor_get(v_t_898_, 1);
lean_inc_ref(v_v_910_);
lean_dec_ref_known(v_t_898_, 2);
v___x_911_ = lean_apply_1(v_other_902_, v_v_910_);
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release___override(lean_object* v_ver_913_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_914_ = ((lean_object*)(l_Lake_ToolchainVer_release___override___closed__0));
lean_inc_ref(v_ver_913_);
v___x_915_ = l_Lake_StdVer_toString(v_ver_913_);
v___x_916_ = lean_string_append(v___x_914_, v___x_915_);
lean_dec_ref(v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v_ver_913_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly___override(lean_object* v_date_920_, lean_object* v_rev_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___y_926_; 
v___x_922_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__0));
lean_inc_ref(v_date_920_);
v___x_923_ = l_Lake_Date_toString(v_date_920_);
v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
lean_dec_ref(v___x_923_);
if (lean_obj_tag(v_rev_921_) == 0)
{
lean_object* v___x_929_; 
v___x_929_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___y_926_ = v___x_929_;
goto v___jp_925_;
}
else
{
lean_object* v_val_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_val_930_ = lean_ctor_get(v_rev_921_, 0);
v___x_931_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
lean_inc(v_val_930_);
v___x_932_ = l_Nat_reprFast(v_val_930_);
v___x_933_ = lean_string_append(v___x_931_, v___x_932_);
lean_dec_ref(v___x_932_);
v___y_926_ = v___x_933_;
goto v___jp_925_;
}
v___jp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_string_append(v___x_924_, v___y_926_);
lean_dec_ref(v___y_926_);
v___x_928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v_date_920_);
lean_ctor_set(v___x_928_, 2, v_rev_921_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr___override(lean_object* v_n_935_){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_936_ = ((lean_object*)(l_Lake_ToolchainVer_pr___override___closed__0));
lean_inc(v_n_935_);
v___x_937_ = l_Nat_reprFast(v_n_935_);
v___x_938_ = lean_string_append(v___x_936_, v___x_937_);
lean_dec_ref(v___x_937_);
v___x_939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_n_935_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other___override(lean_object* v_v_940_){
_start:
{
lean_object* v___x_941_; 
lean_inc_ref(v_v_940_);
v___x_941_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_941_, 0, v_v_940_);
lean_ctor_set(v___x_941_, 1, v_v_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override(lean_object* v_x_942_){
_start:
{
lean_object* v_toString_943_; 
v_toString_943_ = lean_ctor_get(v_x_942_, 0);
lean_inc_ref(v_toString_943_);
return v_toString_943_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override___boxed(lean_object* v_x_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lake_ToolchainVer_toString___override(v_x_944_);
lean_dec_ref(v_x_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
if (lean_obj_tag(v_x_952_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1));
return v___x_954_;
}
else
{
lean_object* v_val_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_966_; 
v_val_955_ = lean_ctor_get(v_x_952_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v_x_952_);
if (v_isSharedCheck_966_ == 0)
{
v___x_957_ = v_x_952_;
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_val_955_);
lean_dec(v_x_952_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_959_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3));
v___x_960_ = l_Nat_reprFast(v_val_955_);
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 3);
lean_ctor_set(v___x_957_, 0, v___x_960_);
v___x_962_ = v___x_957_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_965_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_959_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Repr_addAppParen(v___x_963_, v_x_953_);
return v___x_964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___boxed(lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_x_967_, v_x_968_);
lean_dec(v_x_968_);
return v_res_969_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__3(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_unsigned_to_nat(2u);
v___x_977_ = lean_nat_to_int(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__4(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_unsigned_to_nat(1u);
v___x_979_ = lean_nat_to_int(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr(lean_object* v_x_998_, lean_object* v_prec_999_){
_start:
{
switch(lean_obj_tag(v_x_998_))
{
case 0:
{
lean_object* v_ver_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1019_; 
v_ver_1000_ = lean_ctor_get(v_x_998_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_x_998_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; 
v_unused_1020_ = lean_ctor_get(v_x_998_, 0);
lean_dec(v_unused_1020_);
v___x_1002_ = v_x_998_;
v_isShared_1003_ = v_isSharedCheck_1019_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_ver_1000_);
lean_dec(v_x_998_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1019_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___y_1005_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(1024u);
v___x_1016_ = lean_nat_dec_le(v___x_1015_, v_prec_999_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1005_ = v___x_1017_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1005_ = v___x_1018_;
goto v___jp_1004_;
}
v___jp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1006_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__2));
v___x_1007_ = l_Lake_instReprStdVer_repr___redArg(v_ver_1000_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 5);
lean_ctor_set(v___x_1002_, 1, v___x_1007_);
lean_ctor_set(v___x_1002_, 0, v___x_1006_);
v___x_1009_ = v___x_1002_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_inc(v___y_1005_);
v___x_1010_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___y_1005_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = 0;
v___x_1012_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*1, v___x_1011_);
v___x_1013_ = l_Repr_addAppParen(v___x_1012_, v_prec_999_);
return v___x_1013_;
}
}
}
}
case 1:
{
lean_object* v_date_1021_; lean_object* v_rev_1022_; lean_object* v___y_1024_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_date_1021_ = lean_ctor_get(v_x_998_, 1);
lean_inc_ref(v_date_1021_);
v_rev_1022_ = lean_ctor_get(v_x_998_, 2);
lean_inc(v_rev_1022_);
lean_dec_ref_known(v_x_998_, 3);
v___x_1037_ = lean_unsigned_to_nat(1024u);
v___x_1038_ = lean_nat_dec_le(v___x_1037_, v_prec_999_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1024_ = v___x_1039_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1024_ = v___x_1040_;
goto v___jp_1023_;
}
v___jp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1025_ = lean_box(1);
v___x_1026_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__7));
v___x_1027_ = lean_unsigned_to_nat(1024u);
v___x_1028_ = l_Lake_instReprDate_repr___redArg(v_date_1021_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1026_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1025_);
v___x_1031_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_rev_1022_, v___x_1027_);
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
lean_inc(v___y_1024_);
v___x_1033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___y_1024_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = 0;
v___x_1035_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*1, v___x_1034_);
v___x_1036_ = l_Repr_addAppParen(v___x_1035_, v_prec_999_);
return v___x_1036_;
}
}
case 2:
{
lean_object* v_n_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1061_; 
v_n_1041_ = lean_ctor_get(v_x_998_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_x_998_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_x_998_, 0);
lean_dec(v_unused_1062_);
v___x_1043_ = v_x_998_;
v_isShared_1044_ = v_isSharedCheck_1061_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_n_1041_);
lean_dec(v_x_998_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1061_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___y_1046_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(1024u);
v___x_1058_ = lean_nat_dec_le(v___x_1057_, v_prec_999_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1046_ = v___x_1059_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1046_ = v___x_1060_;
goto v___jp_1045_;
}
v___jp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1047_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__10));
v___x_1048_ = l_Nat_reprFast(v_n_1041_);
v___x_1049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 5);
lean_ctor_set(v___x_1043_, 1, v___x_1049_);
lean_ctor_set(v___x_1043_, 0, v___x_1047_);
v___x_1051_ = v___x_1043_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_inc(v___y_1046_);
v___x_1052_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___y_1046_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = 0;
v___x_1054_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*1, v___x_1053_);
v___x_1055_ = l_Repr_addAppParen(v___x_1054_, v_prec_999_);
return v___x_1055_;
}
}
}
}
default: 
{
lean_object* v_v_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1083_; 
v_v_1063_ = lean_ctor_get(v_x_998_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_x_998_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_x_998_, 0);
lean_dec(v_unused_1084_);
v___x_1065_ = v_x_998_;
v_isShared_1066_ = v_isSharedCheck_1083_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_v_1063_);
lean_dec(v_x_998_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1083_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___y_1068_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_unsigned_to_nat(1024u);
v___x_1080_ = lean_nat_dec_le(v___x_1079_, v_prec_999_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1068_ = v___x_1081_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1068_ = v___x_1082_;
goto v___jp_1067_;
}
v___jp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1069_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__13));
v___x_1070_ = l_String_quote(v_v_1063_);
v___x_1071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 5);
lean_ctor_set(v___x_1065_, 1, v___x_1071_);
lean_ctor_set(v___x_1065_, 0, v___x_1069_);
v___x_1073_ = v___x_1065_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_inc(v___y_1068_);
v___x_1074_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___y_1068_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = 0;
v___x_1076_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*1, v___x_1075_);
v___x_1077_ = l_Repr_addAppParen(v___x_1076_, v_prec_999_);
return v___x_1077_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr___boxed(lean_object* v_x_1085_, lean_object* v_prec_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lake_instReprToolchainVer_repr(v_x_1085_, v_prec_1086_);
lean_dec(v_prec_1086_);
return v_res_1087_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer_decEq(lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
switch(lean_obj_tag(v_x_1090_))
{
case 0:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_object* v_ver_1092_; lean_object* v_ver_1093_; uint8_t v___x_1094_; 
v_ver_1092_ = lean_ctor_get(v_x_1090_, 1);
lean_inc_ref(v_ver_1092_);
lean_dec_ref_known(v_x_1090_, 2);
v_ver_1093_ = lean_ctor_get(v_x_1091_, 1);
lean_inc_ref(v_ver_1093_);
lean_dec_ref_known(v_x_1091_, 2);
v___x_1094_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_1092_, v_ver_1093_);
lean_dec_ref(v_ver_1093_);
lean_dec_ref(v_ver_1092_);
return v___x_1094_;
}
else
{
uint8_t v___x_1095_; 
lean_dec_ref_known(v_x_1090_, 2);
lean_dec_ref(v_x_1091_);
v___x_1095_ = 0;
return v___x_1095_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1091_) == 1)
{
lean_object* v_date_1096_; lean_object* v_rev_1097_; lean_object* v_date_1098_; lean_object* v_rev_1099_; uint8_t v___x_1100_; 
v_date_1096_ = lean_ctor_get(v_x_1090_, 1);
lean_inc_ref(v_date_1096_);
v_rev_1097_ = lean_ctor_get(v_x_1090_, 2);
lean_inc(v_rev_1097_);
lean_dec_ref_known(v_x_1090_, 3);
v_date_1098_ = lean_ctor_get(v_x_1091_, 1);
lean_inc_ref(v_date_1098_);
v_rev_1099_ = lean_ctor_get(v_x_1091_, 2);
lean_inc(v_rev_1099_);
lean_dec_ref_known(v_x_1091_, 3);
v___x_1100_ = l_Lake_instDecidableEqDate_decEq(v_date_1096_, v_date_1098_);
lean_dec_ref(v_date_1098_);
lean_dec_ref(v_date_1096_);
if (v___x_1100_ == 0)
{
lean_dec(v_rev_1099_);
lean_dec(v_rev_1097_);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_1102_ = l_Option_instDecidableEq___redArg(v___x_1101_, v_rev_1097_, v_rev_1099_);
return v___x_1102_;
}
}
else
{
uint8_t v___x_1103_; 
lean_dec_ref_known(v_x_1090_, 3);
lean_dec_ref(v_x_1091_);
v___x_1103_ = 0;
return v___x_1103_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1091_) == 2)
{
lean_object* v_n_1104_; lean_object* v_n_1105_; uint8_t v___x_1106_; 
v_n_1104_ = lean_ctor_get(v_x_1090_, 1);
lean_inc(v_n_1104_);
lean_dec_ref_known(v_x_1090_, 2);
v_n_1105_ = lean_ctor_get(v_x_1091_, 1);
lean_inc(v_n_1105_);
lean_dec_ref_known(v_x_1091_, 2);
v___x_1106_ = lean_nat_dec_eq(v_n_1104_, v_n_1105_);
lean_dec(v_n_1105_);
lean_dec(v_n_1104_);
return v___x_1106_;
}
else
{
uint8_t v___x_1107_; 
lean_dec_ref_known(v_x_1090_, 2);
lean_dec_ref(v_x_1091_);
v___x_1107_ = 0;
return v___x_1107_;
}
}
default: 
{
if (lean_obj_tag(v_x_1091_) == 3)
{
lean_object* v_v_1108_; lean_object* v_v_1109_; uint8_t v___x_1110_; 
v_v_1108_ = lean_ctor_get(v_x_1090_, 1);
lean_inc_ref(v_v_1108_);
lean_dec_ref_known(v_x_1090_, 2);
v_v_1109_ = lean_ctor_get(v_x_1091_, 1);
lean_inc_ref(v_v_1109_);
lean_dec_ref_known(v_x_1091_, 2);
v___x_1110_ = lean_string_dec_eq(v_v_1108_, v_v_1109_);
lean_dec_ref(v_v_1109_);
lean_dec_ref(v_v_1108_);
return v___x_1110_;
}
else
{
uint8_t v___x_1111_; 
lean_dec_ref_known(v_x_1090_, 2);
lean_dec_ref(v_x_1091_);
v___x_1111_ = 0;
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer_decEq___boxed(lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1112_, v_x_1113_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer(lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
uint8_t v___x_1118_; 
v___x_1118_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1116_, v_x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer___boxed(lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Lake_instDecidableEqToolchainVer(v_x_1119_, v_x_1120_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1127_ = lean_string_utf8_byte_size(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(lean_object* v_s_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1129_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1130_ = lean_string_utf8_byte_size(v_s_1128_);
v___x_1131_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1);
v___x_1132_ = lean_nat_dec_le(v___x_1131_, v___x_1130_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec_ref(v_s_1128_);
v___x_1133_ = lean_box(0);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_string_memcmp(v_s_1128_, v___x_1129_, v___x_1134_, v___x_1134_, v___x_1131_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_dec_ref(v_s_1128_);
v___x_1136_ = lean_box(0);
return v___x_1136_;
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_inc_ref(v_s_1128_);
v___x_1137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1137_, 0, v_s_1128_);
lean_ctor_set(v___x_1137_, 1, v___x_1134_);
lean_ctor_set(v___x_1137_, 2, v___x_1130_);
v___x_1138_ = l_String_Slice_pos_x21(v___x_1137_, v___x_1131_);
lean_dec_ref_known(v___x_1137_, 3);
v___x_1139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1139_, 0, v_s_1128_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
lean_ctor_set(v___x_1139_, 2, v___x_1130_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(lean_object* v_s_1141_, lean_object* v_pat_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v_s_1141_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(lean_object* v_s_1144_, lean_object* v_pat_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(v_s_1144_, v_pat_1145_);
lean_dec_ref(v_pat_1145_);
return v_res_1146_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1148_ = lean_string_utf8_byte_size(v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(lean_object* v_s_1149_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1150_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1151_ = lean_string_utf8_byte_size(v_s_1149_);
v___x_1152_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0);
v___x_1153_ = lean_nat_dec_le(v___x_1152_, v___x_1151_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
lean_dec_ref(v_s_1149_);
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_string_memcmp(v_s_1149_, v___x_1150_, v___x_1155_, v___x_1155_, v___x_1152_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec_ref(v_s_1149_);
v___x_1157_ = lean_box(0);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_inc_ref(v_s_1149_);
v___x_1158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1158_, 0, v_s_1149_);
lean_ctor_set(v___x_1158_, 1, v___x_1155_);
lean_ctor_set(v___x_1158_, 2, v___x_1151_);
v___x_1159_ = l_String_Slice_pos_x21(v___x_1158_, v___x_1152_);
lean_dec_ref_known(v___x_1158_, 3);
v___x_1160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1160_, 0, v_s_1149_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
lean_ctor_set(v___x_1160_, 2, v___x_1151_);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(lean_object* v_s_1162_, lean_object* v_pat_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v_s_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(lean_object* v_s_1165_, lean_object* v_pat_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(v_s_1165_, v_pat_1166_);
lean_dec_ref(v_pat_1166_);
return v_res_1167_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0));
v___x_1170_ = lean_string_utf8_byte_size(v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object* v_s_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1172_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0));
v___x_1173_ = lean_string_utf8_byte_size(v_s_1171_);
v___x_1174_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1);
v___x_1175_ = lean_nat_dec_le(v___x_1174_, v___x_1173_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
lean_dec_ref(v_s_1171_);
v___x_1176_ = lean_box(0);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_string_memcmp(v_s_1171_, v___x_1172_, v___x_1177_, v___x_1177_, v___x_1174_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
lean_dec_ref(v_s_1171_);
v___x_1179_ = lean_box(0);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_inc_ref(v_s_1171_);
v___x_1180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1180_, 0, v_s_1171_);
lean_ctor_set(v___x_1180_, 1, v___x_1177_);
lean_ctor_set(v___x_1180_, 2, v___x_1173_);
v___x_1181_ = l_String_Slice_pos_x21(v___x_1180_, v___x_1174_);
lean_dec_ref_known(v___x_1180_, 3);
v___x_1182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1182_, 0, v_s_1171_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
lean_ctor_set(v___x_1182_, 2, v___x_1173_);
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(lean_object* v_s_1184_, lean_object* v_pat_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v_s_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object* v_s_1187_, lean_object* v_pat_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(v_s_1187_, v_pat_1188_);
lean_dec_ref(v_pat_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(lean_object* v___x_1190_, lean_object* v_ver_1191_, lean_object* v_a_1192_, lean_object* v_b_1193_){
_start:
{
uint8_t v_decide_1194_; 
v_decide_1194_ = lean_nat_dec_eq(v_a_1192_, v___x_1190_);
if (v_decide_1194_ == 0)
{
uint32_t v___x_1195_; uint32_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_string_utf8_get_fast(v_ver_1191_, v_a_1192_);
v___x_1196_ = 58;
v___x_1197_ = lean_uint32_dec_eq(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_string_utf8_next_fast(v_ver_1191_, v_a_1192_);
lean_dec(v_a_1192_);
v_a_1192_ = v___x_1199_;
v_b_1193_ = v___x_1198_;
goto _start;
}
else
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_a_1192_);
return v___x_1201_;
}
}
else
{
lean_dec(v_a_1192_);
lean_inc(v_b_1193_);
return v_b_1193_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg___boxed(lean_object* v___x_1202_, lean_object* v_ver_1203_, lean_object* v_a_1204_, lean_object* v_b_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1202_, v_ver_1203_, v_a_1204_, v_b_1205_);
lean_dec(v_b_1205_);
lean_dec_ref(v_ver_1203_);
lean_dec(v___x_1202_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object* v___x_1207_, lean_object* v_rest_1208_, lean_object* v_a_1209_, lean_object* v_b_1210_){
_start:
{
uint8_t v_decide_1211_; 
v_decide_1211_ = lean_nat_dec_eq(v_a_1209_, v___x_1207_);
if (v_decide_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_string_utf8_next_fast(v_rest_1208_, v_a_1209_);
lean_dec(v_a_1209_);
v___x_1213_ = lean_unsigned_to_nat(1u);
v___x_1214_ = lean_nat_add(v_b_1210_, v___x_1213_);
lean_dec(v_b_1210_);
v_a_1209_ = v___x_1212_;
v_b_1210_ = v___x_1214_;
goto _start;
}
else
{
lean_dec(v_a_1209_);
return v_b_1210_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg___boxed(lean_object* v___x_1216_, lean_object* v_rest_1217_, lean_object* v_a_1218_, lean_object* v_b_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___x_1216_, v_rest_1217_, v_a_1218_, v_b_1219_);
lean_dec_ref(v_rest_1217_);
lean_dec(v___x_1216_);
return v_res_1220_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__1(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1223_ = lean_string_utf8_byte_size(v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__2(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1225_ = lean_string_utf8_byte_size(v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__4(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__3));
v___x_1228_ = lean_string_utf8_byte_size(v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofString(lean_object* v_ver_1229_){
_start:
{
uint8_t v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; uint8_t v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; uint8_t v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v_fst_1326_; lean_object* v_snd_1327_; lean_object* v___y_1350_; lean_object* v_searcher_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_searcher_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_string_utf8_byte_size(v_ver_1229_);
v___x_1360_ = lean_box(0);
v___x_1361_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1359_, v_ver_1229_, v_searcher_1358_, v___x_1360_);
if (lean_obj_tag(v___x_1361_) == 0)
{
v___y_1350_ = v___x_1359_;
goto v___jp_1349_;
}
else
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v___y_1350_ = v_val_1362_;
goto v___jp_1349_;
}
v___jp_1230_:
{
if (v___y_1231_ == 0)
{
lean_object* v___x_1236_; 
v___x_1236_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v___y_1235_);
if (lean_obj_tag(v___x_1236_) == 1)
{
lean_object* v_val_1237_; lean_object* v_startInclusive_1238_; lean_object* v_endExclusive_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_val_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v_startInclusive_1238_ = lean_ctor_get(v_val_1237_, 1);
v_endExclusive_1239_ = lean_ctor_get(v_val_1237_, 2);
v___x_1240_ = lean_nat_sub(v_endExclusive_1239_, v_startInclusive_1238_);
v___x_1241_ = lean_nat_dec_eq(v___x_1240_, v___y_1232_);
lean_dec(v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1242_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1243_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__1, &l_Lake_ToolchainVer_ofString___closed__1_once, _init_l_Lake_ToolchainVer_ofString___closed__1);
v___x_1244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___y_1232_);
lean_ctor_set(v___x_1244_, 2, v___x_1243_);
v___x_1245_ = l_String_Slice_beq(v_val_1237_, v___x_1244_);
lean_dec_ref_known(v___x_1244_, 3);
lean_dec(v_val_1237_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_inc_ref(v_ver_1229_);
v___x_1246_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_ver_1229_);
lean_ctor_set(v___x_1246_, 1, v_ver_1229_);
return v___x_1246_;
}
else
{
lean_object* v___x_1247_; 
lean_dec_ref(v_ver_1229_);
v___x_1247_ = l_Lake_ToolchainVer_nightly___override(v___y_1234_, v___y_1233_);
return v___x_1247_;
}
}
else
{
lean_object* v___x_1248_; 
lean_dec(v_val_1237_);
lean_dec(v___y_1232_);
lean_dec_ref(v_ver_1229_);
v___x_1248_ = l_Lake_ToolchainVer_nightly___override(v___y_1234_, v___y_1233_);
return v___x_1248_;
}
}
else
{
lean_object* v___x_1249_; 
lean_dec(v___x_1236_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec(v___y_1232_);
lean_inc_ref(v_ver_1229_);
v___x_1249_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_ver_1229_);
lean_ctor_set(v___x_1249_, 1, v_ver_1229_);
return v___x_1249_;
}
}
else
{
lean_object* v___x_1250_; 
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1232_);
lean_dec_ref(v_ver_1229_);
v___x_1250_ = l_Lake_ToolchainVer_nightly___override(v___y_1234_, v___y_1233_);
return v___x_1250_;
}
}
v___jp_1251_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1261_ = l_String_Slice_positions(v___y_1254_);
lean_dec_ref(v___y_1254_);
lean_inc(v___y_1253_);
v___x_1262_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___y_1257_, v___y_1259_, v___x_1261_, v___y_1253_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1257_);
v___x_1263_ = lean_nat_dec_le(v___x_1262_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec(v___x_1262_);
if (v___x_1263_ == 0)
{
if (lean_obj_tag(v___y_1260_) == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1253_);
lean_inc_ref(v_ver_1229_);
v___x_1264_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_ver_1229_);
lean_ctor_set(v___x_1264_, 1, v_ver_1229_);
return v___x_1264_;
}
else
{
v___y_1231_ = v___y_1252_;
v___y_1232_ = v___y_1253_;
v___y_1233_ = v___y_1260_;
v___y_1234_ = v___y_1256_;
v___y_1235_ = v___y_1255_;
goto v___jp_1230_;
}
}
else
{
v___y_1231_ = v___y_1252_;
v___y_1232_ = v___y_1253_;
v___y_1233_ = v___y_1260_;
v___y_1234_ = v___y_1256_;
v___y_1235_ = v___y_1255_;
goto v___jp_1230_;
}
}
v___jp_1265_:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_box(0);
v___y_1252_ = v___y_1266_;
v___y_1253_ = v___y_1267_;
v___y_1254_ = v___y_1268_;
v___y_1255_ = v___y_1270_;
v___y_1256_ = v___y_1269_;
v___y_1257_ = v___y_1271_;
v___y_1258_ = v___y_1273_;
v___y_1259_ = v___y_1272_;
v___y_1260_ = v___x_1274_;
goto v___jp_1251_;
}
v___jp_1275_:
{
lean_object* v___x_1280_; 
lean_inc_ref(v___y_1279_);
v___x_1280_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v___y_1279_);
if (lean_obj_tag(v___x_1280_) == 1)
{
lean_object* v_val_1281_; lean_object* v_rest_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec_ref(v___y_1279_);
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v_rest_1282_ = l_String_Slice_toString(v_val_1281_);
lean_dec(v_val_1281_);
v___x_1283_ = lean_unsigned_to_nat(10u);
v___x_1284_ = lean_string_utf8_byte_size(v_rest_1282_);
lean_inc_n(v___y_1277_, 3);
lean_inc_ref_n(v_rest_1282_, 2);
v___x_1285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1285_, 0, v_rest_1282_);
lean_ctor_set(v___x_1285_, 1, v___y_1277_);
lean_ctor_set(v___x_1285_, 2, v___x_1284_);
v___x_1286_ = l_String_Slice_Pos_nextn(v___x_1285_, v___y_1277_, v___x_1283_);
lean_inc(v___x_1286_);
v___x_1287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1287_, 0, v_rest_1282_);
lean_ctor_set(v___x_1287_, 1, v___y_1277_);
lean_ctor_set(v___x_1287_, 2, v___x_1286_);
v___x_1288_ = l_String_Slice_toString(v___x_1287_);
lean_dec_ref_known(v___x_1287_, 3);
v___x_1289_ = l_Lake_Date_ofString_x3f(v___x_1288_);
if (lean_obj_tag(v___x_1289_) == 1)
{
lean_object* v_val_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_val_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_val_1290_);
lean_dec_ref_known(v___x_1289_, 1);
v___x_1291_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1292_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__2, &l_Lake_ToolchainVer_ofString___closed__2_once, _init_l_Lake_ToolchainVer_ofString___closed__2);
v___x_1293_ = lean_nat_sub(v___x_1284_, v___x_1286_);
v___x_1294_ = lean_nat_dec_le(v___x_1292_, v___x_1293_);
lean_dec(v___x_1293_);
if (v___x_1294_ == 0)
{
lean_dec(v___x_1286_);
v___y_1266_ = v___y_1276_;
v___y_1267_ = v___y_1277_;
v___y_1268_ = v___x_1285_;
v___y_1269_ = v_val_1290_;
v___y_1270_ = v___y_1278_;
v___y_1271_ = v___x_1284_;
v___y_1272_ = v_rest_1282_;
v___y_1273_ = v___x_1283_;
goto v___jp_1265_;
}
else
{
uint8_t v___x_1295_; 
v___x_1295_ = lean_string_memcmp(v_rest_1282_, v___x_1291_, v___x_1286_, v___y_1277_, v___x_1292_);
if (v___x_1295_ == 0)
{
lean_dec(v___x_1286_);
v___y_1266_ = v___y_1276_;
v___y_1267_ = v___y_1277_;
v___y_1268_ = v___x_1285_;
v___y_1269_ = v_val_1290_;
v___y_1270_ = v___y_1278_;
v___y_1271_ = v___x_1284_;
v___y_1272_ = v_rest_1282_;
v___y_1273_ = v___x_1283_;
goto v___jp_1265_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_inc(v___x_1286_);
lean_inc_ref_n(v_rest_1282_, 2);
v___x_1296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1296_, 0, v_rest_1282_);
lean_ctor_set(v___x_1296_, 1, v___x_1286_);
lean_ctor_set(v___x_1296_, 2, v___x_1284_);
v___x_1297_ = l_String_Slice_pos_x21(v___x_1296_, v___x_1292_);
lean_dec_ref_known(v___x_1296_, 3);
v___x_1298_ = lean_nat_add(v___x_1286_, v___x_1297_);
lean_dec(v___x_1297_);
lean_dec(v___x_1286_);
v___x_1299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1299_, 0, v_rest_1282_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
lean_ctor_set(v___x_1299_, 2, v___x_1284_);
v___x_1300_ = l_String_Slice_toString(v___x_1299_);
lean_dec_ref_known(v___x_1299_, 3);
v___x_1301_ = lean_string_utf8_byte_size(v___x_1300_);
lean_inc(v___y_1277_);
v___x_1302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___y_1277_);
lean_ctor_set(v___x_1302_, 2, v___x_1301_);
v___x_1303_ = l_String_Slice_toNat_x3f(v___x_1302_);
lean_dec_ref_known(v___x_1302_, 3);
v___y_1252_ = v___y_1276_;
v___y_1253_ = v___y_1277_;
v___y_1254_ = v___x_1285_;
v___y_1255_ = v___y_1278_;
v___y_1256_ = v_val_1290_;
v___y_1257_ = v___x_1284_;
v___y_1258_ = v___x_1283_;
v___y_1259_ = v_rest_1282_;
v___y_1260_ = v___x_1303_;
goto v___jp_1251_;
}
}
}
else
{
lean_object* v___x_1304_; 
lean_dec(v___x_1289_);
lean_dec(v___x_1286_);
lean_dec_ref_known(v___x_1285_, 3);
lean_dec_ref(v_rest_1282_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_inc_ref(v_ver_1229_);
v___x_1304_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1304_, 0, v_ver_1229_);
lean_ctor_set(v___x_1304_, 1, v_ver_1229_);
return v___x_1304_;
}
}
else
{
lean_object* v___x_1305_; 
lean_dec(v___x_1280_);
lean_dec(v___y_1277_);
v___x_1305_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___y_1279_);
if (lean_obj_tag(v___x_1305_) == 1)
{
lean_object* v_val_1306_; lean_object* v___x_1307_; 
v_val_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_val_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = l_String_Slice_toNat_x3f(v_val_1306_);
lean_dec(v_val_1306_);
if (lean_obj_tag(v___x_1307_) == 1)
{
if (v___y_1276_ == 0)
{
lean_object* v_val_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_val_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1309_ = ((lean_object*)(l_Lake_ToolchainVer_prOrigin___closed__0));
v___x_1310_ = lean_string_dec_eq(v___y_1278_, v___x_1309_);
lean_dec_ref(v___y_1278_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
lean_dec(v_val_1308_);
lean_inc_ref(v_ver_1229_);
v___x_1311_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1311_, 0, v_ver_1229_);
lean_ctor_set(v___x_1311_, 1, v_ver_1229_);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; 
lean_dec_ref(v_ver_1229_);
v___x_1312_ = l_Lake_ToolchainVer_pr___override(v_val_1308_);
return v___x_1312_;
}
}
else
{
lean_object* v_val_1313_; lean_object* v___x_1314_; 
lean_dec_ref(v___y_1278_);
lean_dec_ref(v_ver_1229_);
v_val_1313_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1314_ = l_Lake_ToolchainVer_pr___override(v_val_1313_);
return v___x_1314_;
}
}
else
{
lean_object* v___x_1315_; 
lean_dec(v___x_1307_);
lean_dec_ref(v___y_1278_);
lean_inc_ref(v_ver_1229_);
v___x_1315_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1315_, 0, v_ver_1229_);
lean_ctor_set(v___x_1315_, 1, v_ver_1229_);
return v___x_1315_;
}
}
else
{
lean_object* v___x_1316_; 
lean_dec(v___x_1305_);
lean_inc_ref(v_ver_1229_);
v___x_1316_ = l_Lake_StdVer_parse(v_ver_1229_);
if (lean_obj_tag(v___x_1316_) == 1)
{
if (v___y_1276_ == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1319_ = lean_string_dec_eq(v___y_1278_, v___x_1318_);
lean_dec_ref(v___y_1278_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_dec(v_a_1317_);
lean_inc_ref(v_ver_1229_);
v___x_1320_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_ver_1229_);
lean_ctor_set(v___x_1320_, 1, v_ver_1229_);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; 
lean_dec_ref(v_ver_1229_);
v___x_1321_ = l_Lake_ToolchainVer_release___override(v_a_1317_);
return v___x_1321_;
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1323_; 
lean_dec_ref(v___y_1278_);
lean_dec_ref(v_ver_1229_);
v_a_1322_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1323_ = l_Lake_ToolchainVer_release___override(v_a_1322_);
return v___x_1323_;
}
}
else
{
lean_object* v___x_1324_; 
lean_dec_ref(v___x_1316_);
lean_dec_ref(v___y_1278_);
lean_inc_ref(v_ver_1229_);
v___x_1324_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_ver_1229_);
lean_ctor_set(v___x_1324_, 1, v_ver_1229_);
return v___x_1324_;
}
}
}
}
v___jp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v_noOrigin_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1328_ = lean_string_utf8_byte_size(v_fst_1326_);
v___x_1329_ = lean_unsigned_to_nat(0u);
v_noOrigin_1330_ = lean_nat_dec_eq(v___x_1328_, v___x_1329_);
v___x_1331_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__3));
v___x_1332_ = lean_string_utf8_byte_size(v_snd_1327_);
v___x_1333_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__4, &l_Lake_ToolchainVer_ofString___closed__4_once, _init_l_Lake_ToolchainVer_ofString___closed__4);
v___x_1334_ = lean_nat_dec_le(v___x_1333_, v___x_1332_);
if (v___x_1334_ == 0)
{
v___y_1276_ = v_noOrigin_1330_;
v___y_1277_ = v___x_1329_;
v___y_1278_ = v_fst_1326_;
v___y_1279_ = v_snd_1327_;
goto v___jp_1275_;
}
else
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_string_memcmp(v_snd_1327_, v___x_1331_, v___x_1329_, v___x_1329_, v___x_1333_);
if (v___x_1335_ == 0)
{
v___y_1276_ = v_noOrigin_1330_;
v___y_1277_ = v___x_1329_;
v___y_1278_ = v_fst_1326_;
v___y_1279_ = v_snd_1327_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1336_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_snd_1327_);
v___x_1337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1337_, 0, v_snd_1327_);
lean_ctor_set(v___x_1337_, 1, v___x_1329_);
lean_ctor_set(v___x_1337_, 2, v___x_1332_);
v___x_1338_ = l_String_Slice_Pos_nextn(v___x_1337_, v___x_1329_, v___x_1336_);
lean_dec_ref_known(v___x_1337_, 3);
v___x_1339_ = lean_string_utf8_extract_fast(v_snd_1327_, v___x_1338_, v___x_1332_);
lean_dec(v___x_1338_);
lean_dec_ref(v_snd_1327_);
v___x_1340_ = l_Lake_StdVer_parse(v___x_1339_);
if (lean_obj_tag(v___x_1340_) == 1)
{
if (v_noOrigin_1330_ == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1343_ = lean_string_dec_eq(v_fst_1326_, v___x_1342_);
lean_dec_ref(v_fst_1326_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec(v_a_1341_);
lean_inc_ref(v_ver_1229_);
v___x_1344_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_ver_1229_);
lean_ctor_set(v___x_1344_, 1, v_ver_1229_);
return v___x_1344_;
}
else
{
lean_object* v___x_1345_; 
lean_dec_ref(v_ver_1229_);
v___x_1345_ = l_Lake_ToolchainVer_release___override(v_a_1341_);
return v___x_1345_;
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1347_; 
lean_dec_ref(v_fst_1326_);
lean_dec_ref(v_ver_1229_);
v_a_1346_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1347_ = l_Lake_ToolchainVer_release___override(v_a_1346_);
return v___x_1347_;
}
}
else
{
lean_object* v___x_1348_; 
lean_dec_ref(v___x_1340_);
lean_dec_ref(v_fst_1326_);
lean_inc_ref(v_ver_1229_);
v___x_1348_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_ver_1229_);
lean_ctor_set(v___x_1348_, 1, v_ver_1229_);
return v___x_1348_;
}
}
}
}
v___jp_1349_:
{
lean_object* v___x_1351_; uint8_t v_decide_1352_; 
v___x_1351_ = lean_string_utf8_byte_size(v_ver_1229_);
v_decide_1352_ = lean_nat_dec_eq(v___y_1350_, v___x_1351_);
if (v_decide_1352_ == 0)
{
lean_object* v_pos_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_pos_1353_ = lean_string_utf8_next_fast(v_ver_1229_, v___y_1350_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_string_utf8_extract_fast(v_ver_1229_, v___x_1354_, v___y_1350_);
lean_dec(v___y_1350_);
v___x_1356_ = lean_string_utf8_extract_fast(v_ver_1229_, v_pos_1353_, v___x_1351_);
v_fst_1326_ = v___x_1355_;
v_snd_1327_ = v___x_1356_;
goto v___jp_1325_;
}
else
{
lean_object* v___x_1357_; 
lean_dec(v___y_1350_);
v___x_1357_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
lean_inc_ref(v_ver_1229_);
v_fst_1326_ = v___x_1357_;
v_snd_1327_ = v_ver_1229_;
goto v___jp_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(lean_object* v___x_1363_, lean_object* v___x_1364_, lean_object* v_rest_1365_, lean_object* v_inst_1366_, lean_object* v_R_1367_, lean_object* v_a_1368_, lean_object* v_b_1369_, lean_object* v_c_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___x_1363_, v_rest_1365_, v_a_1368_, v_b_1369_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object* v___x_1372_, lean_object* v___x_1373_, lean_object* v_rest_1374_, lean_object* v_inst_1375_, lean_object* v_R_1376_, lean_object* v_a_1377_, lean_object* v_b_1378_, lean_object* v_c_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(v___x_1372_, v___x_1373_, v_rest_1374_, v_inst_1375_, v_R_1376_, v_a_1377_, v_b_1378_, v_c_1379_);
lean_dec_ref(v_rest_1374_);
lean_dec_ref(v___x_1373_);
lean_dec(v___x_1372_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(lean_object* v___x_1381_, lean_object* v___x_1382_, lean_object* v_ver_1383_, lean_object* v_inst_1384_, lean_object* v_R_1385_, lean_object* v_a_1386_, lean_object* v_b_1387_, lean_object* v_c_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1381_, v_ver_1383_, v_a_1386_, v_b_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___boxed(lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v_ver_1392_, lean_object* v_inst_1393_, lean_object* v_R_1394_, lean_object* v_a_1395_, lean_object* v_b_1396_, lean_object* v_c_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(v___x_1390_, v___x_1391_, v_ver_1392_, v_inst_1393_, v_R_1394_, v_a_1395_, v_b_1396_, v_c_1397_);
lean_dec(v_b_1396_);
lean_dec_ref(v_ver_1392_);
lean_dec_ref(v___x_1391_);
lean_dec(v___x_1390_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object* v_toolchainFile_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_IO_FS_readFile(v_toolchainFile_1399_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1419_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1419_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1419_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v_str_1410_; lean_object* v_startInclusive_1411_; lean_object* v_endExclusive_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = lean_string_utf8_byte_size(v_a_1402_);
v___x_1408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1408_, 0, v_a_1402_);
lean_ctor_set(v___x_1408_, 1, v___x_1406_);
lean_ctor_set(v___x_1408_, 2, v___x_1407_);
v___x_1409_ = l_String_Slice_trimAscii(v___x_1408_);
v_str_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc_ref(v_str_1410_);
v_startInclusive_1411_ = lean_ctor_get(v___x_1409_, 1);
lean_inc(v_startInclusive_1411_);
v_endExclusive_1412_ = lean_ctor_get(v___x_1409_, 2);
lean_inc(v_endExclusive_1412_);
lean_dec_ref(v___x_1409_);
v___x_1413_ = lean_string_utf8_extract_fast(v_str_1410_, v_startInclusive_1411_, v_endExclusive_1412_);
lean_dec(v_endExclusive_1412_);
lean_dec(v_startInclusive_1411_);
lean_dec_ref(v_str_1410_);
v___x_1414_ = l_Lake_ToolchainVer_ofString(v___x_1413_);
v___x_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1415_);
v___x_1417_ = v___x_1404_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1431_; 
v_a_1420_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1422_ = v___x_1401_;
v_isShared_1423_ = v_isSharedCheck_1431_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1401_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1431_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
if (lean_obj_tag(v_a_1420_) == 11)
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
lean_dec_ref_known(v_a_1420_, 2);
v___x_1424_ = lean_box(0);
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
else
{
lean_object* v___x_1429_; 
if (v_isShared_1423_ == 0)
{
v___x_1429_ = v___x_1422_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1420_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f___boxed(lean_object* v_toolchainFile_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lake_ToolchainVer_ofFile_x3f(v_toolchainFile_1432_);
lean_dec_ref(v_toolchainFile_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f(lean_object* v_dir_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = ((lean_object*)(l_Lake_toolchainFileName___closed__0));
v___x_1438_ = l_System_FilePath_join(v_dir_1435_, v___x_1437_);
v___x_1439_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1438_);
lean_dec_ref(v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f___boxed(lean_object* v_dir_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lake_ToolchainVer_ofDir_x3f(v_dir_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0(lean_object* v_x_1445_){
_start:
{
lean_object* v_toString_1446_; lean_object* v___x_1447_; 
v_toString_1446_ = lean_ctor_get(v_x_1445_, 0);
lean_inc_ref(v_toString_1446_);
v___x_1447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_toString_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0___boxed(lean_object* v_x_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lake_ToolchainVer_instToJson___lam__0(v_x_1448_);
lean_dec_ref(v_x_1448_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instFromJson___lam__0(lean_object* v_x_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_Json_getStr_x3f(v_x_1452_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_a_1462_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1464_ = v___x_1453_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1453_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = l_Lake_ToolchainVer_ofString(v_a_1462_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_blt(lean_object* v_a_1473_, lean_object* v_b_1474_){
_start:
{
switch(lean_obj_tag(v_a_1473_))
{
case 0:
{
if (lean_obj_tag(v_b_1474_) == 0)
{
lean_object* v_ver_1475_; lean_object* v_ver_1476_; uint8_t v___x_1477_; 
v_ver_1475_ = lean_ctor_get(v_a_1473_, 1);
v_ver_1476_ = lean_ctor_get(v_b_1474_, 1);
v___x_1477_ = l_Lake_StdVer_compare(v_ver_1475_, v_ver_1476_);
if (v___x_1477_ == 0)
{
uint8_t v___x_1478_; 
v___x_1478_ = 1;
return v___x_1478_;
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = 0;
return v___x_1479_;
}
}
else
{
uint8_t v___x_1480_; 
v___x_1480_ = 0;
return v___x_1480_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1474_) == 1)
{
lean_object* v_date_1481_; lean_object* v_rev_1482_; lean_object* v_date_1483_; lean_object* v_rev_1484_; lean_object* v___y_1486_; uint8_t v___x_1491_; 
v_date_1481_ = lean_ctor_get(v_a_1473_, 1);
v_rev_1482_ = lean_ctor_get(v_a_1473_, 2);
v_date_1483_ = lean_ctor_get(v_b_1474_, 1);
v_rev_1484_ = lean_ctor_get(v_b_1474_, 2);
v___x_1491_ = l_Lake_instOrdDate_ord(v_date_1481_, v_date_1483_);
if (v___x_1491_ == 0)
{
uint8_t v___x_1492_; 
v___x_1492_ = 1;
return v___x_1492_;
}
else
{
uint8_t v___x_1493_; 
v___x_1493_ = l_Lake_instDecidableEqDate_decEq(v_date_1481_, v_date_1483_);
if (v___x_1493_ == 0)
{
return v___x_1493_;
}
else
{
if (lean_obj_tag(v_rev_1482_) == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___y_1486_ = v___x_1494_;
goto v___jp_1485_;
}
else
{
lean_object* v_val_1495_; 
v_val_1495_ = lean_ctor_get(v_rev_1482_, 0);
v___y_1486_ = v_val_1495_;
goto v___jp_1485_;
}
}
}
v___jp_1485_:
{
if (lean_obj_tag(v_rev_1484_) == 0)
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = lean_nat_dec_lt(v___y_1486_, v___x_1487_);
return v___x_1488_;
}
else
{
lean_object* v_val_1489_; uint8_t v___x_1490_; 
v_val_1489_ = lean_ctor_get(v_rev_1484_, 0);
v___x_1490_ = lean_nat_dec_lt(v___y_1486_, v_val_1489_);
return v___x_1490_;
}
}
}
else
{
uint8_t v___x_1496_; 
v___x_1496_ = 0;
return v___x_1496_;
}
}
default: 
{
uint8_t v___x_1497_; 
v___x_1497_ = 0;
return v___x_1497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_blt___boxed(lean_object* v_a_1498_, lean_object* v_b_1499_){
_start:
{
uint8_t v_res_1500_; lean_object* v_r_1501_; 
v_res_1500_ = l_Lake_ToolchainVer_blt(v_a_1498_, v_b_1499_);
lean_dec_ref(v_b_1499_);
lean_dec_ref(v_a_1498_);
v_r_1501_ = lean_box(v_res_1500_);
return v_r_1501_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLT(void){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_box(0);
return v___x_1502_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLt(lean_object* v_a_1503_, lean_object* v_b_1504_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = l_Lake_ToolchainVer_blt(v_a_1503_, v_b_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLt___boxed(lean_object* v_a_1506_, lean_object* v_b_1507_){
_start:
{
uint8_t v_res_1508_; lean_object* v_r_1509_; 
v_res_1508_ = l_Lake_ToolchainVer_decLt(v_a_1506_, v_b_1507_);
lean_dec_ref(v_b_1507_);
lean_dec_ref(v_a_1506_);
v_r_1509_ = lean_box(v_res_1508_);
return v_r_1509_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_ble(lean_object* v_a_1510_, lean_object* v_b_1511_){
_start:
{
switch(lean_obj_tag(v_a_1510_))
{
case 0:
{
if (lean_obj_tag(v_b_1511_) == 0)
{
lean_object* v_ver_1512_; lean_object* v_ver_1513_; uint8_t v___x_1514_; 
v_ver_1512_ = lean_ctor_get(v_a_1510_, 1);
v_ver_1513_ = lean_ctor_get(v_b_1511_, 1);
v___x_1514_ = l_Lake_StdVer_compare(v_ver_1512_, v_ver_1513_);
if (v___x_1514_ == 2)
{
uint8_t v___x_1515_; 
v___x_1515_ = 0;
return v___x_1515_;
}
else
{
uint8_t v___x_1516_; 
v___x_1516_ = 1;
return v___x_1516_;
}
}
else
{
uint8_t v___x_1517_; 
v___x_1517_ = 0;
return v___x_1517_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1511_) == 1)
{
lean_object* v_date_1518_; lean_object* v_rev_1519_; lean_object* v_date_1520_; lean_object* v_rev_1521_; lean_object* v___y_1523_; uint8_t v___x_1528_; 
v_date_1518_ = lean_ctor_get(v_a_1510_, 1);
v_rev_1519_ = lean_ctor_get(v_a_1510_, 2);
v_date_1520_ = lean_ctor_get(v_b_1511_, 1);
v_rev_1521_ = lean_ctor_get(v_b_1511_, 2);
v___x_1528_ = l_Lake_instOrdDate_ord(v_date_1518_, v_date_1520_);
if (v___x_1528_ == 0)
{
uint8_t v___x_1529_; 
v___x_1529_ = 1;
return v___x_1529_;
}
else
{
uint8_t v___x_1530_; 
v___x_1530_ = l_Lake_instDecidableEqDate_decEq(v_date_1518_, v_date_1520_);
if (v___x_1530_ == 0)
{
return v___x_1530_;
}
else
{
if (lean_obj_tag(v_rev_1519_) == 0)
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_unsigned_to_nat(0u);
v___y_1523_ = v___x_1531_;
goto v___jp_1522_;
}
else
{
lean_object* v_val_1532_; 
v_val_1532_ = lean_ctor_get(v_rev_1519_, 0);
v___y_1523_ = v_val_1532_;
goto v___jp_1522_;
}
}
}
v___jp_1522_:
{
if (lean_obj_tag(v_rev_1521_) == 0)
{
lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = lean_nat_dec_le(v___y_1523_, v___x_1524_);
return v___x_1525_;
}
else
{
lean_object* v_val_1526_; uint8_t v___x_1527_; 
v_val_1526_ = lean_ctor_get(v_rev_1521_, 0);
v___x_1527_ = lean_nat_dec_le(v___y_1523_, v_val_1526_);
return v___x_1527_;
}
}
}
else
{
uint8_t v___x_1533_; 
v___x_1533_ = 0;
return v___x_1533_;
}
}
case 2:
{
if (lean_obj_tag(v_b_1511_) == 2)
{
lean_object* v_n_1534_; lean_object* v_n_1535_; uint8_t v___x_1536_; 
v_n_1534_ = lean_ctor_get(v_a_1510_, 1);
v_n_1535_ = lean_ctor_get(v_b_1511_, 1);
v___x_1536_ = lean_nat_dec_eq(v_n_1534_, v_n_1535_);
return v___x_1536_;
}
else
{
uint8_t v___x_1537_; 
v___x_1537_ = 0;
return v___x_1537_;
}
}
default: 
{
if (lean_obj_tag(v_b_1511_) == 3)
{
lean_object* v_v_1538_; lean_object* v_v_1539_; uint8_t v___x_1540_; 
v_v_1538_ = lean_ctor_get(v_a_1510_, 1);
v_v_1539_ = lean_ctor_get(v_b_1511_, 1);
v___x_1540_ = lean_string_dec_eq(v_v_1538_, v_v_1539_);
return v___x_1540_;
}
else
{
uint8_t v___x_1541_; 
v___x_1541_ = 0;
return v___x_1541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ble___boxed(lean_object* v_a_1542_, lean_object* v_b_1543_){
_start:
{
uint8_t v_res_1544_; lean_object* v_r_1545_; 
v_res_1544_ = l_Lake_ToolchainVer_ble(v_a_1542_, v_b_1543_);
lean_dec_ref(v_b_1543_);
lean_dec_ref(v_a_1542_);
v_r_1545_ = lean_box(v_res_1544_);
return v_r_1545_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLE(void){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_box(0);
return v___x_1546_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLe(lean_object* v_a_1547_, lean_object* v_b_1548_){
_start:
{
uint8_t v___x_1549_; 
v___x_1549_ = l_Lake_ToolchainVer_ble(v_a_1547_, v_b_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLe___boxed(lean_object* v_a_1550_, lean_object* v_b_1551_){
_start:
{
uint8_t v_res_1552_; lean_object* v_r_1553_; 
v_res_1552_ = l_Lake_ToolchainVer_decLe(v_a_1550_, v_b_1551_);
lean_dec_ref(v_b_1551_);
lean_dec_ref(v_a_1550_);
v_r_1553_ = lean_box(v_res_1552_);
return v_r_1553_;
}
}
LEAN_EXPORT lean_object* l_Lake_normalizeToolchain(lean_object* v_s_1554_){
_start:
{
lean_object* v___x_1555_; lean_object* v_toString_1556_; 
v___x_1555_ = l_Lake_ToolchainVer_ofString(v_s_1554_);
v_toString_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc_ref(v_toString_1556_);
lean_dec_ref(v___x_1555_);
return v_toString_1556_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeVersionToolchainVer___lam__0(lean_object* v_x_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = l_Lake_ToolchainVer_ofString(v_x_1561_);
v___x_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx(uint8_t v_x_1566_){
_start:
{
switch(v_x_1566_)
{
case 0:
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_unsigned_to_nat(0u);
return v___x_1567_;
}
case 1:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_unsigned_to_nat(1u);
return v___x_1568_;
}
case 2:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_unsigned_to_nat(2u);
return v___x_1569_;
}
case 3:
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_unsigned_to_nat(3u);
return v___x_1570_;
}
case 4:
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_unsigned_to_nat(4u);
return v___x_1571_;
}
default: 
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_unsigned_to_nat(5u);
return v___x_1572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___boxed(lean_object* v_x_1573_){
_start:
{
uint8_t v_x_boxed_1574_; lean_object* v_res_1575_; 
v_x_boxed_1574_ = lean_unbox(v_x_1573_);
v_res_1575_ = l_Lake_ComparatorOp_ctorIdx(v_x_boxed_1574_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg(lean_object* v_k_1576_){
_start:
{
lean_inc(v_k_1576_);
return v_k_1576_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg___boxed(lean_object* v_k_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lake_ComparatorOp_ctorElim___redArg(v_k_1577_);
lean_dec(v_k_1577_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim(lean_object* v_motive_1579_, lean_object* v_ctorIdx_1580_, uint8_t v_t_1581_, lean_object* v_h_1582_, lean_object* v_k_1583_){
_start:
{
lean_inc(v_k_1583_);
return v_k_1583_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___boxed(lean_object* v_motive_1584_, lean_object* v_ctorIdx_1585_, lean_object* v_t_1586_, lean_object* v_h_1587_, lean_object* v_k_1588_){
_start:
{
uint8_t v_t_boxed_1589_; lean_object* v_res_1590_; 
v_t_boxed_1589_ = lean_unbox(v_t_1586_);
v_res_1590_ = l_Lake_ComparatorOp_ctorElim(v_motive_1584_, v_ctorIdx_1585_, v_t_boxed_1589_, v_h_1587_, v_k_1588_);
lean_dec(v_k_1588_);
lean_dec(v_ctorIdx_1585_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg(lean_object* v_lt_1591_){
_start:
{
lean_inc(v_lt_1591_);
return v_lt_1591_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg___boxed(lean_object* v_lt_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lake_ComparatorOp_lt_elim___redArg(v_lt_1592_);
lean_dec(v_lt_1592_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim(lean_object* v_motive_1594_, uint8_t v_t_1595_, lean_object* v_h_1596_, lean_object* v_lt_1597_){
_start:
{
lean_inc(v_lt_1597_);
return v_lt_1597_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___boxed(lean_object* v_motive_1598_, lean_object* v_t_1599_, lean_object* v_h_1600_, lean_object* v_lt_1601_){
_start:
{
uint8_t v_t_boxed_1602_; lean_object* v_res_1603_; 
v_t_boxed_1602_ = lean_unbox(v_t_1599_);
v_res_1603_ = l_Lake_ComparatorOp_lt_elim(v_motive_1598_, v_t_boxed_1602_, v_h_1600_, v_lt_1601_);
lean_dec(v_lt_1601_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg(lean_object* v_le_1604_){
_start:
{
lean_inc(v_le_1604_);
return v_le_1604_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg___boxed(lean_object* v_le_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lake_ComparatorOp_le_elim___redArg(v_le_1605_);
lean_dec(v_le_1605_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim(lean_object* v_motive_1607_, uint8_t v_t_1608_, lean_object* v_h_1609_, lean_object* v_le_1610_){
_start:
{
lean_inc(v_le_1610_);
return v_le_1610_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___boxed(lean_object* v_motive_1611_, lean_object* v_t_1612_, lean_object* v_h_1613_, lean_object* v_le_1614_){
_start:
{
uint8_t v_t_boxed_1615_; lean_object* v_res_1616_; 
v_t_boxed_1615_ = lean_unbox(v_t_1612_);
v_res_1616_ = l_Lake_ComparatorOp_le_elim(v_motive_1611_, v_t_boxed_1615_, v_h_1613_, v_le_1614_);
lean_dec(v_le_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg(lean_object* v_gt_1617_){
_start:
{
lean_inc(v_gt_1617_);
return v_gt_1617_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg___boxed(lean_object* v_gt_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lake_ComparatorOp_gt_elim___redArg(v_gt_1618_);
lean_dec(v_gt_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim(lean_object* v_motive_1620_, uint8_t v_t_1621_, lean_object* v_h_1622_, lean_object* v_gt_1623_){
_start:
{
lean_inc(v_gt_1623_);
return v_gt_1623_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___boxed(lean_object* v_motive_1624_, lean_object* v_t_1625_, lean_object* v_h_1626_, lean_object* v_gt_1627_){
_start:
{
uint8_t v_t_boxed_1628_; lean_object* v_res_1629_; 
v_t_boxed_1628_ = lean_unbox(v_t_1625_);
v_res_1629_ = l_Lake_ComparatorOp_gt_elim(v_motive_1624_, v_t_boxed_1628_, v_h_1626_, v_gt_1627_);
lean_dec(v_gt_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg(lean_object* v_ge_1630_){
_start:
{
lean_inc(v_ge_1630_);
return v_ge_1630_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg___boxed(lean_object* v_ge_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lake_ComparatorOp_ge_elim___redArg(v_ge_1631_);
lean_dec(v_ge_1631_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim(lean_object* v_motive_1633_, uint8_t v_t_1634_, lean_object* v_h_1635_, lean_object* v_ge_1636_){
_start:
{
lean_inc(v_ge_1636_);
return v_ge_1636_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___boxed(lean_object* v_motive_1637_, lean_object* v_t_1638_, lean_object* v_h_1639_, lean_object* v_ge_1640_){
_start:
{
uint8_t v_t_boxed_1641_; lean_object* v_res_1642_; 
v_t_boxed_1641_ = lean_unbox(v_t_1638_);
v_res_1642_ = l_Lake_ComparatorOp_ge_elim(v_motive_1637_, v_t_boxed_1641_, v_h_1639_, v_ge_1640_);
lean_dec(v_ge_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg(lean_object* v_eq_1643_){
_start:
{
lean_inc(v_eq_1643_);
return v_eq_1643_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg___boxed(lean_object* v_eq_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lake_ComparatorOp_eq_elim___redArg(v_eq_1644_);
lean_dec(v_eq_1644_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim(lean_object* v_motive_1646_, uint8_t v_t_1647_, lean_object* v_h_1648_, lean_object* v_eq_1649_){
_start:
{
lean_inc(v_eq_1649_);
return v_eq_1649_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___boxed(lean_object* v_motive_1650_, lean_object* v_t_1651_, lean_object* v_h_1652_, lean_object* v_eq_1653_){
_start:
{
uint8_t v_t_boxed_1654_; lean_object* v_res_1655_; 
v_t_boxed_1654_ = lean_unbox(v_t_1651_);
v_res_1655_ = l_Lake_ComparatorOp_eq_elim(v_motive_1650_, v_t_boxed_1654_, v_h_1652_, v_eq_1653_);
lean_dec(v_eq_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg(lean_object* v_ne_1656_){
_start:
{
lean_inc(v_ne_1656_);
return v_ne_1656_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg___boxed(lean_object* v_ne_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lake_ComparatorOp_ne_elim___redArg(v_ne_1657_);
lean_dec(v_ne_1657_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim(lean_object* v_motive_1659_, uint8_t v_t_1660_, lean_object* v_h_1661_, lean_object* v_ne_1662_){
_start:
{
lean_inc(v_ne_1662_);
return v_ne_1662_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___boxed(lean_object* v_motive_1663_, lean_object* v_t_1664_, lean_object* v_h_1665_, lean_object* v_ne_1666_){
_start:
{
uint8_t v_t_boxed_1667_; lean_object* v_res_1668_; 
v_t_boxed_1667_ = lean_unbox(v_t_1664_);
v_res_1668_ = l_Lake_ComparatorOp_ne_elim(v_motive_1663_, v_t_boxed_1667_, v_h_1665_, v_ne_1666_);
lean_dec(v_ne_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr(uint8_t v_x_1687_, lean_object* v_prec_1688_){
_start:
{
lean_object* v___y_1690_; lean_object* v___y_1697_; lean_object* v___y_1704_; lean_object* v___y_1711_; lean_object* v___y_1718_; lean_object* v___y_1725_; 
switch(v_x_1687_)
{
case 0:
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = lean_unsigned_to_nat(1024u);
v___x_1732_ = lean_nat_dec_le(v___x_1731_, v_prec_1688_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1690_ = v___x_1733_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1690_ = v___x_1734_;
goto v___jp_1689_;
}
}
case 1:
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = lean_unsigned_to_nat(1024u);
v___x_1736_ = lean_nat_dec_le(v___x_1735_, v_prec_1688_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1697_ = v___x_1737_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1697_ = v___x_1738_;
goto v___jp_1696_;
}
}
case 2:
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_unsigned_to_nat(1024u);
v___x_1740_ = lean_nat_dec_le(v___x_1739_, v_prec_1688_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1704_ = v___x_1741_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1704_ = v___x_1742_;
goto v___jp_1703_;
}
}
case 3:
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = lean_unsigned_to_nat(1024u);
v___x_1744_ = lean_nat_dec_le(v___x_1743_, v_prec_1688_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1711_ = v___x_1745_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1711_ = v___x_1746_;
goto v___jp_1710_;
}
}
case 4:
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = lean_unsigned_to_nat(1024u);
v___x_1748_ = lean_nat_dec_le(v___x_1747_, v_prec_1688_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1718_ = v___x_1749_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1718_ = v___x_1750_;
goto v___jp_1717_;
}
}
default: 
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = lean_unsigned_to_nat(1024u);
v___x_1752_ = lean_nat_dec_le(v___x_1751_, v_prec_1688_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1725_ = v___x_1753_;
goto v___jp_1724_;
}
else
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1725_ = v___x_1754_;
goto v___jp_1724_;
}
}
}
v___jp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1691_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__1));
lean_inc(v___y_1690_);
v___x_1692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___y_1690_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = 0;
v___x_1694_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*1, v___x_1693_);
v___x_1695_ = l_Repr_addAppParen(v___x_1694_, v_prec_1688_);
return v___x_1695_;
}
v___jp_1696_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1698_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__3));
lean_inc(v___y_1697_);
v___x_1699_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___y_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = 0;
v___x_1701_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set_uint8(v___x_1701_, sizeof(void*)*1, v___x_1700_);
v___x_1702_ = l_Repr_addAppParen(v___x_1701_, v_prec_1688_);
return v___x_1702_;
}
v___jp_1703_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1705_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__5));
lean_inc(v___y_1704_);
v___x_1706_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___y_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = 0;
v___x_1708_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set_uint8(v___x_1708_, sizeof(void*)*1, v___x_1707_);
v___x_1709_ = l_Repr_addAppParen(v___x_1708_, v_prec_1688_);
return v___x_1709_;
}
v___jp_1710_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1712_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__7));
lean_inc(v___y_1711_);
v___x_1713_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___y_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = 0;
v___x_1715_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*1, v___x_1714_);
v___x_1716_ = l_Repr_addAppParen(v___x_1715_, v_prec_1688_);
return v___x_1716_;
}
v___jp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1719_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__9));
lean_inc(v___y_1718_);
v___x_1720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___y_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = 0;
v___x_1722_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*1, v___x_1721_);
v___x_1723_ = l_Repr_addAppParen(v___x_1722_, v_prec_1688_);
return v___x_1723_;
}
v___jp_1724_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1726_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__11));
lean_inc(v___y_1725_);
v___x_1727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___y_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = 0;
v___x_1729_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*1, v___x_1728_);
v___x_1730_ = l_Repr_addAppParen(v___x_1729_, v_prec_1688_);
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr___boxed(lean_object* v_x_1755_, lean_object* v_prec_1756_){
_start:
{
uint8_t v_x_329__boxed_1757_; lean_object* v_res_1758_; 
v_x_329__boxed_1757_ = lean_unbox(v_x_1755_);
v_res_1758_ = l_Lake_instReprComparatorOp_repr(v_x_329__boxed_1757_, v_prec_1756_);
lean_dec(v_prec_1756_);
return v_res_1758_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp_default(void){
_start:
{
uint8_t v___x_1761_; 
v___x_1761_ = 0;
return v___x_1761_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp(void){
_start:
{
uint8_t v___x_1762_; 
v___x_1762_ = 0;
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(lean_object* v_sym_1763_, uint8_t v_cmp_1764_, lean_object* v_t_1765_){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = lean_box(v_cmp_1764_);
lean_inc_ref(v_sym_1763_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_sym_1763_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_Data_Trie_insert___redArg(v_t_1765_, v_sym_1763_, v___x_1767_);
lean_dec_ref(v_sym_1763_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0___boxed(lean_object* v_sym_1769_, lean_object* v_cmp_1770_, lean_object* v_t_1771_){
_start:
{
uint8_t v_cmp_boxed_1772_; lean_object* v_res_1773_; 
v_cmp_boxed_1772_ = lean_unbox(v_cmp_1770_);
v_res_1773_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v_sym_1769_, v_cmp_boxed_1772_, v_t_1771_);
return v_res_1773_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9(void){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10(void){
_start:
{
lean_object* v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1784_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9);
v___x_1785_ = 0;
v___x_1786_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
v___x_1787_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1786_, v___x_1785_, v___x_1784_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11(void){
_start:
{
lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1788_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10);
v___x_1789_ = 1;
v___x_1790_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7));
v___x_1791_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1790_, v___x_1789_, v___x_1788_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12(void){
_start:
{
lean_object* v___x_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1792_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11);
v___x_1793_ = 1;
v___x_1794_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
v___x_1795_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1794_, v___x_1793_, v___x_1792_);
return v___x_1795_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13(void){
_start:
{
lean_object* v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1796_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12);
v___x_1797_ = 2;
v___x_1798_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
v___x_1799_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1798_, v___x_1797_, v___x_1796_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14(void){
_start:
{
lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1800_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13);
v___x_1801_ = 3;
v___x_1802_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4));
v___x_1803_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1802_, v___x_1801_, v___x_1800_);
return v___x_1803_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15(void){
_start:
{
lean_object* v___x_1804_; uint8_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1804_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14);
v___x_1805_ = 3;
v___x_1806_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
v___x_1807_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1806_, v___x_1805_, v___x_1804_);
return v___x_1807_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16(void){
_start:
{
lean_object* v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1808_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15);
v___x_1809_ = 4;
v___x_1810_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
v___x_1811_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1810_, v___x_1809_, v___x_1808_);
return v___x_1811_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17(void){
_start:
{
lean_object* v___x_1812_; uint8_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1812_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16);
v___x_1813_ = 5;
v___x_1814_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1));
v___x_1815_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1814_, v___x_1813_, v___x_1812_);
return v___x_1815_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18(void){
_start:
{
lean_object* v___x_1816_; uint8_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1816_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17);
v___x_1817_ = 5;
v___x_1818_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
v___x_1819_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1818_, v___x_1817_, v___x_1816_);
return v___x_1819_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie(void){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(lean_object* v_s_1823_, lean_object* v_p_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie;
v___x_1826_ = lean_string_utf8_byte_size(v_s_1823_);
lean_inc(v_p_1824_);
v___x_1827_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_1823_, v___x_1825_, v_p_1824_, v___x_1826_);
if (lean_obj_tag(v___x_1827_) == 1)
{
lean_object* v_val_1828_; lean_object* v_fst_1829_; lean_object* v_snd_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1844_; 
v_val_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_val_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v_fst_1829_ = lean_ctor_get(v_val_1828_, 0);
v_snd_1830_ = lean_ctor_get(v_val_1828_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_val_1828_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1832_ = v_val_1828_;
v_isShared_1833_ = v_isSharedCheck_1844_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_snd_1830_);
lean_inc(v_fst_1829_);
lean_dec(v_val_1828_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1844_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v_p_x27_1835_; uint8_t v___x_1836_; 
v___x_1834_ = lean_string_utf8_byte_size(v_fst_1829_);
lean_dec(v_fst_1829_);
v_p_x27_1835_ = lean_nat_add(v_p_1824_, v___x_1834_);
v___x_1836_ = lean_string_is_valid_pos(v_s_1823_, v_p_x27_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec(v_p_x27_1835_);
lean_dec(v_snd_1830_);
v___x_1837_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0));
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 1);
lean_ctor_set(v___x_1832_, 1, v_p_1824_);
lean_ctor_set(v___x_1832_, 0, v___x_1837_);
v___x_1839_ = v___x_1832_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_p_1824_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
lean_object* v___x_1842_; 
lean_dec(v_p_1824_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_p_x27_1835_);
lean_ctor_set(v___x_1832_, 0, v_snd_1830_);
v___x_1842_ = v___x_1832_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_snd_1830_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_p_x27_1835_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v___x_1827_);
v___x_1845_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1));
v___x_1846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v_p_1824_);
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___boxed(lean_object* v_s_1847_, lean_object* v_p_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1847_, v_p_1848_);
lean_dec_ref(v_s_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f(lean_object* v_s_1850_){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1850_, v___x_1851_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v_a_1854_; lean_object* v___x_1855_; uint8_t v_decide_1856_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
v_a_1854_ = lean_ctor_get(v___x_1852_, 1);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1852_, 2);
v___x_1855_ = lean_string_utf8_byte_size(v_s_1850_);
v_decide_1856_ = lean_nat_dec_eq(v_a_1854_, v___x_1855_);
lean_dec(v_a_1854_);
if (v_decide_1856_ == 0)
{
lean_object* v___x_1857_; 
lean_dec(v_a_1853_);
v___x_1857_ = lean_box(0);
return v___x_1857_;
}
else
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_a_1853_);
return v___x_1858_;
}
}
else
{
lean_object* v___x_1859_; 
lean_dec_ref_known(v___x_1852_, 2);
v___x_1859_ = lean_box(0);
return v___x_1859_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f___boxed(lean_object* v_s_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lake_ComparatorOp_ofString_x3f(v_s_1860_);
lean_dec_ref(v_s_1860_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString(uint8_t v_self_1862_){
_start:
{
switch(v_self_1862_)
{
case 0:
{
lean_object* v___x_1863_; 
v___x_1863_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
return v___x_1863_;
}
case 1:
{
lean_object* v___x_1864_; 
v___x_1864_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
return v___x_1864_;
}
case 2:
{
lean_object* v___x_1865_; 
v___x_1865_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
return v___x_1865_;
}
case 3:
{
lean_object* v___x_1866_; 
v___x_1866_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
return v___x_1866_;
}
case 4:
{
lean_object* v___x_1867_; 
v___x_1867_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
return v___x_1867_;
}
default: 
{
lean_object* v___x_1868_; 
v___x_1868_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
return v___x_1868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString___boxed(lean_object* v_self_1869_){
_start:
{
uint8_t v_self_boxed_1870_; lean_object* v_res_1871_; 
v_self_boxed_1870_ = lean_unbox(v_self_1869_);
v_res_1871_ = l_Lake_ComparatorOp_toString(v_self_boxed_1870_);
return v_res_1871_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_unsigned_to_nat(7u);
v___x_1884_ = lean_nat_to_int(v___x_1883_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_unsigned_to_nat(6u);
v___x_1889_ = lean_nat_to_int(v___x_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_unsigned_to_nat(19u);
v___x_1894_ = lean_nat_to_int(v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___redArg(lean_object* v_x_1895_){
_start:
{
lean_object* v_ver_1896_; uint8_t v_op_1897_; uint8_t v_includeSuffixes_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_ver_1896_ = lean_ctor_get(v_x_1895_, 0);
lean_inc_ref(v_ver_1896_);
v_op_1897_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*1);
v_includeSuffixes_1898_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_1895_);
v___x_1899_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_1900_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__3));
v___x_1901_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__4, &l_Lake_instReprVerComparator_repr___redArg___closed__4_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__4);
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = l_Lake_instReprStdVer_repr___redArg(v_ver_1896_);
v___x_1904_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1901_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = 0;
v___x_1906_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*1, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1900_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_1909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_box(1);
v___x_1911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__6));
v___x_1913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v___x_1899_);
v___x_1915_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__7, &l_Lake_instReprVerComparator_repr___redArg___closed__7_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__7);
v___x_1916_ = l_Lake_instReprComparatorOp_repr(v_op_1897_, v___x_1902_);
v___x_1917_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set_uint8(v___x_1918_, sizeof(void*)*1, v___x_1905_);
v___x_1919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1914_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1908_);
v___x_1921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set(v___x_1921_, 1, v___x_1910_);
v___x_1922_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__9));
v___x_1923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v___x_1899_);
v___x_1925_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__10, &l_Lake_instReprVerComparator_repr___redArg___closed__10_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__10);
v___x_1926_ = l_Bool_repr___redArg(v_includeSuffixes_1898_);
v___x_1927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*1, v___x_1905_);
v___x_1929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1924_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_1931_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_1932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v___x_1929_);
v___x_1933_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_1934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1930_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set_uint8(v___x_1936_, sizeof(void*)*1, v___x_1905_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr(lean_object* v_x_1937_, lean_object* v_prec_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lake_instReprVerComparator_repr___redArg(v_x_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___boxed(lean_object* v_x_1940_, lean_object* v_prec_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lake_instReprVerComparator_repr(v_x_1940_, v_prec_1941_);
lean_dec(v_prec_1941_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(lean_object* v_s_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___x_1958_; 
lean_inc(v_a_1957_);
v___x_1958_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1956_, v_a_1957_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2025_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_a_1960_ = lean_ctor_get(v___x_1958_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_1962_ = v___x_1958_;
v_isShared_1963_ = v_isSharedCheck_2025_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2025_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; uint8_t v_decide_1965_; 
v___x_1964_ = lean_string_utf8_byte_size(v_s_1956_);
v_decide_1965_ = lean_nat_dec_eq(v_a_1960_, v___x_1964_);
if (v_decide_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_del_object(v___x_1962_);
lean_dec(v_a_1957_);
lean_inc_ref(v_s_1956_);
v___x_1966_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_1956_, v_a_1960_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v_a_1968_; lean_object* v___x_1969_; lean_object* v_a_1970_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
v_a_1968_ = lean_ctor_get(v___x_1966_, 1);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1966_, 2);
v___x_1969_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_1956_, v_a_1968_);
lean_dec_ref(v_s_1956_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
if (lean_obj_tag(v_a_1970_) == 1)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1992_; 
v_a_1971_ = lean_ctor_get(v___x_1969_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v___x_1969_, 0);
lean_dec(v_unused_1993_);
v___x_1973_ = v___x_1969_;
v_isShared_1974_ = v_isSharedCheck_1992_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1969_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1992_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_val_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_val_1975_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v_a_1970_, 1);
v___x_1976_ = lean_string_utf8_byte_size(v_val_1975_);
v___x_1977_ = lean_unsigned_to_nat(0u);
v___x_1978_ = lean_nat_dec_eq(v___x_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; lean_object* v___x_1983_; 
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v_a_1967_);
lean_ctor_set(v___x_1979_, 1, v_val_1975_);
v___x_1980_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
v___x_1981_ = lean_unbox(v_a_1959_);
lean_dec(v_a_1959_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*1, v___x_1981_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*1 + 1, v___x_1978_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1980_);
v___x_1983_ = v___x_1973_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_a_1971_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1990_; 
lean_dec(v_val_1975_);
v___x_1985_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_a_1967_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
v___x_1988_ = lean_unbox(v_a_1959_);
lean_dec(v_a_1959_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*1, v___x_1988_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*1 + 1, v___x_1978_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1987_);
v___x_1990_ = v___x_1973_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_a_1971_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2005_; 
lean_dec(v_a_1970_);
v_a_1994_ = lean_ctor_get(v___x_1969_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v___x_1969_, 0);
lean_dec(v_unused_2006_);
v___x_1996_ = v___x_1969_;
v_isShared_1997_ = v_isSharedCheck_2005_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1969_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2005_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; lean_object* v___x_2003_; 
v___x_1998_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_a_1967_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
v___x_2001_ = lean_unbox(v_a_1959_);
lean_dec(v_a_1959_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*1, v___x_2001_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*1 + 1, v_decide_1965_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2000_);
v___x_2003_ = v___x_1996_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_a_1994_);
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
lean_object* v_a_2007_; lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_a_1959_);
lean_dec_ref(v_s_1956_);
v_a_2007_ = lean_ctor_get(v___x_1966_, 0);
v_a_2008_ = lean_ctor_get(v___x_1966_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1966_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_inc(v_a_2007_);
lean_dec(v___x_1966_);
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
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2007_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_a_2008_);
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
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
lean_dec(v_a_1959_);
v___x_2016_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0));
v___x_2017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2017_, 0, v_s_1956_);
lean_ctor_set(v___x_2017_, 1, v_a_1957_);
lean_ctor_set(v___x_2017_, 2, v___x_1964_);
v___x_2018_ = l_String_Slice_toString(v___x_2017_);
lean_dec_ref_known(v___x_2017_, 3);
v___x_2019_ = lean_string_append(v___x_2016_, v___x_2018_);
lean_dec_ref(v___x_2018_);
v___x_2020_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1));
v___x_2021_ = lean_string_append(v___x_2019_, v___x_2020_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set_tag(v___x_1962_, 1);
lean_ctor_set(v___x_1962_, 0, v___x_2021_);
v___x_2023_ = v___x_1962_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_a_1960_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_a_1957_);
lean_dec_ref(v_s_1956_);
v_a_2026_ = lean_ctor_get(v___x_1958_, 0);
v_a_2027_ = lean_ctor_get(v___x_1958_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_1958_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_inc(v_a_2026_);
lean_dec(v___x_1958_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2026_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_parse(lean_object* v_s_2035_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = lean_string_utf8_byte_size(v_s_2035_);
lean_inc_ref(v_s_2035_);
v___x_2038_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_2035_, v___x_2036_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v_a_2040_; uint8_t v_decide_2041_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
v_a_2040_ = lean_ctor_get(v___x_2038_, 1);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2038_, 2);
v_decide_2041_ = lean_nat_dec_eq(v_a_2040_, v___x_2037_);
if (v_decide_2041_ == 0)
{
lean_object* v_tail_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v_a_2039_);
v_tail_2042_ = lean_string_utf8_extract(v_s_2035_, v_a_2040_, v___x_2037_);
lean_dec(v_a_2040_);
lean_dec_ref(v_s_2035_);
v___x_2043_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_2044_ = lean_string_append(v___x_2043_, v_tail_2042_);
lean_dec_ref(v_tail_2042_);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; 
lean_dec(v_a_2040_);
lean_dec_ref(v_s_2035_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_a_2039_);
return v___x_2046_;
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2048_; 
lean_dec_ref(v_s_2035_);
v_a_2047_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2038_, 2);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_a_2047_);
return v___x_2048_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_VerComparator_test(lean_object* v_self_2049_, lean_object* v_ver_2050_){
_start:
{
uint8_t v___y_2052_; uint8_t v___y_2053_; lean_object* v___y_2054_; uint8_t v___y_2055_; uint8_t v___y_2056_; lean_object* v___y_2057_; uint8_t v___y_2058_; uint8_t v___y_2063_; lean_object* v___y_2064_; uint8_t v___y_2065_; uint8_t v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; uint8_t v___y_2073_; lean_object* v___y_2074_; uint8_t v___y_2075_; lean_object* v___y_2076_; uint8_t v___y_2077_; lean_object* v___y_2082_; uint8_t v___y_2083_; lean_object* v___y_2084_; uint8_t v___y_2085_; lean_object* v_ver_2089_; uint8_t v_op_2090_; uint8_t v_includeSuffixes_2091_; lean_object* v_ver_2093_; 
v_ver_2089_ = lean_ctor_get(v_self_2049_, 0);
v_op_2090_ = lean_ctor_get_uint8(v_self_2049_, sizeof(void*)*1);
v_includeSuffixes_2091_ = lean_ctor_get_uint8(v_self_2049_, sizeof(void*)*1 + 1);
if (v_includeSuffixes_2091_ == 0)
{
lean_object* v_toSemVerCore_2097_; lean_object* v_specialDescr_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_toSemVerCore_2097_ = lean_ctor_get(v_ver_2050_, 0);
v_specialDescr_2098_ = lean_ctor_get(v_ver_2050_, 1);
v___x_2099_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_2100_ = lean_string_dec_eq(v_specialDescr_2098_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v_toSemVerCore_2101_; lean_object* v_specialDescr_2102_; uint8_t v___x_2103_; 
v_toSemVerCore_2101_ = lean_ctor_get(v_ver_2089_, 0);
v_specialDescr_2102_ = lean_ctor_get(v_ver_2089_, 1);
v___x_2103_ = lean_string_dec_eq(v_specialDescr_2102_, v___x_2099_);
if (v___x_2103_ == 0)
{
uint8_t v___x_2104_; 
v___x_2104_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_2101_, v_toSemVerCore_2097_);
if (v___x_2104_ == 0)
{
return v___x_2104_;
}
else
{
uint8_t v___x_2105_; 
v___x_2105_ = lean_string_dec_eq(v_specialDescr_2098_, v_specialDescr_2102_);
switch(v_op_2090_)
{
case 0:
{
uint8_t v___x_2106_; 
v___x_2106_ = lean_string_dec_lt(v_specialDescr_2098_, v_specialDescr_2102_);
return v___x_2106_;
}
case 1:
{
uint8_t v___x_2107_; 
v___x_2107_ = l_String_decLE(v_specialDescr_2098_, v_specialDescr_2102_);
return v___x_2107_;
}
case 2:
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_string_dec_lt(v_specialDescr_2102_, v_specialDescr_2098_);
return v___x_2108_;
}
case 3:
{
uint8_t v___x_2109_; 
v___x_2109_ = l_String_decLE(v_specialDescr_2102_, v_specialDescr_2098_);
return v___x_2109_;
}
case 4:
{
return v___x_2105_;
}
default: 
{
if (v___x_2105_ == 0)
{
return v___x_2104_;
}
else
{
return v___x_2103_;
}
}
}
}
}
else
{
return v_includeSuffixes_2091_;
}
}
else
{
v_ver_2093_ = v_ver_2050_;
goto v___jp_2092_;
}
}
else
{
v_ver_2093_ = v_ver_2050_;
goto v___jp_2092_;
}
v___jp_2051_:
{
uint8_t v___x_2059_; 
v___x_2059_ = l_Lake_instDecidableEqStdVer_decEq(v___y_2057_, v___y_2054_);
switch(v___y_2056_)
{
case 0:
{
return v___y_2053_;
}
case 1:
{
return v___y_2055_;
}
case 2:
{
return v___y_2052_;
}
case 3:
{
return v___y_2058_;
}
case 4:
{
return v___x_2059_;
}
default: 
{
if (v___x_2059_ == 0)
{
uint8_t v___x_2060_; 
v___x_2060_ = 1;
return v___x_2060_;
}
else
{
uint8_t v___x_2061_; 
v___x_2061_ = 0;
return v___x_2061_;
}
}
}
}
v___jp_2062_:
{
uint8_t v___x_2069_; 
v___x_2069_ = l_Lake_StdVer_compare(v___y_2064_, v___y_2067_);
if (v___x_2069_ == 2)
{
uint8_t v___x_2070_; 
v___x_2070_ = 0;
v___y_2052_ = v___y_2068_;
v___y_2053_ = v___y_2063_;
v___y_2054_ = v___y_2064_;
v___y_2055_ = v___y_2065_;
v___y_2056_ = v___y_2066_;
v___y_2057_ = v___y_2067_;
v___y_2058_ = v___x_2070_;
goto v___jp_2051_;
}
else
{
uint8_t v___x_2071_; 
v___x_2071_ = 1;
v___y_2052_ = v___y_2068_;
v___y_2053_ = v___y_2063_;
v___y_2054_ = v___y_2064_;
v___y_2055_ = v___y_2065_;
v___y_2056_ = v___y_2066_;
v___y_2057_ = v___y_2067_;
v___y_2058_ = v___x_2071_;
goto v___jp_2051_;
}
}
v___jp_2072_:
{
uint8_t v___x_2078_; 
v___x_2078_ = l_Lake_StdVer_compare(v___y_2074_, v___y_2076_);
if (v___x_2078_ == 0)
{
uint8_t v___x_2079_; 
v___x_2079_ = 1;
v___y_2063_ = v___y_2073_;
v___y_2064_ = v___y_2074_;
v___y_2065_ = v___y_2077_;
v___y_2066_ = v___y_2075_;
v___y_2067_ = v___y_2076_;
v___y_2068_ = v___x_2079_;
goto v___jp_2062_;
}
else
{
uint8_t v___x_2080_; 
v___x_2080_ = 0;
v___y_2063_ = v___y_2073_;
v___y_2064_ = v___y_2074_;
v___y_2065_ = v___y_2077_;
v___y_2066_ = v___y_2075_;
v___y_2067_ = v___y_2076_;
v___y_2068_ = v___x_2080_;
goto v___jp_2062_;
}
}
v___jp_2081_:
{
uint8_t v___x_2086_; 
v___x_2086_ = l_Lake_StdVer_compare(v___y_2084_, v___y_2082_);
if (v___x_2086_ == 2)
{
uint8_t v___x_2087_; 
v___x_2087_ = 0;
v___y_2073_ = v___y_2085_;
v___y_2074_ = v___y_2082_;
v___y_2075_ = v___y_2083_;
v___y_2076_ = v___y_2084_;
v___y_2077_ = v___x_2087_;
goto v___jp_2072_;
}
else
{
uint8_t v___x_2088_; 
v___x_2088_ = 1;
v___y_2073_ = v___y_2085_;
v___y_2074_ = v___y_2082_;
v___y_2075_ = v___y_2083_;
v___y_2076_ = v___y_2084_;
v___y_2077_ = v___x_2088_;
goto v___jp_2072_;
}
}
v___jp_2092_:
{
uint8_t v___x_2094_; 
v___x_2094_ = l_Lake_StdVer_compare(v_ver_2093_, v_ver_2089_);
if (v___x_2094_ == 0)
{
uint8_t v___x_2095_; 
v___x_2095_ = 1;
v___y_2082_ = v_ver_2089_;
v___y_2083_ = v_op_2090_;
v___y_2084_ = v_ver_2093_;
v___y_2085_ = v___x_2095_;
goto v___jp_2081_;
}
else
{
uint8_t v___x_2096_; 
v___x_2096_ = 0;
v___y_2082_ = v_ver_2089_;
v___y_2083_ = v_op_2090_;
v___y_2084_ = v_ver_2093_;
v___y_2085_ = v___x_2096_;
goto v___jp_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_test___boxed(lean_object* v_self_2110_, lean_object* v_ver_2111_){
_start:
{
uint8_t v_res_2112_; lean_object* v_r_2113_; 
v_res_2112_ = l_Lake_VerComparator_test(v_self_2110_, v_ver_2111_);
lean_dec_ref(v_ver_2111_);
lean_dec_ref(v_self_2110_);
v_r_2113_ = lean_box(v_res_2112_);
return v_r_2113_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_toString(lean_object* v_self_2114_){
_start:
{
lean_object* v_ver_2115_; uint8_t v_op_2116_; uint8_t v_includeSuffixes_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_ver_2115_ = lean_ctor_get(v_self_2114_, 0);
lean_inc_ref(v_ver_2115_);
v_op_2116_ = lean_ctor_get_uint8(v_self_2114_, sizeof(void*)*1);
v_includeSuffixes_2117_ = lean_ctor_get_uint8(v_self_2114_, sizeof(void*)*1 + 1);
lean_dec_ref(v_self_2114_);
v___x_2118_ = l_Lake_ComparatorOp_toString(v_op_2116_);
v___x_2119_ = l_Lake_StdVer_toString(v_ver_2115_);
v___x_2120_ = lean_string_append(v___x_2118_, v___x_2119_);
lean_dec_ref(v___x_2119_);
if (v_includeSuffixes_2117_ == 0)
{
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_2122_ = lean_string_append(v___x_2120_, v___x_2121_);
return v___x_2122_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_2125_, lean_object* v_x_2126_, lean_object* v_x_2127_){
_start:
{
if (lean_obj_tag(v_x_2127_) == 0)
{
lean_dec(v_x_2125_);
return v_x_2126_;
}
else
{
lean_object* v_head_2128_; lean_object* v_tail_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2139_; 
v_head_2128_ = lean_ctor_get(v_x_2127_, 0);
v_tail_2129_ = lean_ctor_get(v_x_2127_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_x_2127_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2131_ = v_x_2127_;
v_isShared_2132_ = v_isSharedCheck_2139_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_tail_2129_);
lean_inc(v_head_2128_);
lean_dec(v_x_2127_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2139_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
lean_inc(v_x_2125_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 5);
lean_ctor_set(v___x_2131_, 1, v_x_2125_);
lean_ctor_set(v___x_2131_, 0, v_x_2126_);
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_x_2126_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_x_2125_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2128_);
v___x_2136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v_x_2126_ = v___x_2136_;
v_x_2127_ = v_tail_2129_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2140_, lean_object* v_x_2141_, lean_object* v_x_2142_){
_start:
{
if (lean_obj_tag(v_x_2142_) == 0)
{
lean_dec(v_x_2140_);
return v_x_2141_;
}
else
{
lean_object* v_head_2143_; lean_object* v_tail_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2154_; 
v_head_2143_ = lean_ctor_get(v_x_2142_, 0);
v_tail_2144_ = lean_ctor_get(v_x_2142_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_x_2142_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2146_ = v_x_2142_;
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_tail_2144_);
lean_inc(v_head_2143_);
lean_dec(v_x_2142_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
lean_inc(v_x_2140_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 5);
lean_ctor_set(v___x_2146_, 1, v_x_2140_);
lean_ctor_set(v___x_2146_, 0, v_x_2141_);
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_x_2141_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_x_2140_);
v___x_2149_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2143_);
v___x_2151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_2140_, v___x_2151_, v_tail_2144_);
return v___x_2152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
if (lean_obj_tag(v_x_2155_) == 0)
{
lean_object* v___x_2157_; 
lean_dec(v_x_2156_);
v___x_2157_ = lean_box(0);
return v___x_2157_;
}
else
{
lean_object* v_tail_2158_; 
v_tail_2158_ = lean_ctor_get(v_x_2155_, 1);
if (lean_obj_tag(v_tail_2158_) == 0)
{
lean_object* v_head_2159_; lean_object* v___x_2160_; 
lean_dec(v_x_2156_);
v_head_2159_ = lean_ctor_get(v_x_2155_, 0);
lean_inc(v_head_2159_);
lean_dec_ref_known(v_x_2155_, 2);
v___x_2160_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2159_);
return v___x_2160_;
}
else
{
lean_object* v_head_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_inc(v_tail_2158_);
v_head_2161_ = lean_ctor_get(v_x_2155_, 0);
lean_inc(v_head_2161_);
lean_dec_ref_known(v_x_2155_, 2);
v___x_2162_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2161_);
v___x_2163_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(v_x_2156_, v___x_2162_, v_tail_2158_);
return v___x_2163_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0));
v___x_2170_ = lean_string_length(v___x_2169_);
return v___x_2170_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3);
v___x_2172_ = lean_nat_to_int(v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(lean_object* v_xs_2180_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = lean_array_get_size(v_xs_2180_);
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = lean_nat_dec_eq(v___x_2181_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2184_ = lean_array_to_list(v_xs_2180_);
v___x_2185_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2186_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(v___x_2184_, v___x_2185_);
v___x_2187_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2188_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v___x_2186_);
v___x_2190_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2187_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = l_Std_Format_fill(v___x_2192_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; 
lean_dec_ref(v_xs_2180_);
v___x_2194_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(lean_object* v_x_2195_, lean_object* v_x_2196_, lean_object* v_x_2197_){
_start:
{
if (lean_obj_tag(v_x_2197_) == 0)
{
lean_dec(v_x_2195_);
return v_x_2196_;
}
else
{
lean_object* v_head_2198_; lean_object* v_tail_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2209_; 
v_head_2198_ = lean_ctor_get(v_x_2197_, 0);
v_tail_2199_ = lean_ctor_get(v_x_2197_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_x_2197_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2201_ = v_x_2197_;
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_tail_2199_);
lean_inc(v_head_2198_);
lean_dec(v_x_2197_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
lean_inc(v_x_2195_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set_tag(v___x_2201_, 5);
lean_ctor_set(v___x_2201_, 1, v_x_2195_);
lean_ctor_set(v___x_2201_, 0, v_x_2196_);
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_x_2196_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_x_2195_);
v___x_2204_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2198_);
v___x_2206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v_x_2196_ = v___x_2206_;
v_x_2197_ = v_tail_2199_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
if (lean_obj_tag(v_x_2210_) == 0)
{
lean_object* v___x_2212_; 
lean_dec(v_x_2211_);
v___x_2212_ = lean_box(0);
return v___x_2212_;
}
else
{
lean_object* v_tail_2213_; 
v_tail_2213_ = lean_ctor_get(v_x_2210_, 1);
if (lean_obj_tag(v_tail_2213_) == 0)
{
lean_object* v_head_2214_; lean_object* v___x_2215_; 
lean_dec(v_x_2211_);
v_head_2214_ = lean_ctor_get(v_x_2210_, 0);
lean_inc(v_head_2214_);
lean_dec_ref_known(v_x_2210_, 2);
v___x_2215_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2214_);
return v___x_2215_;
}
else
{
lean_object* v_head_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_inc(v_tail_2213_);
v_head_2216_ = lean_ctor_get(v_x_2210_, 0);
lean_inc(v_head_2216_);
lean_dec_ref_known(v_x_2210_, 2);
v___x_2217_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2216_);
v___x_2218_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(v_x_2211_, v___x_2217_, v_tail_2213_);
return v___x_2218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(lean_object* v_xs_2219_){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = lean_array_get_size(v_xs_2219_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_nat_dec_eq(v___x_2220_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2223_ = lean_array_to_list(v_xs_2219_);
v___x_2224_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2225_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(v___x_2223_, v___x_2224_);
v___x_2226_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2227_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v___x_2225_);
v___x_2229_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2226_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = l_Std_Format_fill(v___x_2231_);
return v___x_2232_;
}
else
{
lean_object* v___x_2233_; 
lean_dec_ref(v_xs_2219_);
v___x_2233_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2233_;
}
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_unsigned_to_nat(12u);
v___x_2244_ = lean_nat_to_int(v___x_2243_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_unsigned_to_nat(11u);
v___x_2249_ = lean_nat_to_int(v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object* v_x_2250_){
_start:
{
lean_object* v_toString_2251_; lean_object* v_clauses_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2286_; 
v_toString_2251_ = lean_ctor_get(v_x_2250_, 0);
v_clauses_2252_ = lean_ctor_get(v_x_2250_, 1);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_x_2250_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2254_ = v_x_2250_;
v_isShared_2255_ = v_isSharedCheck_2286_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_clauses_2252_);
lean_inc(v_toString_2251_);
lean_dec(v_x_2250_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2286_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2256_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_2257_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__3));
v___x_2258_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__4, &l_Lake_instReprVerRange_repr___redArg___closed__4_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__4);
v___x_2259_ = l_String_quote(v_toString_2251_);
v___x_2260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set_tag(v___x_2254_, 4);
lean_ctor_set(v___x_2254_, 1, v___x_2260_);
lean_ctor_set(v___x_2254_, 0, v___x_2258_);
v___x_2262_ = v___x_2254_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2263_ = 0;
v___x_2264_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*1, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2257_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_2267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = lean_box(1);
v___x_2269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__6));
v___x_2271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
lean_ctor_set(v___x_2272_, 1, v___x_2256_);
v___x_2273_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__7, &l_Lake_instReprVerRange_repr___redArg___closed__7_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__7);
v___x_2274_ = l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(v_clauses_2252_);
v___x_2275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
lean_ctor_set_uint8(v___x_2276_, sizeof(void*)*1, v___x_2263_);
v___x_2277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2272_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_2279_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_2280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v___x_2277_);
v___x_2281_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_2282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2278_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set_uint8(v___x_2284_, sizeof(void*)*1, v___x_2263_);
return v___x_2284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr(lean_object* v_x_2287_, lean_object* v_prec_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lake_instReprVerRange_repr___redArg(v_x_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___boxed(lean_object* v_x_2290_, lean_object* v_prec_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lake_instReprVerRange_repr(v_x_2290_, v_prec_2291_);
lean_dec(v_prec_2291_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0(lean_object* v_self_2302_){
_start:
{
lean_object* v_toString_2303_; 
v_toString_2303_ = lean_ctor_get(v_self_2302_, 0);
lean_inc_ref(v_toString_2303_);
return v_toString_2303_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0___boxed(lean_object* v_self_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lake_VerRange_instToString___lam__0(v_self_2304_);
lean_dec_ref(v_self_2304_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(lean_object* v_as_2309_, size_t v_i_2310_, size_t v_stop_2311_, lean_object* v_b_2312_){
_start:
{
uint8_t v___x_2313_; 
v___x_2313_ = lean_usize_dec_eq(v_i_2310_, v_stop_2311_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; 
v___x_2314_ = lean_array_uget_borrowed(v_as_2309_, v_i_2310_);
v___x_2315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0));
v___x_2316_ = lean_string_append(v_b_2312_, v___x_2315_);
lean_inc(v___x_2314_);
v___x_2317_ = l_Lake_VerComparator_toString(v___x_2314_);
v___x_2318_ = lean_string_append(v___x_2316_, v___x_2317_);
lean_dec_ref(v___x_2317_);
v___x_2319_ = ((size_t)1ULL);
v___x_2320_ = lean_usize_add(v_i_2310_, v___x_2319_);
v_i_2310_ = v___x_2320_;
v_b_2312_ = v___x_2318_;
goto _start;
}
else
{
return v_b_2312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___boxed(lean_object* v_as_2322_, lean_object* v_i_2323_, lean_object* v_stop_2324_, lean_object* v_b_2325_){
_start:
{
size_t v_i_boxed_2326_; size_t v_stop_boxed_2327_; lean_object* v_res_2328_; 
v_i_boxed_2326_ = lean_unbox_usize(v_i_2323_);
lean_dec(v_i_2323_);
v_stop_boxed_2327_ = lean_unbox_usize(v_stop_2324_);
lean_dec(v_stop_2324_);
v_res_2328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_as_2322_, v_i_boxed_2326_, v_stop_boxed_2327_, v_b_2325_);
lean_dec_ref(v_as_2322_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(lean_object* v_ands_2330_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2331_ = lean_array_get_size(v_ands_2330_);
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = lean_nat_dec_eq(v___x_2331_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2334_ = lean_array_fget_borrowed(v_ands_2330_, v___x_2332_);
lean_inc(v___x_2334_);
v___x_2335_ = l_Lake_VerComparator_toString(v___x_2334_);
v___x_2336_ = lean_unsigned_to_nat(1u);
v___x_2337_ = lean_nat_dec_lt(v___x_2336_, v___x_2331_);
if (v___x_2337_ == 0)
{
return v___x_2335_;
}
else
{
uint8_t v___x_2338_; 
v___x_2338_ = lean_nat_dec_le(v___x_2331_, v___x_2331_);
if (v___x_2338_ == 0)
{
if (v___x_2337_ == 0)
{
return v___x_2335_;
}
else
{
size_t v___x_2339_; size_t v___x_2340_; lean_object* v___x_2341_; 
v___x_2339_ = ((size_t)1ULL);
v___x_2340_ = lean_usize_of_nat(v___x_2331_);
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2330_, v___x_2339_, v___x_2340_, v___x_2335_);
return v___x_2341_;
}
}
else
{
size_t v___x_2342_; size_t v___x_2343_; lean_object* v___x_2344_; 
v___x_2342_ = ((size_t)1ULL);
v___x_2343_ = lean_usize_of_nat(v___x_2331_);
v___x_2344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2330_, v___x_2342_, v___x_2343_, v___x_2335_);
return v___x_2344_;
}
}
}
else
{
lean_object* v___x_2345_; 
v___x_2345_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0));
return v___x_2345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___boxed(lean_object* v_ands_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v_ands_2346_);
lean_dec_ref(v_ands_2346_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(lean_object* v_as_2349_, size_t v_i_2350_, size_t v_stop_2351_, lean_object* v_b_2352_){
_start:
{
uint8_t v___x_2353_; 
v___x_2353_ = lean_usize_dec_eq(v_i_2350_, v_stop_2351_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; size_t v___x_2359_; size_t v___x_2360_; 
v___x_2354_ = lean_array_uget_borrowed(v_as_2349_, v_i_2350_);
v___x_2355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0));
v___x_2356_ = lean_string_append(v_b_2352_, v___x_2355_);
v___x_2357_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2354_);
v___x_2358_ = lean_string_append(v___x_2356_, v___x_2357_);
lean_dec_ref(v___x_2357_);
v___x_2359_ = ((size_t)1ULL);
v___x_2360_ = lean_usize_add(v_i_2350_, v___x_2359_);
v_i_2350_ = v___x_2360_;
v_b_2352_ = v___x_2358_;
goto _start;
}
else
{
return v_b_2352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___boxed(lean_object* v_as_2362_, lean_object* v_i_2363_, lean_object* v_stop_2364_, lean_object* v_b_2365_){
_start:
{
size_t v_i_boxed_2366_; size_t v_stop_boxed_2367_; lean_object* v_res_2368_; 
v_i_boxed_2366_ = lean_unbox_usize(v_i_2363_);
lean_dec(v_i_2363_);
v_stop_boxed_2367_ = lean_unbox_usize(v_stop_2364_);
lean_dec(v_stop_2364_);
v_res_2368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_as_2362_, v_i_boxed_2366_, v_stop_boxed_2367_, v_b_2365_);
lean_dec_ref(v_as_2362_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(lean_object* v_ors_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2370_ = lean_array_get_size(v_ors_2369_);
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = lean_nat_dec_eq(v___x_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2373_ = lean_array_fget_borrowed(v_ors_2369_, v___x_2371_);
v___x_2374_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2373_);
v___x_2375_ = lean_unsigned_to_nat(1u);
v___x_2376_ = lean_nat_dec_lt(v___x_2375_, v___x_2370_);
if (v___x_2376_ == 0)
{
return v___x_2374_;
}
else
{
uint8_t v___x_2377_; 
v___x_2377_ = lean_nat_dec_le(v___x_2370_, v___x_2370_);
if (v___x_2377_ == 0)
{
if (v___x_2376_ == 0)
{
return v___x_2374_;
}
else
{
size_t v___x_2378_; size_t v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = ((size_t)1ULL);
v___x_2379_ = lean_usize_of_nat(v___x_2370_);
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2369_, v___x_2378_, v___x_2379_, v___x_2374_);
return v___x_2380_;
}
}
else
{
size_t v___x_2381_; size_t v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = ((size_t)1ULL);
v___x_2382_ = lean_usize_of_nat(v___x_2370_);
v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2369_, v___x_2381_, v___x_2382_, v___x_2374_);
return v___x_2383_;
}
}
}
else
{
lean_object* v___x_2384_; 
v___x_2384_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
return v___x_2384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs___boxed(lean_object* v_ors_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_ors_2385_);
lean_dec_ref(v_ors_2385_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_ofClauses(lean_object* v_clauses_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_clauses_2387_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v_clauses_2387_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_appendRange(lean_object* v_ands_2390_, lean_object* v_minVer_2391_, lean_object* v_maxVer_2392_, lean_object* v_specialDescr_2393_){
_start:
{
lean_object* v_minVer_2394_; lean_object* v___x_2395_; lean_object* v_maxVer_2396_; uint8_t v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_minVer_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2394_, 0, v_minVer_2391_);
lean_ctor_set(v_minVer_2394_, 1, v_specialDescr_2393_);
v___x_2395_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2396_, 0, v_maxVer_2392_);
lean_ctor_set(v_maxVer_2396_, 1, v___x_2395_);
v___x_2397_ = 3;
v___x_2398_ = 0;
v___x_2399_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2399_, 0, v_minVer_2394_);
lean_ctor_set_uint8(v___x_2399_, sizeof(void*)*1, v___x_2397_);
lean_ctor_set_uint8(v___x_2399_, sizeof(void*)*1 + 1, v___x_2398_);
v___x_2400_ = lean_array_push(v_ands_2390_, v___x_2399_);
v___x_2401_ = 0;
v___x_2402_ = 1;
v___x_2403_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2403_, 0, v_maxVer_2396_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*1, v___x_2401_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*1 + 1, v___x_2402_);
v___x_2404_ = lean_array_push(v___x_2400_, v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(lean_object* v_s_2407_, lean_object* v_ands_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v_a_2413_; lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2585_; 
v___x_2410_ = lean_unsigned_to_nat(0u);
v___x_2411_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2409_);
lean_inc_ref(v_s_2407_);
v___x_2412_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2407_, v___x_2411_, v_a_2409_, v_a_2409_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_a_2414_ = lean_ctor_get(v___x_2412_, 1);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2416_ = v___x_2412_;
v_isShared_2417_ = v_isSharedCheck_2585_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2585_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; 
v___x_2418_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2407_, v_a_2414_);
lean_dec_ref(v_s_2407_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2575_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_a_2420_ = lean_ctor_get(v___x_2418_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2422_ = v___x_2418_;
v_isShared_2423_ = v_isSharedCheck_2575_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2575_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2424_ = lean_array_get_size(v_a_2413_);
v___x_2425_ = lean_unsigned_to_nat(1u);
v___x_2426_ = lean_nat_dec_eq(v___x_2424_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2427_ = lean_unsigned_to_nat(2u);
v___x_2428_ = lean_nat_dec_eq(v___x_2424_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = lean_unsigned_to_nat(3u);
v___x_2430_ = lean_nat_dec_eq(v___x_2424_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_dec(v_a_2419_);
lean_del_object(v___x_2416_);
lean_dec(v_a_2413_);
lean_dec_ref(v_ands_2408_);
v___x_2431_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0));
v___x_2432_ = l_Nat_reprFast(v___x_2424_);
v___x_2433_ = lean_string_append(v___x_2431_, v___x_2432_);
lean_dec_ref(v___x_2432_);
v___x_2434_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2435_ = lean_string_append(v___x_2433_, v___x_2434_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2435_);
v___x_2437_ = v___x_2422_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_a_2420_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_array_fget_borrowed(v_a_2413_, v___x_2410_);
v___x_2440_ = l_String_Slice_toNat_x3f(v___x_2439_);
if (lean_obj_tag(v___x_2440_) == 1)
{
lean_object* v_val_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_val_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_val_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2442_ = lean_array_fget_borrowed(v_a_2413_, v___x_2425_);
v___x_2443_ = l_String_Slice_toNat_x3f(v___x_2442_);
if (lean_obj_tag(v___x_2443_) == 1)
{
lean_object* v_val_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_val_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_val_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = lean_array_fget(v_a_2413_, v___x_2427_);
lean_dec(v_a_2413_);
v___x_2446_ = l_String_Slice_toNat_x3f(v___x_2445_);
if (lean_obj_tag(v___x_2446_) == 1)
{
lean_object* v_val_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v_minVer_2452_; 
lean_dec(v___x_2445_);
v_val_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_val_2447_);
lean_dec_ref_known(v___x_2446_, 1);
lean_inc(v_val_2444_);
lean_inc(v_val_2441_);
v___x_2448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2448_, 0, v_val_2441_);
lean_ctor_set(v___x_2448_, 1, v_val_2444_);
lean_ctor_set(v___x_2448_, 2, v_val_2447_);
v___x_2449_ = lean_nat_add(v_val_2444_, v___x_2425_);
lean_dec(v_val_2444_);
v___x_2450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2450_, 0, v_val_2441_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
lean_ctor_set(v___x_2450_, 2, v___x_2410_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v_a_2419_);
lean_ctor_set(v___x_2416_, 0, v___x_2448_);
v_minVer_2452_ = v___x_2416_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_a_2419_);
v_minVer_2452_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v_maxVer_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2453_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2454_, 0, v___x_2450_);
lean_ctor_set(v_maxVer_2454_, 1, v___x_2453_);
v___x_2455_ = 3;
v___x_2456_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2456_, 0, v_minVer_2452_);
lean_ctor_set_uint8(v___x_2456_, sizeof(void*)*1, v___x_2455_);
lean_ctor_set_uint8(v___x_2456_, sizeof(void*)*1 + 1, v___x_2428_);
v___x_2457_ = lean_array_push(v_ands_2408_, v___x_2456_);
v___x_2458_ = 0;
v___x_2459_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2459_, 0, v_maxVer_2454_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*1, v___x_2458_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*1 + 1, v___x_2430_);
v___x_2460_ = lean_array_push(v___x_2457_, v___x_2459_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2460_);
v___x_2462_ = v___x_2422_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_a_2420_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
else
{
lean_object* v_str_2465_; lean_object* v_startInclusive_2466_; lean_object* v_endExclusive_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v___x_2446_);
lean_dec(v_val_2444_);
lean_dec(v_val_2441_);
lean_dec(v_a_2419_);
lean_del_object(v___x_2416_);
lean_dec_ref(v_ands_2408_);
v_str_2465_ = lean_ctor_get(v___x_2445_, 0);
lean_inc_ref(v_str_2465_);
v_startInclusive_2466_ = lean_ctor_get(v___x_2445_, 1);
lean_inc(v_startInclusive_2466_);
v_endExclusive_2467_ = lean_ctor_get(v___x_2445_, 2);
lean_inc(v_endExclusive_2467_);
lean_dec(v___x_2445_);
v___x_2468_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2469_ = lean_string_utf8_extract_fast(v_str_2465_, v_startInclusive_2466_, v_endExclusive_2467_);
lean_dec(v_endExclusive_2467_);
lean_dec(v_startInclusive_2466_);
lean_dec_ref(v_str_2465_);
v___x_2470_ = lean_string_append(v___x_2468_, v___x_2469_);
lean_dec_ref(v___x_2469_);
v___x_2471_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2472_ = lean_string_append(v___x_2470_, v___x_2471_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2472_);
v___x_2474_ = v___x_2422_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_a_2420_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
else
{
lean_object* v_str_2476_; lean_object* v_startInclusive_2477_; lean_object* v_endExclusive_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
lean_inc(v___x_2442_);
lean_dec(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_a_2419_);
lean_del_object(v___x_2416_);
lean_dec(v_a_2413_);
lean_dec_ref(v_ands_2408_);
v_str_2476_ = lean_ctor_get(v___x_2442_, 0);
lean_inc_ref(v_str_2476_);
v_startInclusive_2477_ = lean_ctor_get(v___x_2442_, 1);
lean_inc(v_startInclusive_2477_);
v_endExclusive_2478_ = lean_ctor_get(v___x_2442_, 2);
lean_inc(v_endExclusive_2478_);
lean_dec(v___x_2442_);
v___x_2479_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2480_ = lean_string_utf8_extract_fast(v_str_2476_, v_startInclusive_2477_, v_endExclusive_2478_);
lean_dec(v_endExclusive_2478_);
lean_dec(v_startInclusive_2477_);
lean_dec_ref(v_str_2476_);
v___x_2481_ = lean_string_append(v___x_2479_, v___x_2480_);
lean_dec_ref(v___x_2480_);
v___x_2482_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2483_ = lean_string_append(v___x_2481_, v___x_2482_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2483_);
v___x_2485_ = v___x_2422_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_a_2420_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
else
{
lean_object* v_str_2487_; lean_object* v_startInclusive_2488_; lean_object* v_endExclusive_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
lean_inc(v___x_2439_);
lean_dec(v___x_2440_);
lean_dec(v_a_2419_);
lean_del_object(v___x_2416_);
lean_dec(v_a_2413_);
lean_dec_ref(v_ands_2408_);
v_str_2487_ = lean_ctor_get(v___x_2439_, 0);
lean_inc_ref(v_str_2487_);
v_startInclusive_2488_ = lean_ctor_get(v___x_2439_, 1);
lean_inc(v_startInclusive_2488_);
v_endExclusive_2489_ = lean_ctor_get(v___x_2439_, 2);
lean_inc(v_endExclusive_2489_);
lean_dec(v___x_2439_);
v___x_2490_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2491_ = lean_string_utf8_extract_fast(v_str_2487_, v_startInclusive_2488_, v_endExclusive_2489_);
lean_dec(v_endExclusive_2489_);
lean_dec(v_startInclusive_2488_);
lean_dec_ref(v_str_2487_);
v___x_2492_ = lean_string_append(v___x_2490_, v___x_2491_);
lean_dec_ref(v___x_2491_);
v___x_2493_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2494_ = lean_string_append(v___x_2492_, v___x_2493_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2494_);
v___x_2496_ = v___x_2422_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_a_2420_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
else
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_array_fget_borrowed(v_a_2413_, v___x_2410_);
v___x_2499_ = l_String_Slice_toNat_x3f(v___x_2498_);
if (lean_obj_tag(v___x_2499_) == 1)
{
lean_object* v_val_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v_val_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_val_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2501_ = lean_array_fget(v_a_2413_, v___x_2425_);
lean_dec(v_a_2413_);
v___x_2502_ = l_String_Slice_toNat_x3f(v___x_2501_);
if (lean_obj_tag(v___x_2502_) == 1)
{
lean_object* v_val_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v_minVer_2508_; 
lean_dec(v___x_2501_);
v_val_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc_n(v_val_2503_, 2);
lean_dec_ref_known(v___x_2502_, 1);
lean_inc(v_val_2500_);
v___x_2504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2504_, 0, v_val_2500_);
lean_ctor_set(v___x_2504_, 1, v_val_2503_);
lean_ctor_set(v___x_2504_, 2, v___x_2410_);
v___x_2505_ = lean_nat_add(v_val_2503_, v___x_2425_);
lean_dec(v_val_2503_);
v___x_2506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2506_, 0, v_val_2500_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
lean_ctor_set(v___x_2506_, 2, v___x_2410_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v_a_2419_);
lean_ctor_set(v___x_2416_, 0, v___x_2504_);
v_minVer_2508_ = v___x_2416_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_a_2419_);
v_minVer_2508_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; lean_object* v_maxVer_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2509_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2510_, 0, v___x_2506_);
lean_ctor_set(v_maxVer_2510_, 1, v___x_2509_);
v___x_2511_ = 3;
v___x_2512_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2512_, 0, v_minVer_2508_);
lean_ctor_set_uint8(v___x_2512_, sizeof(void*)*1, v___x_2511_);
lean_ctor_set_uint8(v___x_2512_, sizeof(void*)*1 + 1, v___x_2426_);
v___x_2513_ = lean_array_push(v_ands_2408_, v___x_2512_);
v___x_2514_ = 0;
v___x_2515_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2515_, 0, v_maxVer_2510_);
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*1, v___x_2514_);
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*1 + 1, v___x_2428_);
v___x_2516_ = lean_array_push(v___x_2513_, v___x_2515_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2516_);
v___x_2518_ = v___x_2422_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_a_2420_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
else
{
lean_object* v_str_2521_; lean_object* v_startInclusive_2522_; lean_object* v_endExclusive_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2530_; 
lean_dec(v___x_2502_);
lean_dec(v_val_2500_);
lean_dec(v_a_2419_);
lean_del_object(v___x_2416_);
lean_dec_ref(v_ands_2408_);
v_str_2521_ = lean_ctor_get(v___x_2501_, 0);
lean_inc_ref(v_str_2521_);
v_startInclusive_2522_ = lean_ctor_get(v___x_2501_, 1);
lean_inc(v_startInclusive_2522_);
v_endExclusive_2523_ = lean_ctor_get(v___x_2501_, 2);
lean_inc(v_endExclusive_2523_);
lean_dec(v___x_2501_);
v___x_2524_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2525_ = lean_string_utf8_extract_fast(v_str_2521_, v_startInclusive_2522_, v_endExclusive_2523_);
lean_dec(v_endExclusive_2523_);
lean_dec(v_startInclusive_2522_);
lean_dec_ref(v_str_2521_);
v___x_2526_ = lean_string_append(v___x_2524_, v___x_2525_);
lean_dec_ref(v___x_2525_);
v___x_2527_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2528_ = lean_string_append(v___x_2526_, v___x_2527_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2528_);
v___x_2530_ = v___x_2422_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_a_2420_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
else
{
lean_object* v_str_2532_; lean_object* v_startInclusive_2533_; lean_object* v_endExclusive_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_inc(v___x_2498_);
lean_dec(v___x_2499_);
lean_dec(v_a_2419_);
lean_del_object(v___x_2416_);
lean_dec(v_a_2413_);
lean_dec_ref(v_ands_2408_);
v_str_2532_ = lean_ctor_get(v___x_2498_, 0);
lean_inc_ref(v_str_2532_);
v_startInclusive_2533_ = lean_ctor_get(v___x_2498_, 1);
lean_inc(v_startInclusive_2533_);
v_endExclusive_2534_ = lean_ctor_get(v___x_2498_, 2);
lean_inc(v_endExclusive_2534_);
lean_dec(v___x_2498_);
v___x_2535_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2536_ = lean_string_utf8_extract_fast(v_str_2532_, v_startInclusive_2533_, v_endExclusive_2534_);
lean_dec(v_endExclusive_2534_);
lean_dec(v_startInclusive_2533_);
lean_dec_ref(v_str_2532_);
v___x_2537_ = lean_string_append(v___x_2535_, v___x_2536_);
lean_dec_ref(v___x_2536_);
v___x_2538_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2539_ = lean_string_append(v___x_2537_, v___x_2538_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2539_);
v___x_2541_ = v___x_2422_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_a_2420_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_array_fget(v_a_2413_, v___x_2410_);
lean_dec(v_a_2413_);
v___x_2544_ = l_String_Slice_toNat_x3f(v___x_2543_);
if (lean_obj_tag(v___x_2544_) == 1)
{
lean_object* v_val_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v_minVer_2550_; 
lean_dec(v___x_2543_);
v_val_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc_n(v_val_2545_, 2);
lean_dec_ref_known(v___x_2544_, 1);
v___x_2546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2546_, 0, v_val_2545_);
lean_ctor_set(v___x_2546_, 1, v___x_2410_);
lean_ctor_set(v___x_2546_, 2, v___x_2410_);
v___x_2547_ = lean_nat_add(v_val_2545_, v___x_2425_);
lean_dec(v_val_2545_);
v___x_2548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v___x_2410_);
lean_ctor_set(v___x_2548_, 2, v___x_2410_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v_a_2419_);
lean_ctor_set(v___x_2416_, 0, v___x_2546_);
v_minVer_2550_ = v___x_2416_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_a_2419_);
v_minVer_2550_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v_maxVer_2552_; uint8_t v___x_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2551_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2552_, 0, v___x_2548_);
lean_ctor_set(v_maxVer_2552_, 1, v___x_2551_);
v___x_2553_ = 3;
v___x_2554_ = 0;
v___x_2555_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2555_, 0, v_minVer_2550_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*1, v___x_2553_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*1 + 1, v___x_2554_);
v___x_2556_ = lean_array_push(v_ands_2408_, v___x_2555_);
v___x_2557_ = 0;
v___x_2558_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2558_, 0, v_maxVer_2552_);
lean_ctor_set_uint8(v___x_2558_, sizeof(void*)*1, v___x_2557_);
lean_ctor_set_uint8(v___x_2558_, sizeof(void*)*1 + 1, v___x_2426_);
v___x_2559_ = lean_array_push(v___x_2556_, v___x_2558_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2559_);
v___x_2561_ = v___x_2422_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_a_2420_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
else
{
lean_object* v_str_2564_; lean_object* v_startInclusive_2565_; lean_object* v_endExclusive_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
lean_dec(v___x_2544_);
lean_dec(v_a_2419_);
lean_del_object(v___x_2416_);
lean_dec_ref(v_ands_2408_);
v_str_2564_ = lean_ctor_get(v___x_2543_, 0);
lean_inc_ref(v_str_2564_);
v_startInclusive_2565_ = lean_ctor_get(v___x_2543_, 1);
lean_inc(v_startInclusive_2565_);
v_endExclusive_2566_ = lean_ctor_get(v___x_2543_, 2);
lean_inc(v_endExclusive_2566_);
lean_dec(v___x_2543_);
v___x_2567_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2568_ = lean_string_utf8_extract_fast(v_str_2564_, v_startInclusive_2565_, v_endExclusive_2566_);
lean_dec(v_endExclusive_2566_);
lean_dec(v_startInclusive_2565_);
lean_dec_ref(v_str_2564_);
v___x_2569_ = lean_string_append(v___x_2567_, v___x_2568_);
lean_dec_ref(v___x_2568_);
v___x_2570_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2571_ = lean_string_append(v___x_2569_, v___x_2570_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2571_);
v___x_2573_ = v___x_2422_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_a_2420_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_del_object(v___x_2416_);
lean_dec(v_a_2413_);
lean_dec_ref(v_ands_2408_);
v_a_2576_ = lean_ctor_get(v___x_2418_, 0);
v_a_2577_ = lean_ctor_get(v___x_2418_, 1);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2418_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_inc(v_a_2576_);
lean_dec(v___x_2418_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2576_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(lean_object* v_s_2588_, lean_object* v_ands_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v_a_2594_; lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2817_; 
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2590_);
lean_inc_ref(v_s_2588_);
v___x_2593_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2588_, v___x_2592_, v_a_2590_, v_a_2590_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_a_2595_ = lean_ctor_get(v___x_2593_, 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2597_ = v___x_2593_;
v_isShared_2598_ = v_isSharedCheck_2817_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2817_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; 
v___x_2599_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2588_, v_a_2595_);
lean_dec_ref(v_s_2588_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2807_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_a_2601_ = lean_ctor_get(v___x_2599_, 1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2603_ = v___x_2599_;
v_isShared_2604_ = v_isSharedCheck_2807_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2807_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2605_ = lean_array_get_size(v_a_2594_);
v___x_2606_ = lean_unsigned_to_nat(1u);
v___x_2607_ = lean_nat_dec_eq(v___x_2605_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = lean_unsigned_to_nat(2u);
v___x_2609_ = lean_nat_dec_eq(v___x_2605_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = lean_unsigned_to_nat(3u);
v___x_2611_ = lean_nat_dec_eq(v___x_2605_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_dec(v_a_2600_);
lean_del_object(v___x_2597_);
lean_dec(v_a_2594_);
lean_dec_ref(v_ands_2589_);
v___x_2612_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0));
v___x_2613_ = l_Nat_reprFast(v___x_2605_);
v___x_2614_ = lean_string_append(v___x_2612_, v___x_2613_);
lean_dec_ref(v___x_2613_);
v___x_2615_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2616_ = lean_string_append(v___x_2614_, v___x_2615_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2616_);
v___x_2618_ = v___x_2603_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_a_2601_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_array_fget_borrowed(v_a_2594_, v___x_2591_);
v___x_2621_ = l_String_Slice_toNat_x3f(v___x_2620_);
if (lean_obj_tag(v___x_2621_) == 1)
{
lean_object* v_val_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_val_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = lean_array_fget_borrowed(v_a_2594_, v___x_2606_);
v___x_2624_ = l_String_Slice_toNat_x3f(v___x_2623_);
if (lean_obj_tag(v___x_2624_) == 1)
{
lean_object* v_val_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_val_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_val_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v___x_2626_ = lean_array_fget(v_a_2594_, v___x_2608_);
lean_dec(v_a_2594_);
v___x_2627_ = l_String_Slice_toNat_x3f(v___x_2626_);
if (lean_obj_tag(v___x_2627_) == 1)
{
lean_object* v_val_2628_; uint8_t v___x_2629_; 
lean_dec(v___x_2626_);
v_val_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_val_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = lean_nat_dec_eq(v_val_2622_, v___x_2591_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_minVer_2633_; lean_object* v___x_2634_; lean_object* v_maxVer_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_del_object(v___x_2597_);
lean_inc(v_val_2622_);
v___x_2630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2630_, 0, v_val_2622_);
lean_ctor_set(v___x_2630_, 1, v_val_2625_);
lean_ctor_set(v___x_2630_, 2, v_val_2628_);
v___x_2631_ = lean_nat_add(v_val_2622_, v___x_2606_);
lean_dec(v_val_2622_);
v___x_2632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
lean_ctor_set(v___x_2632_, 1, v___x_2591_);
lean_ctor_set(v___x_2632_, 2, v___x_2591_);
v_minVer_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2633_, 0, v___x_2630_);
lean_ctor_set(v_minVer_2633_, 1, v_a_2600_);
v___x_2634_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2635_, 0, v___x_2632_);
lean_ctor_set(v_maxVer_2635_, 1, v___x_2634_);
v___x_2636_ = 3;
v___x_2637_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2637_, 0, v_minVer_2633_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*1, v___x_2636_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*1 + 1, v___x_2629_);
v___x_2638_ = lean_array_push(v_ands_2589_, v___x_2637_);
v___x_2639_ = 0;
v___x_2640_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2640_, 0, v_maxVer_2635_);
lean_ctor_set_uint8(v___x_2640_, sizeof(void*)*1, v___x_2639_);
lean_ctor_set_uint8(v___x_2640_, sizeof(void*)*1 + 1, v___x_2611_);
v___x_2641_ = lean_array_push(v___x_2638_, v___x_2640_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2641_);
v___x_2643_ = v___x_2603_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_a_2601_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
else
{
uint8_t v___x_2645_; uint8_t v___y_2647_; 
v___x_2645_ = lean_nat_dec_eq(v_val_2625_, v___x_2591_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v_minVer_2666_; lean_object* v___x_2667_; lean_object* v_maxVer_2668_; uint8_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_del_object(v___x_2603_);
lean_inc(v_val_2625_);
lean_inc(v_val_2622_);
v___x_2663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2663_, 0, v_val_2622_);
lean_ctor_set(v___x_2663_, 1, v_val_2625_);
lean_ctor_set(v___x_2663_, 2, v_val_2628_);
v___x_2664_ = lean_nat_add(v_val_2625_, v___x_2606_);
lean_dec(v_val_2625_);
v___x_2665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2665_, 0, v_val_2622_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
lean_ctor_set(v___x_2665_, 2, v___x_2591_);
v_minVer_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2666_, 0, v___x_2663_);
lean_ctor_set(v_minVer_2666_, 1, v_a_2600_);
v___x_2667_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2668_, 0, v___x_2665_);
lean_ctor_set(v_maxVer_2668_, 1, v___x_2667_);
v___x_2669_ = 3;
v___x_2670_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2670_, 0, v_minVer_2666_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*1, v___x_2669_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*1 + 1, v___x_2645_);
v___x_2671_ = lean_array_push(v_ands_2589_, v___x_2670_);
v___x_2672_ = 0;
v___x_2673_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2673_, 0, v_maxVer_2668_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*1, v___x_2672_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*1 + 1, v___x_2629_);
v___x_2674_ = lean_array_push(v___x_2671_, v___x_2673_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 1, v_a_2601_);
lean_ctor_set(v___x_2597_, 0, v___x_2674_);
v___x_2676_ = v___x_2597_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2601_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
else
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_nat_dec_eq(v_val_2628_, v___x_2591_);
if (v___x_2678_ == 0)
{
lean_del_object(v___x_2597_);
v___y_2647_ = v___x_2609_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2679_ = lean_string_utf8_byte_size(v_a_2600_);
v___x_2680_ = lean_nat_dec_eq(v___x_2679_, v___x_2591_);
if (v___x_2680_ == 0)
{
lean_del_object(v___x_2597_);
v___y_2647_ = v___x_2680_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
lean_dec(v_val_2628_);
lean_dec(v_val_2625_);
lean_dec(v_val_2622_);
lean_del_object(v___x_2603_);
lean_dec(v_a_2600_);
lean_dec_ref(v_ands_2589_);
v___x_2681_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1));
if (v_isShared_2598_ == 0)
{
lean_ctor_set_tag(v___x_2597_, 1);
lean_ctor_set(v___x_2597_, 1, v_a_2601_);
lean_ctor_set(v___x_2597_, 0, v___x_2681_);
v___x_2683_ = v___x_2597_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_a_2601_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
v___jp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v_minVer_2651_; lean_object* v___x_2652_; lean_object* v_maxVer_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
lean_inc(v_val_2628_);
lean_inc(v_val_2625_);
lean_inc(v_val_2622_);
v___x_2648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2648_, 0, v_val_2622_);
lean_ctor_set(v___x_2648_, 1, v_val_2625_);
lean_ctor_set(v___x_2648_, 2, v_val_2628_);
v___x_2649_ = lean_nat_add(v_val_2628_, v___x_2606_);
lean_dec(v_val_2628_);
v___x_2650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2650_, 0, v_val_2622_);
lean_ctor_set(v___x_2650_, 1, v_val_2625_);
lean_ctor_set(v___x_2650_, 2, v___x_2649_);
v_minVer_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2651_, 0, v___x_2648_);
lean_ctor_set(v_minVer_2651_, 1, v_a_2600_);
v___x_2652_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2653_, 0, v___x_2650_);
lean_ctor_set(v_maxVer_2653_, 1, v___x_2652_);
v___x_2654_ = 3;
v___x_2655_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2655_, 0, v_minVer_2651_);
lean_ctor_set_uint8(v___x_2655_, sizeof(void*)*1, v___x_2654_);
lean_ctor_set_uint8(v___x_2655_, sizeof(void*)*1 + 1, v___y_2647_);
v___x_2656_ = lean_array_push(v_ands_2589_, v___x_2655_);
v___x_2657_ = 0;
v___x_2658_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2658_, 0, v_maxVer_2653_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*1, v___x_2657_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*1 + 1, v___x_2645_);
v___x_2659_ = lean_array_push(v___x_2656_, v___x_2658_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2659_);
v___x_2661_ = v___x_2603_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_a_2601_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
else
{
lean_object* v_str_2685_; lean_object* v_startInclusive_2686_; lean_object* v_endExclusive_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
lean_dec(v___x_2627_);
lean_dec(v_val_2625_);
lean_dec(v_val_2622_);
lean_dec(v_a_2600_);
lean_del_object(v___x_2597_);
lean_dec_ref(v_ands_2589_);
v_str_2685_ = lean_ctor_get(v___x_2626_, 0);
lean_inc_ref(v_str_2685_);
v_startInclusive_2686_ = lean_ctor_get(v___x_2626_, 1);
lean_inc(v_startInclusive_2686_);
v_endExclusive_2687_ = lean_ctor_get(v___x_2626_, 2);
lean_inc(v_endExclusive_2687_);
lean_dec(v___x_2626_);
v___x_2688_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2689_ = lean_string_utf8_extract_fast(v_str_2685_, v_startInclusive_2686_, v_endExclusive_2687_);
lean_dec(v_endExclusive_2687_);
lean_dec(v_startInclusive_2686_);
lean_dec_ref(v_str_2685_);
v___x_2690_ = lean_string_append(v___x_2688_, v___x_2689_);
lean_dec_ref(v___x_2689_);
v___x_2691_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2692_ = lean_string_append(v___x_2690_, v___x_2691_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2692_);
v___x_2694_ = v___x_2603_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_a_2601_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
else
{
lean_object* v_str_2696_; lean_object* v_startInclusive_2697_; lean_object* v_endExclusive_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
lean_inc(v___x_2623_);
lean_dec(v___x_2624_);
lean_dec(v_val_2622_);
lean_dec(v_a_2600_);
lean_del_object(v___x_2597_);
lean_dec(v_a_2594_);
lean_dec_ref(v_ands_2589_);
v_str_2696_ = lean_ctor_get(v___x_2623_, 0);
lean_inc_ref(v_str_2696_);
v_startInclusive_2697_ = lean_ctor_get(v___x_2623_, 1);
lean_inc(v_startInclusive_2697_);
v_endExclusive_2698_ = lean_ctor_get(v___x_2623_, 2);
lean_inc(v_endExclusive_2698_);
lean_dec(v___x_2623_);
v___x_2699_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2700_ = lean_string_utf8_extract_fast(v_str_2696_, v_startInclusive_2697_, v_endExclusive_2698_);
lean_dec(v_endExclusive_2698_);
lean_dec(v_startInclusive_2697_);
lean_dec_ref(v_str_2696_);
v___x_2701_ = lean_string_append(v___x_2699_, v___x_2700_);
lean_dec_ref(v___x_2700_);
v___x_2702_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2703_ = lean_string_append(v___x_2701_, v___x_2702_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2703_);
v___x_2705_ = v___x_2603_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_a_2601_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
else
{
lean_object* v_str_2707_; lean_object* v_startInclusive_2708_; lean_object* v_endExclusive_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
lean_inc(v___x_2620_);
lean_dec(v___x_2621_);
lean_dec(v_a_2600_);
lean_del_object(v___x_2597_);
lean_dec(v_a_2594_);
lean_dec_ref(v_ands_2589_);
v_str_2707_ = lean_ctor_get(v___x_2620_, 0);
lean_inc_ref(v_str_2707_);
v_startInclusive_2708_ = lean_ctor_get(v___x_2620_, 1);
lean_inc(v_startInclusive_2708_);
v_endExclusive_2709_ = lean_ctor_get(v___x_2620_, 2);
lean_inc(v_endExclusive_2709_);
lean_dec(v___x_2620_);
v___x_2710_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2711_ = lean_string_utf8_extract_fast(v_str_2707_, v_startInclusive_2708_, v_endExclusive_2709_);
lean_dec(v_endExclusive_2709_);
lean_dec(v_startInclusive_2708_);
lean_dec_ref(v_str_2707_);
v___x_2712_ = lean_string_append(v___x_2710_, v___x_2711_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2714_ = lean_string_append(v___x_2712_, v___x_2713_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2714_);
v___x_2716_ = v___x_2603_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_a_2601_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_del_object(v___x_2597_);
v___x_2718_ = lean_array_fget_borrowed(v_a_2594_, v___x_2591_);
v___x_2719_ = l_String_Slice_toNat_x3f(v___x_2718_);
if (lean_obj_tag(v___x_2719_) == 1)
{
lean_object* v_val_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v_val_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_val_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v___x_2721_ = lean_array_fget(v_a_2594_, v___x_2606_);
lean_dec(v_a_2594_);
v___x_2722_ = l_String_Slice_toNat_x3f(v___x_2721_);
if (lean_obj_tag(v___x_2722_) == 1)
{
lean_object* v_val_2723_; uint8_t v___x_2724_; 
lean_dec(v___x_2721_);
v_val_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_val_2723_);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = lean_nat_dec_eq(v_val_2720_, v___x_2591_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v_minVer_2728_; lean_object* v___x_2729_; lean_object* v_maxVer_2730_; uint8_t v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_inc(v_val_2720_);
v___x_2725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2725_, 0, v_val_2720_);
lean_ctor_set(v___x_2725_, 1, v_val_2723_);
lean_ctor_set(v___x_2725_, 2, v___x_2591_);
v___x_2726_ = lean_nat_add(v_val_2720_, v___x_2606_);
lean_dec(v_val_2720_);
v___x_2727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
lean_ctor_set(v___x_2727_, 1, v___x_2591_);
lean_ctor_set(v___x_2727_, 2, v___x_2591_);
v_minVer_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2728_, 0, v___x_2725_);
lean_ctor_set(v_minVer_2728_, 1, v_a_2600_);
v___x_2729_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2730_, 0, v___x_2727_);
lean_ctor_set(v_maxVer_2730_, 1, v___x_2729_);
v___x_2731_ = 3;
v___x_2732_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2732_, 0, v_minVer_2728_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*1, v___x_2731_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*1 + 1, v___x_2724_);
v___x_2733_ = lean_array_push(v_ands_2589_, v___x_2732_);
v___x_2734_ = 0;
v___x_2735_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2735_, 0, v_maxVer_2730_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*1, v___x_2734_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*1 + 1, v___x_2609_);
v___x_2736_ = lean_array_push(v___x_2733_, v___x_2735_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2736_);
v___x_2738_ = v___x_2603_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_a_2601_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v_minVer_2743_; lean_object* v___x_2744_; lean_object* v_maxVer_2745_; uint8_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
lean_inc(v_val_2723_);
lean_inc(v_val_2720_);
v___x_2740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2740_, 0, v_val_2720_);
lean_ctor_set(v___x_2740_, 1, v_val_2723_);
lean_ctor_set(v___x_2740_, 2, v___x_2591_);
v___x_2741_ = lean_nat_add(v_val_2723_, v___x_2606_);
lean_dec(v_val_2723_);
v___x_2742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2742_, 0, v_val_2720_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
lean_ctor_set(v___x_2742_, 2, v___x_2591_);
v_minVer_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2743_, 0, v___x_2740_);
lean_ctor_set(v_minVer_2743_, 1, v_a_2600_);
v___x_2744_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2745_, 0, v___x_2742_);
lean_ctor_set(v_maxVer_2745_, 1, v___x_2744_);
v___x_2746_ = 3;
v___x_2747_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2747_, 0, v_minVer_2743_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*1, v___x_2746_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*1 + 1, v___x_2607_);
v___x_2748_ = lean_array_push(v_ands_2589_, v___x_2747_);
v___x_2749_ = 0;
v___x_2750_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2750_, 0, v_maxVer_2745_);
lean_ctor_set_uint8(v___x_2750_, sizeof(void*)*1, v___x_2749_);
lean_ctor_set_uint8(v___x_2750_, sizeof(void*)*1 + 1, v___x_2724_);
v___x_2751_ = lean_array_push(v___x_2748_, v___x_2750_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2751_);
v___x_2753_ = v___x_2603_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_a_2601_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
else
{
lean_object* v_str_2755_; lean_object* v_startInclusive_2756_; lean_object* v_endExclusive_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
lean_dec(v___x_2722_);
lean_dec(v_val_2720_);
lean_dec(v_a_2600_);
lean_dec_ref(v_ands_2589_);
v_str_2755_ = lean_ctor_get(v___x_2721_, 0);
lean_inc_ref(v_str_2755_);
v_startInclusive_2756_ = lean_ctor_get(v___x_2721_, 1);
lean_inc(v_startInclusive_2756_);
v_endExclusive_2757_ = lean_ctor_get(v___x_2721_, 2);
lean_inc(v_endExclusive_2757_);
lean_dec(v___x_2721_);
v___x_2758_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2759_ = lean_string_utf8_extract_fast(v_str_2755_, v_startInclusive_2756_, v_endExclusive_2757_);
lean_dec(v_endExclusive_2757_);
lean_dec(v_startInclusive_2756_);
lean_dec_ref(v_str_2755_);
v___x_2760_ = lean_string_append(v___x_2758_, v___x_2759_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2762_ = lean_string_append(v___x_2760_, v___x_2761_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2762_);
v___x_2764_ = v___x_2603_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_a_2601_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
lean_object* v_str_2766_; lean_object* v_startInclusive_2767_; lean_object* v_endExclusive_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_inc(v___x_2718_);
lean_dec(v___x_2719_);
lean_dec(v_a_2600_);
lean_dec(v_a_2594_);
lean_dec_ref(v_ands_2589_);
v_str_2766_ = lean_ctor_get(v___x_2718_, 0);
lean_inc_ref(v_str_2766_);
v_startInclusive_2767_ = lean_ctor_get(v___x_2718_, 1);
lean_inc(v_startInclusive_2767_);
v_endExclusive_2768_ = lean_ctor_get(v___x_2718_, 2);
lean_inc(v_endExclusive_2768_);
lean_dec(v___x_2718_);
v___x_2769_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2770_ = lean_string_utf8_extract_fast(v_str_2766_, v_startInclusive_2767_, v_endExclusive_2768_);
lean_dec(v_endExclusive_2768_);
lean_dec(v_startInclusive_2767_);
lean_dec_ref(v_str_2766_);
v___x_2771_ = lean_string_append(v___x_2769_, v___x_2770_);
lean_dec_ref(v___x_2770_);
v___x_2772_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2773_ = lean_string_append(v___x_2771_, v___x_2772_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2773_);
v___x_2775_ = v___x_2603_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_a_2601_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_del_object(v___x_2597_);
v___x_2777_ = lean_array_fget(v_a_2594_, v___x_2591_);
lean_dec(v_a_2594_);
v___x_2778_ = l_String_Slice_toNat_x3f(v___x_2777_);
if (lean_obj_tag(v___x_2778_) == 1)
{
lean_object* v_val_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v_minVer_2783_; lean_object* v___x_2784_; lean_object* v_maxVer_2785_; uint8_t v___x_2786_; uint8_t v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; uint8_t v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
lean_dec(v___x_2777_);
v_val_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc_n(v_val_2779_, 2);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2780_, 0, v_val_2779_);
lean_ctor_set(v___x_2780_, 1, v___x_2591_);
lean_ctor_set(v___x_2780_, 2, v___x_2591_);
v___x_2781_ = lean_nat_add(v_val_2779_, v___x_2606_);
lean_dec(v_val_2779_);
v___x_2782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
lean_ctor_set(v___x_2782_, 1, v___x_2591_);
lean_ctor_set(v___x_2782_, 2, v___x_2591_);
v_minVer_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2783_, 0, v___x_2780_);
lean_ctor_set(v_minVer_2783_, 1, v_a_2600_);
v___x_2784_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2785_, 0, v___x_2782_);
lean_ctor_set(v_maxVer_2785_, 1, v___x_2784_);
v___x_2786_ = 3;
v___x_2787_ = 0;
v___x_2788_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2788_, 0, v_minVer_2783_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*1, v___x_2786_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*1 + 1, v___x_2787_);
v___x_2789_ = lean_array_push(v_ands_2589_, v___x_2788_);
v___x_2790_ = 0;
v___x_2791_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2791_, 0, v_maxVer_2785_);
lean_ctor_set_uint8(v___x_2791_, sizeof(void*)*1, v___x_2790_);
lean_ctor_set_uint8(v___x_2791_, sizeof(void*)*1 + 1, v___x_2607_);
v___x_2792_ = lean_array_push(v___x_2789_, v___x_2791_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2792_);
v___x_2794_ = v___x_2603_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_a_2601_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
else
{
lean_object* v_str_2796_; lean_object* v_startInclusive_2797_; lean_object* v_endExclusive_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2805_; 
lean_dec(v___x_2778_);
lean_dec(v_a_2600_);
lean_dec_ref(v_ands_2589_);
v_str_2796_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_ref(v_str_2796_);
v_startInclusive_2797_ = lean_ctor_get(v___x_2777_, 1);
lean_inc(v_startInclusive_2797_);
v_endExclusive_2798_ = lean_ctor_get(v___x_2777_, 2);
lean_inc(v_endExclusive_2798_);
lean_dec(v___x_2777_);
v___x_2799_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2800_ = lean_string_utf8_extract_fast(v_str_2796_, v_startInclusive_2797_, v_endExclusive_2798_);
lean_dec(v_endExclusive_2798_);
lean_dec(v_startInclusive_2797_);
lean_dec_ref(v_str_2796_);
v___x_2801_ = lean_string_append(v___x_2799_, v___x_2800_);
lean_dec_ref(v___x_2800_);
v___x_2802_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2803_ = lean_string_append(v___x_2801_, v___x_2802_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2803_);
v___x_2805_ = v___x_2603_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_a_2601_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_del_object(v___x_2597_);
lean_dec(v_a_2594_);
lean_dec_ref(v_ands_2589_);
v_a_2808_ = lean_ctor_get(v___x_2599_, 0);
v_a_2809_ = lean_ctor_get(v___x_2599_, 1);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2599_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_inc(v_a_2808_);
lean_dec(v___x_2599_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2808_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(lean_object* v_s_2823_, lean_object* v_ands_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v___y_2827_; lean_object* v___y_2831_; lean_object* v___y_2836_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2989_; 
v___x_2839_ = lean_unsigned_to_nat(0u);
v___x_2840_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2825_);
lean_inc_ref(v_s_2823_);
v___x_2841_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2823_, v___x_2840_, v_a_2825_, v_a_2825_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_a_2843_ = lean_ctor_get(v___x_2841_, 1);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2845_ = v___x_2841_;
v_isShared_2846_ = v_isSharedCheck_2989_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2989_;
goto v_resetjp_2844_;
}
v___jp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0));
v___x_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___y_2827_);
return v___x_2829_;
}
v___jp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2832_ = ((lean_object*)(l_Lake_VerComparator_wild));
v___x_2833_ = lean_array_push(v_ands_2824_, v___x_2832_);
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
lean_ctor_set(v___x_2834_, 1, v___y_2831_);
return v___x_2834_;
}
v___jp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1));
v___x_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v___y_2836_);
return v___x_2838_;
}
v_resetjp_2844_:
{
lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___x_2962_; lean_object* v___y_2964_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v___x_2962_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__1));
v___x_2984_ = lean_array_get_size(v_a_2842_);
v___x_2985_ = lean_nat_dec_lt(v___x_2839_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_box(0);
v___y_2964_ = v___x_2986_;
goto v___jp_2963_;
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_array_fget_borrowed(v_a_2842_, v___x_2839_);
lean_inc(v___x_2987_);
v___x_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
v___y_2964_ = v___x_2988_;
goto v___jp_2963_;
}
v___jp_2847_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v___x_2853_ = lean_unsigned_to_nat(3u);
v___x_2854_ = lean_array_get_size(v_a_2842_);
lean_dec(v_a_2842_);
v___x_2855_ = lean_nat_dec_lt(v___x_2853_, v___x_2854_);
if (v___x_2855_ == 0)
{
switch(lean_obj_tag(v___y_2849_))
{
case 2:
{
switch(lean_obj_tag(v___y_2851_))
{
case 2:
{
if (lean_obj_tag(v___y_2848_) == 1)
{
lean_object* v_n_2856_; lean_object* v_n_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v_minVer_2862_; lean_object* v_maxVer_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; uint8_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2872_; 
v_n_2856_ = lean_ctor_get(v___y_2849_, 0);
lean_inc_n(v_n_2856_, 2);
lean_dec_ref_known(v___y_2849_, 1);
v_n_2857_ = lean_ctor_get(v___y_2851_, 0);
lean_inc_n(v_n_2857_, 2);
lean_dec_ref_known(v___y_2851_, 1);
v___x_2858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2858_, 0, v_n_2856_);
lean_ctor_set(v___x_2858_, 1, v_n_2857_);
lean_ctor_set(v___x_2858_, 2, v___x_2839_);
v___x_2859_ = lean_nat_add(v_n_2857_, v___y_2852_);
lean_dec(v_n_2857_);
v___x_2860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2860_, 0, v_n_2856_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
lean_ctor_set(v___x_2860_, 2, v___x_2839_);
v___x_2861_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2862_, 0, v___x_2858_);
lean_ctor_set(v_minVer_2862_, 1, v___x_2861_);
v_maxVer_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2863_, 0, v___x_2860_);
lean_ctor_set(v_maxVer_2863_, 1, v___x_2861_);
v___x_2864_ = 3;
v___x_2865_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2865_, 0, v_minVer_2862_);
lean_ctor_set_uint8(v___x_2865_, sizeof(void*)*1, v___x_2864_);
lean_ctor_set_uint8(v___x_2865_, sizeof(void*)*1 + 1, v___x_2855_);
v___x_2866_ = lean_array_push(v_ands_2824_, v___x_2865_);
v___x_2867_ = 0;
v___x_2868_ = 1;
v___x_2869_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2869_, 0, v_maxVer_2863_);
lean_ctor_set_uint8(v___x_2869_, sizeof(void*)*1, v___x_2867_);
lean_ctor_set_uint8(v___x_2869_, sizeof(void*)*1 + 1, v___x_2868_);
v___x_2870_ = lean_array_push(v___x_2866_, v___x_2869_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v___y_2850_);
lean_ctor_set(v___x_2845_, 0, v___x_2870_);
v___x_2872_ = v___x_2845_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v___y_2850_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
else
{
lean_dec_ref_known(v___y_2851_, 1);
lean_dec_ref_known(v___y_2849_, 1);
lean_dec(v___y_2848_);
lean_del_object(v___x_2845_);
lean_dec_ref(v_ands_2824_);
v___y_2836_ = v___y_2850_;
goto v___jp_2835_;
}
}
case 1:
{
if (lean_obj_tag(v___y_2848_) == 2)
{
lean_dec_ref_known(v___y_2848_, 1);
lean_dec_ref_known(v___y_2849_, 1);
lean_del_object(v___x_2845_);
lean_dec_ref(v_ands_2824_);
v___y_2827_ = v___y_2850_;
goto v___jp_2826_;
}
else
{
lean_object* v_n_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v_minVer_2879_; lean_object* v_maxVer_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; uint8_t v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
lean_dec(v___y_2848_);
v_n_2874_ = lean_ctor_get(v___y_2849_, 0);
lean_inc_n(v_n_2874_, 2);
lean_dec_ref_known(v___y_2849_, 1);
v___x_2875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2875_, 0, v_n_2874_);
lean_ctor_set(v___x_2875_, 1, v___x_2839_);
lean_ctor_set(v___x_2875_, 2, v___x_2839_);
v___x_2876_ = lean_nat_add(v_n_2874_, v___y_2852_);
lean_dec(v_n_2874_);
v___x_2877_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v___x_2839_);
lean_ctor_set(v___x_2877_, 2, v___x_2839_);
v___x_2878_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2879_, 0, v___x_2875_);
lean_ctor_set(v_minVer_2879_, 1, v___x_2878_);
v_maxVer_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2880_, 0, v___x_2877_);
lean_ctor_set(v_maxVer_2880_, 1, v___x_2878_);
v___x_2881_ = 3;
v___x_2882_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2882_, 0, v_minVer_2879_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*1, v___x_2881_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*1 + 1, v___x_2855_);
v___x_2883_ = lean_array_push(v_ands_2824_, v___x_2882_);
v___x_2884_ = 0;
v___x_2885_ = 1;
v___x_2886_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2886_, 0, v_maxVer_2880_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*1, v___x_2884_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*1 + 1, v___x_2885_);
v___x_2887_ = lean_array_push(v___x_2883_, v___x_2886_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v___y_2850_);
lean_ctor_set(v___x_2845_, 0, v___x_2887_);
v___x_2889_ = v___x_2845_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___y_2850_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
default: 
{
lean_dec_ref_known(v___y_2849_, 1);
lean_dec(v___y_2851_);
lean_dec(v___y_2848_);
lean_del_object(v___x_2845_);
lean_dec_ref(v_ands_2824_);
v___y_2836_ = v___y_2850_;
goto v___jp_2835_;
}
}
}
case 1:
{
if (lean_obj_tag(v___y_2848_) == 2)
{
lean_dec_ref_known(v___y_2848_, 1);
lean_dec(v___y_2851_);
lean_del_object(v___x_2845_);
lean_dec_ref(v_ands_2824_);
v___y_2827_ = v___y_2850_;
goto v___jp_2826_;
}
else
{
lean_dec(v___y_2848_);
if (lean_obj_tag(v___y_2851_) == 2)
{
lean_object* v___x_2891_; lean_object* v___x_2893_; 
lean_dec_ref_known(v___y_2851_, 1);
lean_dec_ref(v_ands_2824_);
v___x_2891_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2));
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 1);
lean_ctor_set(v___x_2845_, 1, v___y_2850_);
lean_ctor_set(v___x_2845_, 0, v___x_2891_);
v___x_2893_ = v___x_2845_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v___y_2850_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
else
{
lean_dec(v___y_2851_);
lean_del_object(v___x_2845_);
v___y_2831_ = v___y_2850_;
goto v___jp_2830_;
}
}
}
default: 
{
lean_dec(v___y_2849_);
lean_del_object(v___x_2845_);
if (lean_obj_tag(v___y_2851_) == 1)
{
if (lean_obj_tag(v___y_2848_) == 2)
{
lean_dec_ref_known(v___y_2848_, 1);
lean_dec_ref(v_ands_2824_);
v___y_2827_ = v___y_2850_;
goto v___jp_2826_;
}
else
{
lean_dec(v___y_2848_);
v___y_2831_ = v___y_2850_;
goto v___jp_2830_;
}
}
else
{
lean_dec(v___y_2851_);
lean_dec(v___y_2848_);
v___y_2831_ = v___y_2850_;
goto v___jp_2830_;
}
}
}
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2901_; 
lean_dec(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v_ands_2824_);
v___x_2895_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3));
v___x_2896_ = l_Nat_reprFast(v___x_2854_);
v___x_2897_ = lean_string_append(v___x_2895_, v___x_2896_);
lean_dec_ref(v___x_2896_);
v___x_2898_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2899_ = lean_string_append(v___x_2897_, v___x_2898_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 1);
lean_ctor_set(v___x_2845_, 1, v___y_2850_);
lean_ctor_set(v___x_2845_, 0, v___x_2899_);
v___x_2901_ = v___x_2845_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___y_2850_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
v___jp_2903_:
{
lean_object* v___x_2910_; 
v___x_2910_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2908_, v___y_2909_, v___y_2906_);
lean_dec(v___y_2909_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2927_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_a_2912_ = lean_ctor_get(v___x_2910_, 1);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2914_ = v___x_2910_;
v_isShared_2915_ = v_isSharedCheck_2927_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2927_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2916_ = lean_string_utf8_byte_size(v_s_2823_);
v___x_2917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2917_, 0, v_s_2823_);
lean_ctor_set(v___x_2917_, 1, v___x_2839_);
lean_ctor_set(v___x_2917_, 2, v___x_2916_);
v___x_2918_ = l_String_Slice_Pos_get_x3f(v___x_2917_, v_a_2912_);
lean_dec_ref_known(v___x_2917_, 3);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_del_object(v___x_2914_);
v___y_2848_ = v_a_2911_;
v___y_2849_ = v___y_2904_;
v___y_2850_ = v_a_2912_;
v___y_2851_ = v___y_2905_;
v___y_2852_ = v___y_2907_;
goto v___jp_2847_;
}
else
{
lean_object* v_val_2919_; uint32_t v___x_2920_; uint32_t v___x_2921_; uint8_t v___x_2922_; 
v_val_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_val_2919_);
lean_dec_ref_known(v___x_2918_, 1);
v___x_2920_ = 45;
v___x_2921_ = lean_unbox_uint32(v_val_2919_);
lean_dec(v_val_2919_);
v___x_2922_ = lean_uint32_dec_eq(v___x_2921_, v___x_2920_);
if (v___x_2922_ == 0)
{
lean_del_object(v___x_2914_);
v___y_2848_ = v_a_2911_;
v___y_2849_ = v___y_2904_;
v___y_2850_ = v_a_2912_;
v___y_2851_ = v___y_2905_;
v___y_2852_ = v___y_2907_;
goto v___jp_2847_;
}
else
{
lean_object* v___x_2923_; lean_object* v___x_2925_; 
lean_dec(v_a_2911_);
lean_dec(v___y_2905_);
lean_dec(v___y_2904_);
lean_del_object(v___x_2845_);
lean_dec(v_a_2842_);
lean_dec_ref(v_ands_2824_);
v___x_2923_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4));
if (v_isShared_2915_ == 0)
{
lean_ctor_set_tag(v___x_2914_, 1);
lean_ctor_set(v___x_2914_, 0, v___x_2923_);
v___x_2925_ = v___x_2914_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_a_2912_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v___y_2905_);
lean_dec(v___y_2904_);
lean_del_object(v___x_2845_);
lean_dec(v_a_2842_);
lean_dec_ref(v_ands_2824_);
lean_dec_ref(v_s_2823_);
v_a_2928_ = lean_ctor_get(v___x_2910_, 0);
v_a_2929_ = lean_ctor_get(v___x_2910_, 1);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2910_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_inc(v_a_2928_);
lean_dec(v___x_2910_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2928_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
v___jp_2937_:
{
lean_object* v___x_2943_; 
v___x_2943_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2939_, v___y_2942_, v___y_2940_);
lean_dec(v___y_2942_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v_a_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
v_a_2945_ = lean_ctor_get(v___x_2943_, 1);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___x_2943_, 2);
v___x_2946_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__12));
v___x_2947_ = lean_unsigned_to_nat(2u);
v___x_2948_ = lean_array_get_size(v_a_2842_);
v___x_2949_ = lean_nat_dec_lt(v___x_2947_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_box(0);
v___y_2904_ = v___y_2938_;
v___y_2905_ = v_a_2944_;
v___y_2906_ = v_a_2945_;
v___y_2907_ = v___y_2941_;
v___y_2908_ = v___x_2946_;
v___y_2909_ = v___x_2950_;
goto v___jp_2903_;
}
else
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_array_fget_borrowed(v_a_2842_, v___x_2947_);
lean_inc(v___x_2951_);
v___x_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
v___y_2904_ = v___y_2938_;
v___y_2905_ = v_a_2944_;
v___y_2906_ = v_a_2945_;
v___y_2907_ = v___y_2941_;
v___y_2908_ = v___x_2946_;
v___y_2909_ = v___x_2952_;
goto v___jp_2903_;
}
}
else
{
lean_object* v_a_2953_; lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec(v___y_2938_);
lean_del_object(v___x_2845_);
lean_dec(v_a_2842_);
lean_dec_ref(v_ands_2824_);
lean_dec_ref(v_s_2823_);
v_a_2953_ = lean_ctor_get(v___x_2943_, 0);
v_a_2954_ = lean_ctor_get(v___x_2943_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2943_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_inc(v_a_2953_);
lean_dec(v___x_2943_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2953_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
v___jp_2963_:
{
lean_object* v___x_2965_; 
v___x_2965_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___x_2962_, v___y_2964_, v_a_2843_);
lean_dec(v___y_2964_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v_a_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
v_a_2967_ = lean_ctor_get(v___x_2965_, 1);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2965_, 2);
v___x_2968_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__10));
v___x_2969_ = lean_unsigned_to_nat(1u);
v___x_2970_ = lean_array_get_size(v_a_2842_);
v___x_2971_ = lean_nat_dec_lt(v___x_2969_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_box(0);
v___y_2938_ = v_a_2966_;
v___y_2939_ = v___x_2968_;
v___y_2940_ = v_a_2967_;
v___y_2941_ = v___x_2969_;
v___y_2942_ = v___x_2972_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_array_fget_borrowed(v_a_2842_, v___x_2969_);
lean_inc(v___x_2973_);
v___x_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
v___y_2938_ = v_a_2966_;
v___y_2939_ = v___x_2968_;
v___y_2940_ = v_a_2967_;
v___y_2941_ = v___x_2969_;
v___y_2942_ = v___x_2974_;
goto v___jp_2937_;
}
}
else
{
lean_object* v_a_2975_; lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_del_object(v___x_2845_);
lean_dec(v_a_2842_);
lean_dec_ref(v_ands_2824_);
lean_dec_ref(v_s_2823_);
v_a_2975_ = lean_ctor_get(v___x_2965_, 0);
v_a_2976_ = lean_ctor_get(v___x_2965_, 1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2965_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_inc(v_a_2975_);
lean_dec(v___x_2965_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2975_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(lean_object* v_s_2996_, uint8_t v_needsRange_2997_, lean_object* v_ors_2998_, lean_object* v_ands_2999_, lean_object* v_p_3000_){
_start:
{
lean_object* v___x_3007_; uint8_t v_decide_3008_; 
v___x_3007_ = lean_string_utf8_byte_size(v_s_2996_);
v_decide_3008_ = lean_nat_dec_eq(v_p_3000_, v___x_3007_);
if (v_decide_3008_ == 0)
{
uint32_t v_c_3023_; uint8_t v___y_3119_; uint32_t v___x_3124_; uint8_t v___x_3125_; 
v_c_3023_ = lean_string_utf8_get_fast(v_s_2996_, v_p_3000_);
v___x_3124_ = 65;
v___x_3125_ = lean_uint32_dec_le(v___x_3124_, v_c_3023_);
if (v___x_3125_ == 0)
{
v___y_3119_ = v___x_3125_;
goto v___jp_3118_;
}
else
{
uint32_t v___x_3126_; uint8_t v___x_3127_; 
v___x_3126_ = 90;
v___x_3127_ = lean_uint32_dec_le(v_c_3023_, v___x_3126_);
v___y_3119_ = v___x_3127_;
goto v___jp_3118_;
}
v___jp_3024_:
{
uint32_t v___x_3025_; uint8_t v___x_3026_; 
v___x_3025_ = 42;
v___x_3026_ = lean_uint32_dec_eq(v_c_3023_, v___x_3025_);
if (v___x_3026_ == 0)
{
uint32_t v___x_3027_; uint8_t v___x_3028_; 
v___x_3027_ = 94;
v___x_3028_ = lean_uint32_dec_eq(v_c_3023_, v___x_3027_);
if (v___x_3028_ == 0)
{
uint32_t v___x_3029_; uint8_t v___x_3030_; 
v___x_3029_ = 126;
v___x_3030_ = lean_uint32_dec_eq(v_c_3023_, v___x_3029_);
if (v___x_3030_ == 0)
{
uint32_t v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = 32;
v___x_3032_ = lean_uint32_dec_eq(v_c_3023_, v___x_3031_);
if (v___x_3032_ == 0)
{
uint32_t v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = 9;
v___x_3034_ = lean_uint32_dec_eq(v_c_3023_, v___x_3033_);
if (v___x_3034_ == 0)
{
uint32_t v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = 13;
v___x_3036_ = lean_uint32_dec_eq(v_c_3023_, v___x_3035_);
if (v___x_3036_ == 0)
{
uint32_t v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = 10;
v___x_3038_ = lean_uint32_dec_eq(v_c_3023_, v___x_3037_);
if (v___x_3038_ == 0)
{
uint8_t v___x_3039_; uint32_t v___x_3040_; uint8_t v___x_3041_; 
v___x_3039_ = 1;
v___x_3040_ = 44;
v___x_3041_ = lean_uint32_dec_eq(v_c_3023_, v___x_3040_);
if (v___x_3041_ == 0)
{
uint32_t v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = 124;
v___x_3043_ = lean_uint32_dec_eq(v_c_3023_, v___x_3042_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; 
lean_inc_ref(v_s_2996_);
v___x_3044_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_2996_, v_p_3000_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v_a_3046_; lean_object* v___x_3047_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
v_a_3046_ = lean_ctor_get(v___x_3044_, 1);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3044_, 2);
v___x_3047_ = lean_array_push(v_ands_2999_, v_a_3045_);
v_needsRange_2997_ = v___x_3043_;
v_ands_2999_ = v___x_3047_;
v_p_3000_ = v_a_3046_;
goto _start;
}
else
{
lean_object* v_a_3049_; lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec_ref(v_ands_2999_);
lean_dec_ref(v_ors_2998_);
lean_dec_ref(v_s_2996_);
v_a_3049_ = lean_ctor_get(v___x_3044_, 0);
v_a_3050_ = lean_ctor_get(v___x_3044_, 1);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3044_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_inc(v_a_3049_);
lean_dec(v___x_3044_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3049_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
else
{
lean_object* v_p_3058_; uint8_t v_decide_3059_; 
v_p_3058_ = lean_string_utf8_next_fast(v_s_2996_, v_p_3000_);
lean_dec(v_p_3000_);
v_decide_3059_ = lean_nat_dec_eq(v_p_3058_, v___x_3007_);
if (v_decide_3059_ == 0)
{
uint32_t v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = lean_string_utf8_get_fast(v_s_2996_, v_p_3058_);
v___x_3061_ = lean_uint32_dec_eq(v___x_3060_, v___x_3042_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
lean_dec_ref(v_ands_2999_);
lean_dec_ref(v_ors_2998_);
lean_dec_ref(v_s_2996_);
v___x_3062_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v_p_3058_);
return v___x_3063_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v___x_3064_ = lean_array_get_size(v_ands_2999_);
v___x_3065_ = lean_unsigned_to_nat(0u);
v___x_3066_ = lean_nat_dec_eq(v___x_3064_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = lean_array_push(v_ors_2998_, v_ands_2999_);
v___x_3068_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2));
v___x_3069_ = lean_string_utf8_next_fast(v_s_2996_, v_p_3058_);
v_needsRange_2997_ = v___x_3039_;
v_ors_2998_ = v___x_3067_;
v_ands_2999_ = v___x_3068_;
v_p_3000_ = v___x_3069_;
goto _start;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_dec_ref(v_ands_2999_);
lean_dec_ref(v_ors_2998_);
lean_dec_ref(v_s_2996_);
v___x_3071_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v_p_3058_);
return v___x_3072_;
}
}
}
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_dec_ref(v_ands_2999_);
lean_dec_ref(v_ors_2998_);
lean_dec_ref(v_s_2996_);
v___x_3073_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v_p_3058_);
return v___x_3074_;
}
}
}
else
{
if (v_needsRange_2997_ == 0)
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_string_utf8_next_fast(v_s_2996_, v_p_3000_);
lean_dec(v_p_3000_);
v_needsRange_2997_ = v___x_3039_;
v_p_3000_ = v___x_3075_;
goto _start;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_dec_ref(v_ands_2999_);
lean_dec_ref(v_ors_2998_);
lean_dec_ref(v_s_2996_);
v___x_3077_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v_p_3000_);
return v___x_3078_;
}
}
}
else
{
goto v___jp_3004_;
}
}
else
{
goto v___jp_3004_;
}
}
else
{
goto v___jp_3004_;
}
}
else
{
goto v___jp_3004_;
}
}
else
{
lean_object* v_p_3079_; uint8_t v_decide_3080_; 
v_p_3079_ = lean_string_utf8_next_fast(v_s_2996_, v_p_3000_);
lean_dec(v_p_3000_);
v_decide_3080_ = lean_nat_dec_eq(v_p_3079_, v___x_3007_);
if (v_decide_3080_ == 0)
{
lean_object* v___x_3081_; 
lean_inc_ref(v_s_2996_);
v___x_3081_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(v_s_2996_, v_ands_2999_, v_p_3079_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v_a_3083_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
v_a_3083_ = lean_ctor_get(v___x_3081_, 1);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3081_, 2);
v_needsRange_2997_ = v_decide_3080_;
v_ands_2999_ = v_a_3082_;
v_p_3000_ = v_a_3083_;
goto _start;
}
else
{
lean_object* v_a_3085_; lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref(v_ors_2998_);
lean_dec_ref(v_s_2996_);
v_a_3085_ = lean_ctor_get(v___x_3081_, 0);
v_a_3086_ = lean_ctor_get(v___x_3081_, 1);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3081_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_inc(v_a_3085_);
lean_dec(v___x_3081_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3085_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec_ref(v_ands_2999_);
lean_dec_ref(v_ors_2998_);
lean_dec_ref(v_s_2996_);
v___x_3094_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3));
v___x_3095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v_p_3079_);
return v___x_3095_;
}
}
}
else
{
lean_object* v_p_3096_; uint8_t v_decide_3097_; 
v_p_3096_ = lean_string_utf8_next_fast(v_s_2996_, v_p_3000_);
lean_dec(v_p_3000_);
v_decide_3097_ = lean_nat_dec_eq(v_p_3096_, v___x_3007_);
if (v_decide_3097_ == 0)
{
lean_object* v___x_3098_; 
lean_inc_ref(v_s_2996_);
v___x_3098_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(v_s_2996_, v_ands_2999_, v_p_3096_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v_a_3100_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3099_);
v_a_3100_ = lean_ctor_get(v___x_3098_, 1);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3098_, 2);
v_needsRange_2997_ = v_decide_3097_;
v_ands_2999_ = v_a_3099_;
v_p_3000_ = v_a_3100_;
goto _start;
}
else
{
lean_object* v_a_3102_; lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref(v_ors_2998_);
lean_dec_ref(v_s_2996_);
v_a_3102_ = lean_ctor_get(v___x_3098_, 0);
v_a_3103_ = lean_ctor_get(v___x_3098_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3098_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_inc(v_a_3102_);
lean_dec(v___x_3098_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3102_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec_ref(v_ands_2999_);
lean_dec_ref(v_ors_2998_);
lean_dec_ref(v_s_2996_);
v___x_3111_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4));
v___x_3112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
lean_ctor_set(v___x_3112_, 1, v_p_3096_);
return v___x_3112_;
}
}
}
else
{
goto v___jp_3009_;
}
}
v___jp_3113_:
{
uint32_t v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = 48;
v___x_3115_ = lean_uint32_dec_le(v___x_3114_, v_c_3023_);
if (v___x_3115_ == 0)
{
goto v___jp_3024_;
}
else
{
uint32_t v___x_3116_; uint8_t v___x_3117_; 
v___x_3116_ = 57;
v___x_3117_ = lean_uint32_dec_le(v_c_3023_, v___x_3116_);
if (v___x_3117_ == 0)
{
goto v___jp_3024_;
}
else
{
goto v___jp_3009_;
}
}
}
v___jp_3118_:
{
if (v___y_3119_ == 0)
{
uint32_t v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = 97;
v___x_3121_ = lean_uint32_dec_le(v___x_3120_, v_c_3023_);
if (v___x_3121_ == 0)
{
goto v___jp_3113_;
}
else
{
uint32_t v___x_3122_; uint8_t v___x_3123_; 
v___x_3122_ = 122;
v___x_3123_ = lean_uint32_dec_le(v_c_3023_, v___x_3122_);
if (v___x_3123_ == 0)
{
goto v___jp_3113_;
}
else
{
goto v___jp_3009_;
}
}
}
else
{
goto v___jp_3009_;
}
}
}
else
{
lean_dec_ref(v_s_2996_);
if (v_needsRange_2997_ == 0)
{
lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3128_ = lean_array_get_size(v_ands_2999_);
v___x_3129_ = lean_unsigned_to_nat(0u);
v___x_3130_ = lean_nat_dec_eq(v___x_3128_, v___x_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_array_push(v_ors_2998_, v_ands_2999_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v_p_3000_);
return v___x_3132_;
}
else
{
lean_dec_ref(v_ands_2999_);
lean_dec_ref(v_ors_2998_);
goto v___jp_3001_;
}
}
else
{
lean_dec_ref(v_ands_2999_);
lean_dec_ref(v_ors_2998_);
goto v___jp_3001_;
}
}
v___jp_3001_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
lean_ctor_set(v___x_3003_, 1, v_p_3000_);
return v___x_3003_;
}
v___jp_3004_:
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_string_utf8_next_fast(v_s_2996_, v_p_3000_);
lean_dec(v_p_3000_);
v_p_3000_ = v___x_3005_;
goto _start;
}
v___jp_3009_:
{
lean_object* v___x_3010_; 
lean_inc_ref(v_s_2996_);
v___x_3010_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(v_s_2996_, v_ands_2999_, v_p_3000_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v_a_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
v_a_3012_ = lean_ctor_get(v___x_3010_, 1);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3010_, 2);
v_needsRange_2997_ = v_decide_3008_;
v_ands_2999_ = v_a_3011_;
v_p_3000_ = v_a_3012_;
goto _start;
}
else
{
lean_object* v_a_3014_; lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v_ors_2998_);
lean_dec_ref(v_s_2996_);
v_a_3014_ = lean_ctor_get(v___x_3010_, 0);
v_a_3015_ = lean_ctor_get(v___x_3010_, 1);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3010_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_inc(v_a_3014_);
lean_dec(v___x_3010_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3014_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(lean_object* v_s_3133_, lean_object* v_needsRange_3134_, lean_object* v_ors_3135_, lean_object* v_ands_3136_, lean_object* v_p_3137_){
_start:
{
uint8_t v_needsRange_boxed_3138_; lean_object* v_res_3139_; 
v_needsRange_boxed_3138_ = lean_unbox(v_needsRange_3134_);
v_res_3139_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3133_, v_needsRange_boxed_3138_, v_ors_3135_, v_ands_3136_, v_p_3137_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object* v_s_3142_, lean_object* v_a_3143_){
_start:
{
uint8_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = 1;
v___x_3145_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3142_);
v___x_3146_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3142_, v___x_3144_, v___x_3145_, v___x_3145_, v_a_3143_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3156_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_a_3148_ = lean_ctor_get(v___x_3146_, 1);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3150_ = v___x_3146_;
v_isShared_3151_ = v_isSharedCheck_3156_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3156_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v_s_3142_);
lean_ctor_set(v___x_3152_, 1, v_a_3147_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v___x_3152_);
v___x_3154_ = v___x_3150_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v_a_3148_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec_ref(v_s_3142_);
v_a_3157_ = lean_ctor_get(v___x_3146_, 0);
v_a_3158_ = lean_ctor_get(v___x_3146_, 1);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3146_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_inc(v_a_3157_);
lean_dec(v___x_3146_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3157_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_parse(lean_object* v_s_3166_){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3167_ = lean_unsigned_to_nat(0u);
v___x_3168_ = lean_string_utf8_byte_size(v_s_3166_);
v___x_3169_ = 1;
v___x_3170_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3166_);
v___x_3171_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3166_, v___x_3169_, v___x_3170_, v___x_3170_, v___x_3167_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3186_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_a_3173_ = lean_ctor_get(v___x_3171_, 1);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3175_ = v___x_3171_;
v_isShared_3176_ = v_isSharedCheck_3186_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3186_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
uint8_t v_decide_3177_; 
v_decide_3177_ = lean_nat_dec_eq(v_a_3173_, v___x_3168_);
if (v_decide_3177_ == 0)
{
lean_object* v_tail_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_del_object(v___x_3175_);
lean_dec(v_a_3172_);
v_tail_3178_ = lean_string_utf8_extract(v_s_3166_, v_a_3173_, v___x_3168_);
lean_dec(v_a_3173_);
lean_dec_ref(v_s_3166_);
v___x_3179_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_3180_ = lean_string_append(v___x_3179_, v_tail_3178_);
lean_dec_ref(v_tail_3178_);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
return v___x_3181_;
}
else
{
lean_object* v___x_3183_; 
lean_dec(v_a_3173_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 1, v_a_3172_);
lean_ctor_set(v___x_3175_, 0, v_s_3166_);
v___x_3183_ = v___x_3175_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_s_3166_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_a_3172_);
v___x_3183_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3188_; 
lean_dec_ref(v_s_3166_);
v_a_3187_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___x_3171_, 2);
v___x_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3188_, 0, v_a_3187_);
return v___x_3188_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(lean_object* v_ver_3191_, lean_object* v_as_3192_, size_t v_i_3193_, size_t v_stop_3194_){
_start:
{
uint8_t v___x_3195_; 
v___x_3195_ = lean_usize_dec_eq(v_i_3193_, v_stop_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; uint8_t v___x_3197_; 
v___x_3196_ = lean_array_uget_borrowed(v_as_3192_, v_i_3193_);
v___x_3197_ = l_Lake_VerComparator_test(v___x_3196_, v_ver_3191_);
if (v___x_3197_ == 0)
{
uint8_t v___x_3198_; 
v___x_3198_ = 1;
return v___x_3198_;
}
else
{
size_t v___x_3199_; size_t v___x_3200_; 
v___x_3199_ = ((size_t)1ULL);
v___x_3200_ = lean_usize_add(v_i_3193_, v___x_3199_);
v_i_3193_ = v___x_3200_;
goto _start;
}
}
else
{
uint8_t v___x_3202_; 
v___x_3202_ = 0;
return v___x_3202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0___boxed(lean_object* v_ver_3203_, lean_object* v_as_3204_, lean_object* v_i_3205_, lean_object* v_stop_3206_){
_start:
{
size_t v_i_boxed_3207_; size_t v_stop_boxed_3208_; uint8_t v_res_3209_; lean_object* v_r_3210_; 
v_i_boxed_3207_ = lean_unbox_usize(v_i_3205_);
lean_dec(v_i_3205_);
v_stop_boxed_3208_ = lean_unbox_usize(v_stop_3206_);
lean_dec(v_stop_3206_);
v_res_3209_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3203_, v_as_3204_, v_i_boxed_3207_, v_stop_boxed_3208_);
lean_dec_ref(v_as_3204_);
lean_dec_ref(v_ver_3203_);
v_r_3210_ = lean_box(v_res_3209_);
return v_r_3210_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(lean_object* v_ver_3211_, lean_object* v_as_3212_, size_t v_i_3213_, size_t v_stop_3214_){
_start:
{
uint8_t v___x_3215_; 
v___x_3215_ = lean_usize_dec_eq(v_i_3213_, v_stop_3214_);
if (v___x_3215_ == 0)
{
uint8_t v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v___x_3216_ = 1;
v___x_3217_ = lean_array_uget_borrowed(v_as_3212_, v_i_3213_);
v___x_3218_ = lean_unsigned_to_nat(0u);
v___x_3219_ = lean_array_get_size(v___x_3217_);
v___x_3220_ = lean_nat_dec_lt(v___x_3218_, v___x_3219_);
if (v___x_3220_ == 0)
{
return v___x_3216_;
}
else
{
if (v___x_3220_ == 0)
{
return v___x_3216_;
}
else
{
size_t v___x_3221_; size_t v___x_3222_; uint8_t v___x_3223_; 
v___x_3221_ = ((size_t)0ULL);
v___x_3222_ = lean_usize_of_nat(v___x_3219_);
v___x_3223_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3211_, v___x_3217_, v___x_3221_, v___x_3222_);
if (v___x_3223_ == 0)
{
return v___x_3216_;
}
else
{
size_t v___x_3224_; size_t v___x_3225_; 
v___x_3224_ = ((size_t)1ULL);
v___x_3225_ = lean_usize_add(v_i_3213_, v___x_3224_);
v_i_3213_ = v___x_3225_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3227_; 
v___x_3227_ = 0;
return v___x_3227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1___boxed(lean_object* v_ver_3228_, lean_object* v_as_3229_, lean_object* v_i_3230_, lean_object* v_stop_3231_){
_start:
{
size_t v_i_boxed_3232_; size_t v_stop_boxed_3233_; uint8_t v_res_3234_; lean_object* v_r_3235_; 
v_i_boxed_3232_ = lean_unbox_usize(v_i_3230_);
lean_dec(v_i_3230_);
v_stop_boxed_3233_ = lean_unbox_usize(v_stop_3231_);
lean_dec(v_stop_3231_);
v_res_3234_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3228_, v_as_3229_, v_i_boxed_3232_, v_stop_boxed_3233_);
lean_dec_ref(v_as_3229_);
lean_dec_ref(v_ver_3228_);
v_r_3235_ = lean_box(v_res_3234_);
return v_r_3235_;
}
}
LEAN_EXPORT uint8_t l_Lake_VerRange_test(lean_object* v_self_3236_, lean_object* v_ver_3237_){
_start:
{
lean_object* v_clauses_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v_clauses_3238_ = lean_ctor_get(v_self_3236_, 1);
v___x_3239_ = lean_unsigned_to_nat(0u);
v___x_3240_ = lean_array_get_size(v_clauses_3238_);
v___x_3241_ = lean_nat_dec_lt(v___x_3239_, v___x_3240_);
if (v___x_3241_ == 0)
{
return v___x_3241_;
}
else
{
if (v___x_3241_ == 0)
{
return v___x_3241_;
}
else
{
size_t v___x_3242_; size_t v___x_3243_; uint8_t v___x_3244_; 
v___x_3242_ = ((size_t)0ULL);
v___x_3243_ = lean_usize_of_nat(v___x_3240_);
v___x_3244_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3237_, v_clauses_3238_, v___x_3242_, v___x_3243_);
return v___x_3244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_test___boxed(lean_object* v_self_3245_, lean_object* v_ver_3246_){
_start:
{
uint8_t v_res_3247_; lean_object* v_r_3248_; 
v_res_3247_ = l_Lake_VerRange_test(v_self_3245_, v_ver_3246_);
lean_dec_ref(v_ver_3246_);
lean_dec_ref(v_self_3245_);
v_r_3248_ = lean_box(v_res_3247_);
return v_r_3248_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Date(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Trie(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Trie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_SemVerCore_instLT = _init_l_Lake_SemVerCore_instLT();
lean_mark_persistent(l_Lake_SemVerCore_instLT);
l_Lake_SemVerCore_instLE = _init_l_Lake_SemVerCore_instLE();
lean_mark_persistent(l_Lake_SemVerCore_instLE);
l_Lake_StdVer_instLT = _init_l_Lake_StdVer_instLT();
lean_mark_persistent(l_Lake_StdVer_instLT);
l_Lake_StdVer_instLE = _init_l_Lake_StdVer_instLE();
lean_mark_persistent(l_Lake_StdVer_instLE);
l_Lake_ToolchainVer_instLT = _init_l_Lake_ToolchainVer_instLT();
lean_mark_persistent(l_Lake_ToolchainVer_instLT);
l_Lake_ToolchainVer_instLE = _init_l_Lake_ToolchainVer_instLE();
lean_mark_persistent(l_Lake_ToolchainVer_instLE);
l_Lake_instInhabitedComparatorOp_default = _init_l_Lake_instInhabitedComparatorOp_default();
l_Lake_instInhabitedComparatorOp = _init_l_Lake_instInhabitedComparatorOp();
l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie = _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie();
lean_mark_persistent(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Version(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Lake_Util_Date(uint8_t builtin);
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Lean_Data_Trie(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Version(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Trie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Version(builtin);
}
#ifdef __cplusplus
}
#endif
