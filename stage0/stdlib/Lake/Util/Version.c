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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx___boxed(lean_object*);
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
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = lean_string_utf8_byte_size(v_s_1_);
v___x_9_ = lean_nat_dec_eq(v_p_4_, v___x_8_);
if (v___x_9_ == 0)
{
uint32_t v_c_10_; uint8_t v___y_12_; uint8_t v___y_19_; uint32_t v___x_29_; uint8_t v___x_30_; 
v_c_10_ = lean_string_utf8_get_fast(v_s_1_, v_p_4_);
v___x_29_ = 46;
v___x_30_ = lean_uint32_dec_eq(v_c_10_, v___x_29_);
if (v___x_30_ == 0)
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 65;
v___x_32_ = lean_uint32_dec_le(v___x_31_, v_c_10_);
if (v___x_32_ == 0)
{
goto v___jp_24_;
}
else
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 90;
v___x_34_ = lean_uint32_dec_le(v_c_10_, v___x_33_);
if (v___x_34_ == 0)
{
goto v___jp_24_;
}
else
{
goto v___jp_5_;
}
}
}
else
{
lean_object* v_c_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_inc(v_p_4_);
lean_inc_ref(v_s_1_);
v_c_35_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_35_, 0, v_s_1_);
lean_ctor_set(v_c_35_, 1, v_iniPos_3_);
lean_ctor_set(v_c_35_, 2, v_p_4_);
v___x_36_ = lean_array_push(v_cs_2_, v_c_35_);
v___x_37_ = lean_string_utf8_next_fast(v_s_1_, v_p_4_);
lean_dec(v_p_4_);
v_cs_2_ = v___x_36_;
v_iniPos_3_ = v___x_37_;
v_p_4_ = v___x_37_;
goto _start;
}
v___jp_11_:
{
if (v___y_12_ == 0)
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 42;
v___x_14_ = lean_uint32_dec_eq(v_c_10_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v_c_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
lean_inc(v_p_4_);
v_c_15_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_15_, 0, v_s_1_);
lean_ctor_set(v_c_15_, 1, v_iniPos_3_);
lean_ctor_set(v_c_15_, 2, v_p_4_);
v___x_16_ = lean_array_push(v_cs_2_, v_c_15_);
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_p_4_);
return v___x_17_;
}
else
{
goto v___jp_5_;
}
}
else
{
goto v___jp_5_;
}
}
v___jp_18_:
{
if (v___y_19_ == 0)
{
uint32_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = 48;
v___x_21_ = lean_uint32_dec_le(v___x_20_, v_c_10_);
if (v___x_21_ == 0)
{
v___y_12_ = v___x_21_;
goto v___jp_11_;
}
else
{
uint32_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 57;
v___x_23_ = lean_uint32_dec_le(v_c_10_, v___x_22_);
v___y_12_ = v___x_23_;
goto v___jp_11_;
}
}
else
{
goto v___jp_5_;
}
}
v___jp_24_:
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 97;
v___x_26_ = lean_uint32_dec_le(v___x_25_, v_c_10_);
if (v___x_26_ == 0)
{
v___y_19_ = v___x_26_;
goto v___jp_18_;
}
else
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 122;
v___x_28_ = lean_uint32_dec_le(v_c_10_, v___x_27_);
v___y_19_ = v___x_28_;
goto v___jp_18_;
}
}
}
else
{
lean_object* v_c_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
lean_inc(v_p_4_);
v_c_39_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_39_, 0, v_s_1_);
lean_ctor_set(v_c_39_, 1, v_iniPos_3_);
lean_ctor_set(v_c_39_, 2, v_p_4_);
v___x_40_ = lean_array_push(v_cs_2_, v_c_39_);
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
lean_ctor_set(v___x_41_, 1, v_p_4_);
return v___x_41_;
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents_go(lean_object* v_s_42_, lean_object* v_cs_43_, lean_object* v_iniPos_44_, lean_object* v_p_45_, lean_object* v_iniPos__le_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_42_, v_cs_43_, v_iniPos_44_, v_p_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents(lean_object* v_s_50_, lean_object* v_p_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_p_51_);
v___x_53_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_50_, v___x_52_, v_p_51_, v_p_51_);
return v___x_53_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Util_Version_0__Lake_isWildVer(lean_object* v_s_54_){
_start:
{
lean_object* v_str_55_; lean_object* v_startInclusive_56_; lean_object* v_endExclusive_57_; lean_object* v_p_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v_str_55_ = lean_ctor_get(v_s_54_, 0);
v_startInclusive_56_ = lean_ctor_get(v_s_54_, 1);
v_endExclusive_57_ = lean_ctor_get(v_s_54_, 2);
v_p_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_nat_sub(v_endExclusive_57_, v_startInclusive_56_);
v___x_60_ = lean_nat_dec_eq(v_p_58_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_61_ = lean_string_utf8_next_fast(v_str_55_, v_startInclusive_56_);
v___x_62_ = lean_nat_sub(v___x_61_, v_startInclusive_56_);
v___x_63_ = lean_nat_dec_eq(v___x_62_, v___x_59_);
lean_dec(v___x_59_);
lean_dec(v___x_62_);
if (v___x_63_ == 0)
{
return v___x_63_;
}
else
{
uint32_t v_c_64_; uint8_t v___y_66_; uint32_t v___x_69_; uint8_t v___x_70_; 
v_c_64_ = lean_string_utf8_get_fast(v_str_55_, v_startInclusive_56_);
v___x_69_ = 120;
v___x_70_ = lean_uint32_dec_eq(v_c_64_, v___x_69_);
if (v___x_70_ == 0)
{
uint32_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = 88;
v___x_72_ = lean_uint32_dec_eq(v_c_64_, v___x_71_);
v___y_66_ = v___x_72_;
goto v___jp_65_;
}
else
{
v___y_66_ = v___x_70_;
goto v___jp_65_;
}
v___jp_65_:
{
if (v___y_66_ == 0)
{
uint32_t v___x_67_; uint8_t v___x_68_; 
v___x_67_ = 42;
v___x_68_ = lean_uint32_dec_eq(v_c_64_, v___x_67_);
return v___x_68_;
}
else
{
return v___y_66_;
}
}
}
}
else
{
uint8_t v___x_73_; 
lean_dec(v___x_59_);
v___x_73_ = 0;
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_isWildVer___boxed(lean_object* v_s_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l___private_Lake_Util_Version_0__Lake_isWildVer(v_s_74_);
lean_dec_ref(v_s_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg(lean_object* v_what_80_, lean_object* v_s_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_String_Slice_toNat_x3f(v_s_81_);
if (lean_obj_tag(v___x_83_) == 1)
{
lean_object* v_val_84_; lean_object* v___x_85_; 
v_val_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_val_84_);
lean_dec_ref_known(v___x_83_, 1);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v_val_84_);
lean_ctor_set(v___x_85_, 1, v_a_82_);
return v___x_85_;
}
else
{
lean_object* v_str_86_; lean_object* v_startInclusive_87_; lean_object* v_endExclusive_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v___x_83_);
v_str_86_ = lean_ctor_get(v_s_81_, 0);
v_startInclusive_87_ = lean_ctor_get(v_s_81_, 1);
v_endExclusive_88_ = lean_ctor_get(v_s_81_, 2);
v___x_89_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0));
v___x_90_ = lean_string_append(v___x_89_, v_what_80_);
v___x_91_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1));
v___x_92_ = lean_string_append(v___x_90_, v___x_91_);
v___x_93_ = lean_string_utf8_extract(v_str_86_, v_startInclusive_87_, v_endExclusive_88_);
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
lean_dec_ref(v___x_93_);
v___x_95_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_96_ = lean_string_append(v___x_94_, v___x_95_);
v___x_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_a_82_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___boxed(lean_object* v_what_98_, lean_object* v_s_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg(v_what_98_, v_s_99_, v_a_100_);
lean_dec_ref(v_s_99_);
lean_dec_ref(v_what_98_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat(lean_object* v_00_u03c3_102_, lean_object* v_what_103_, lean_object* v_s_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_String_Slice_toNat_x3f(v_s_104_);
if (lean_obj_tag(v___x_106_) == 1)
{
lean_object* v_val_107_; lean_object* v___x_108_; 
v_val_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v___x_106_, 1);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_val_107_);
lean_ctor_set(v___x_108_, 1, v_a_105_);
return v___x_108_;
}
else
{
lean_object* v_str_109_; lean_object* v_startInclusive_110_; lean_object* v_endExclusive_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v___x_106_);
v_str_109_ = lean_ctor_get(v_s_104_, 0);
v_startInclusive_110_ = lean_ctor_get(v_s_104_, 1);
v_endExclusive_111_ = lean_ctor_get(v_s_104_, 2);
v___x_112_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0));
v___x_113_ = lean_string_append(v___x_112_, v_what_103_);
v___x_114_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1));
v___x_115_ = lean_string_append(v___x_113_, v___x_114_);
v___x_116_ = lean_string_utf8_extract(v_str_109_, v_startInclusive_110_, v_endExclusive_111_);
v___x_117_ = lean_string_append(v___x_115_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_118_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_119_ = lean_string_append(v___x_117_, v___x_118_);
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v_a_105_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___boxed(lean_object* v_00_u03c3_121_, lean_object* v_what_122_, lean_object* v_s_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lake_Util_Version_0__Lake_parseVerNat(v_00_u03c3_121_, v_what_122_, v_s_123_, v_a_124_);
lean_dec_ref(v_s_123_);
lean_dec_ref(v_what_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx(lean_object* v_x_126_){
_start:
{
switch(lean_obj_tag(v_x_126_))
{
case 0:
{
lean_object* v___x_127_; 
v___x_127_ = lean_unsigned_to_nat(0u);
return v___x_127_;
}
case 1:
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(1u);
return v___x_128_;
}
default: 
{
lean_object* v___x_129_; 
v___x_129_ = lean_unsigned_to_nat(2u);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___boxed(lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx(v_x_130_);
lean_dec(v_x_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(lean_object* v_t_132_, lean_object* v_k_133_){
_start:
{
if (lean_obj_tag(v_t_132_) == 2)
{
lean_object* v_n_134_; lean_object* v___x_135_; 
v_n_134_ = lean_ctor_get(v_t_132_, 0);
lean_inc(v_n_134_);
lean_dec_ref_known(v_t_132_, 1);
v___x_135_ = lean_apply_1(v_k_133_, v_n_134_);
return v___x_135_;
}
else
{
lean_dec(v_t_132_);
return v_k_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(lean_object* v_motive_136_, lean_object* v_ctorIdx_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_k_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_138_, v_k_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___boxed(lean_object* v_motive_142_, lean_object* v_ctorIdx_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_k_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(v_motive_142_, v_ctorIdx_143_, v_t_144_, v_h_145_, v_k_146_);
lean_dec(v_ctorIdx_143_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim___redArg(lean_object* v_t_148_, lean_object* v_none_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_148_, v_none_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim(lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_none_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_152_, v_none_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim___redArg(lean_object* v_t_156_, lean_object* v_wild_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_156_, v_wild_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim(lean_object* v_motive_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_wild_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_160_, v_wild_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim___redArg(lean_object* v_t_164_, lean_object* v_nat_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_164_, v_nat_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim(lean_object* v_motive_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_nat_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_168_, v_nat_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(lean_object* v_what_173_, lean_object* v_s_x3f_174_, lean_object* v_a_175_){
_start:
{
if (lean_obj_tag(v_s_x3f_174_) == 1)
{
lean_object* v_val_176_; uint8_t v___x_177_; 
v_val_176_ = lean_ctor_get(v_s_x3f_174_, 0);
v___x_177_ = l___private_Lake_Util_Version_0__Lake_isWildVer(v_val_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = l_String_Slice_toNat_x3f(v_val_176_);
if (lean_obj_tag(v___x_178_) == 1)
{
lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
v_val_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_187_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 2);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_val_179_);
v___x_184_ = v_reuseFailAlloc_186_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_a_175_);
return v___x_185_;
}
}
}
else
{
lean_object* v_str_188_; lean_object* v_startInclusive_189_; lean_object* v_endExclusive_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v___x_178_);
v_str_188_ = lean_ctor_get(v_val_176_, 0);
v_startInclusive_189_ = lean_ctor_get(v_val_176_, 1);
v_endExclusive_190_ = lean_ctor_get(v_val_176_, 2);
v___x_191_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0));
v___x_192_ = lean_string_append(v___x_191_, v_what_173_);
v___x_193_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0));
v___x_194_ = lean_string_append(v___x_192_, v___x_193_);
v___x_195_ = lean_string_utf8_extract(v_str_188_, v_startInclusive_189_, v_endExclusive_190_);
v___x_196_ = lean_string_append(v___x_194_, v___x_195_);
lean_dec_ref(v___x_195_);
v___x_197_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_198_ = lean_string_append(v___x_196_, v___x_197_);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_a_175_);
return v___x_199_;
}
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_box(1);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_a_175_);
return v___x_201_;
}
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_box(0);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_a_175_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___boxed(lean_object* v_what_204_, lean_object* v_s_x3f_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v_what_204_, v_s_x3f_205_, v_a_206_);
lean_dec(v_s_x3f_205_);
lean_dec_ref(v_what_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent(lean_object* v_00_u03c3_208_, lean_object* v_what_209_, lean_object* v_s_x3f_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v_what_209_, v_s_x3f_210_, v_a_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___boxed(lean_object* v_00_u03c3_213_, lean_object* v_what_214_, lean_object* v_s_x3f_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent(v_00_u03c3_213_, v_what_214_, v_s_x3f_215_, v_a_216_);
lean_dec(v_s_x3f_215_);
lean_dec_ref(v_what_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(lean_object* v_s_218_, lean_object* v_p_219_){
_start:
{
uint8_t v___y_221_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = lean_string_utf8_byte_size(v_s_218_);
v___x_225_ = lean_nat_dec_eq(v_p_219_, v___x_224_);
if (v___x_225_ == 0)
{
uint32_t v___x_226_; uint8_t v___y_228_; uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_226_ = lean_string_utf8_get_fast(v_s_218_, v_p_219_);
v___x_233_ = 32;
v___x_234_ = lean_uint32_dec_eq(v___x_226_, v___x_233_);
if (v___x_234_ == 0)
{
uint32_t v___x_235_; uint8_t v___x_236_; 
v___x_235_ = 9;
v___x_236_ = lean_uint32_dec_eq(v___x_226_, v___x_235_);
v___y_228_ = v___x_236_;
goto v___jp_227_;
}
else
{
v___y_228_ = v___x_234_;
goto v___jp_227_;
}
v___jp_227_:
{
if (v___y_228_ == 0)
{
uint32_t v___x_229_; uint8_t v___x_230_; 
v___x_229_ = 13;
v___x_230_ = lean_uint32_dec_eq(v___x_226_, v___x_229_);
if (v___x_230_ == 0)
{
uint32_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 10;
v___x_232_ = lean_uint32_dec_eq(v___x_226_, v___x_231_);
v___y_221_ = v___x_232_;
goto v___jp_220_;
}
else
{
v___y_221_ = v___x_230_;
goto v___jp_220_;
}
}
else
{
return v_p_219_;
}
}
}
else
{
return v_p_219_;
}
v___jp_220_:
{
if (v___y_221_ == 0)
{
lean_object* v___x_222_; 
v___x_222_ = lean_string_utf8_next_fast(v_s_218_, v_p_219_);
lean_dec(v_p_219_);
v_p_219_ = v___x_222_;
goto _start;
}
else
{
return v_p_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace___boxed(lean_object* v_s_237_, lean_object* v_p_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(v_s_237_, v_p_238_);
lean_dec_ref(v_s_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(lean_object* v_s_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_string_utf8_byte_size(v_s_240_);
v___x_243_ = lean_nat_dec_eq(v_a_241_, v___x_242_);
if (v___x_243_ == 0)
{
uint32_t v___x_244_; uint32_t v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_string_utf8_get_fast(v_s_240_, v_a_241_);
v___x_245_ = 45;
v___x_246_ = lean_uint32_dec_eq(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_a_241_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_249_ = lean_string_utf8_next_fast(v_s_240_, v_a_241_);
lean_dec(v_a_241_);
v___x_250_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(v_s_240_, v___x_249_);
v___x_251_ = lean_string_utf8_extract(v_s_240_, v___x_249_, v___x_250_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_250_);
return v___x_253_;
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_a_241_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f___boxed(lean_object* v_s_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_256_, v_a_257_);
lean_dec_ref(v_s_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(lean_object* v_s_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_263_; lean_object* v_a_264_; 
v___x_263_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_261_, v_a_262_);
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
if (lean_obj_tag(v_a_264_) == 1)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_280_; 
v_a_265_ = lean_ctor_get(v___x_263_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_281_);
v___x_267_ = v___x_263_;
v_isShared_268_ = v_isSharedCheck_280_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_263_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_280_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v_val_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_val_269_ = lean_ctor_get(v_a_264_, 0);
lean_inc(v_val_269_);
lean_dec_ref_known(v_a_264_, 1);
v___x_270_ = lean_string_utf8_byte_size(v_val_269_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_nat_dec_eq(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_274_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v_val_269_);
v___x_274_ = v___x_267_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_val_269_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_a_265_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
lean_object* v___x_276_; lean_object* v___x_278_; 
lean_dec(v_val_269_);
v___x_276_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0));
if (v_isShared_268_ == 0)
{
lean_ctor_set_tag(v___x_267_, 1);
lean_ctor_set(v___x_267_, 0, v___x_276_);
v___x_278_ = v___x_267_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_a_265_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_290_; 
lean_dec(v_a_264_);
v_a_282_ = lean_ctor_get(v___x_263_, 1);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; 
v_unused_291_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_291_);
v___x_284_ = v___x_263_;
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_263_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_286_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_a_282_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___boxed(lean_object* v_s_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_292_, v_a_293_);
lean_dec_ref(v_s_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(lean_object* v_s_296_, lean_object* v_x_297_, lean_object* v_startPos_298_, lean_object* v_endPos_299_){
_start:
{
lean_object* v___x_300_; 
lean_inc_ref(v_s_296_);
v___x_300_ = lean_apply_2(v_x_297_, v_s_296_, v_startPos_298_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_a_302_; uint8_t v___x_303_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
v_a_302_ = lean_ctor_get(v___x_300_, 1);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_300_, 2);
v___x_303_ = lean_nat_dec_eq(v_a_302_, v_endPos_299_);
if (v___x_303_ == 0)
{
lean_object* v_tail_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_a_301_);
v_tail_304_ = lean_string_utf8_extract(v_s_296_, v_a_302_, v_endPos_299_);
lean_dec(v_a_302_);
lean_dec_ref(v_s_296_);
v___x_305_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_306_ = lean_string_append(v___x_305_, v_tail_304_);
lean_dec_ref(v_tail_304_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; 
lean_dec(v_a_302_);
lean_dec_ref(v_s_296_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v_a_301_);
return v___x_308_;
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_310_; 
lean_dec_ref(v_s_296_);
v_a_309_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_300_, 2);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v_a_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___boxed(lean_object* v_s_311_, lean_object* v_x_312_, lean_object* v_startPos_313_, lean_object* v_endPos_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_311_, v_x_312_, v_startPos_313_, v_endPos_314_);
lean_dec(v_endPos_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object* v_00_u03b1_316_, lean_object* v_s_317_, lean_object* v_x_318_, lean_object* v_startPos_319_, lean_object* v_endPos_320_){
_start:
{
lean_object* v___x_321_; 
lean_inc_ref(v_s_317_);
v___x_321_ = lean_apply_2(v_x_318_, v_s_317_, v_startPos_319_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v_a_323_; uint8_t v___x_324_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
v_a_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_321_, 2);
v___x_324_ = lean_nat_dec_eq(v_a_323_, v_endPos_320_);
if (v___x_324_ == 0)
{
lean_object* v_tail_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_a_322_);
v_tail_325_ = lean_string_utf8_extract(v_s_317_, v_a_323_, v_endPos_320_);
lean_dec(v_a_323_);
lean_dec_ref(v_s_317_);
v___x_326_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_327_ = lean_string_append(v___x_326_, v_tail_325_);
lean_dec_ref(v_tail_325_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; 
lean_dec(v_a_323_);
lean_dec_ref(v_s_317_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_a_322_);
return v___x_329_;
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_331_; 
lean_dec_ref(v_s_317_);
v_a_330_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_321_, 2);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_a_330_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___boxed(lean_object* v_00_u03b1_332_, lean_object* v_s_333_, lean_object* v_x_334_, lean_object* v_startPos_335_, lean_object* v_endPos_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lake_Util_Version_0__Lake_runVerParse(v_00_u03b1_332_, v_s_333_, v_x_334_, v_startPos_335_, v_endPos_336_);
lean_dec(v_endPos_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprSemVerCore_repr_spec__0(lean_object* v_a_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_nat_to_int(v_a_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(9u);
v___x_358_ = lean_nat_to_int(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__0));
v___x_370_ = lean_string_length(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__15, &l_Lake_instReprSemVerCore_repr___redArg___closed__15_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15);
v___x_372_ = lean_nat_to_int(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___redArg(lean_object* v_x_377_){
_start:
{
lean_object* v_major_378_; lean_object* v_minor_379_; lean_object* v_patch_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_major_378_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_major_378_);
v_minor_379_ = lean_ctor_get(v_x_377_, 1);
lean_inc(v_minor_379_);
v_patch_380_ = lean_ctor_get(v_x_377_, 2);
lean_inc(v_patch_380_);
lean_dec_ref(v_x_377_);
v___x_381_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_382_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__6));
v___x_383_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__7, &l_Lake_instReprSemVerCore_repr___redArg___closed__7_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7);
v___x_384_ = l_Nat_reprFast(v_major_378_);
v___x_385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
v___x_386_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_383_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = 0;
v___x_388_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*1, v___x_387_);
v___x_389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_382_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_box(1);
v___x_393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_391_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__11));
v___x_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_381_);
v___x_397_ = l_Nat_reprFast(v_minor_379_);
v___x_398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_383_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*1, v___x_387_);
v___x_401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_396_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_390_);
v___x_403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_392_);
v___x_404_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__13));
v___x_405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_381_);
v___x_407_ = l_Nat_reprFast(v_patch_380_);
v___x_408_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
v___x_409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_383_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*1, v___x_387_);
v___x_411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_406_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_413_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_411_);
v___x_415_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_412_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*1, v___x_387_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr(lean_object* v_x_419_, lean_object* v_prec_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lake_instReprSemVerCore_repr___redArg(v_x_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___boxed(lean_object* v_x_422_, lean_object* v_prec_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lake_instReprSemVerCore_repr(v_x_422_, v_prec_423_);
lean_dec(v_prec_423_);
return v_res_424_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore_decEq(lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
lean_object* v_major_429_; lean_object* v_minor_430_; lean_object* v_patch_431_; lean_object* v_major_432_; lean_object* v_minor_433_; lean_object* v_patch_434_; uint8_t v___x_435_; 
v_major_429_ = lean_ctor_get(v_x_427_, 0);
v_minor_430_ = lean_ctor_get(v_x_427_, 1);
v_patch_431_ = lean_ctor_get(v_x_427_, 2);
v_major_432_ = lean_ctor_get(v_x_428_, 0);
v_minor_433_ = lean_ctor_get(v_x_428_, 1);
v_patch_434_ = lean_ctor_get(v_x_428_, 2);
v___x_435_ = lean_nat_dec_eq(v_major_429_, v_major_432_);
if (v___x_435_ == 0)
{
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = lean_nat_dec_eq(v_minor_430_, v_minor_433_);
if (v___x_436_ == 0)
{
return v___x_436_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = lean_nat_dec_eq(v_patch_431_, v_patch_434_);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore_decEq___boxed(lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_438_, v_x_439_);
lean_dec_ref(v_x_439_);
lean_dec_ref(v_x_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore(lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_442_, v_x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore___boxed(lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Lake_instDecidableEqSemVerCore(v_x_445_, v_x_446_);
lean_dec_ref(v_x_446_);
lean_dec_ref(v_x_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdSemVerCore_ord(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_major_451_; lean_object* v_minor_452_; lean_object* v_patch_453_; lean_object* v_major_454_; lean_object* v_minor_455_; lean_object* v_patch_456_; uint8_t v___x_457_; 
v_major_451_ = lean_ctor_get(v_x_449_, 0);
v_minor_452_ = lean_ctor_get(v_x_449_, 1);
v_patch_453_ = lean_ctor_get(v_x_449_, 2);
v_major_454_ = lean_ctor_get(v_x_450_, 0);
v_minor_455_ = lean_ctor_get(v_x_450_, 1);
v_patch_456_ = lean_ctor_get(v_x_450_, 2);
v___x_457_ = lean_nat_dec_lt(v_major_451_, v_major_454_);
if (v___x_457_ == 0)
{
uint8_t v___x_458_; 
v___x_458_ = lean_nat_dec_eq(v_major_451_, v_major_454_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; 
v___x_459_ = 2;
return v___x_459_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = lean_nat_dec_lt(v_minor_452_, v_minor_455_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; 
v___x_461_ = lean_nat_dec_eq(v_minor_452_, v_minor_455_);
if (v___x_461_ == 0)
{
uint8_t v___x_462_; 
v___x_462_ = 2;
return v___x_462_;
}
else
{
uint8_t v___x_463_; 
v___x_463_ = lean_nat_dec_lt(v_patch_453_, v_patch_456_);
if (v___x_463_ == 0)
{
uint8_t v___x_464_; 
v___x_464_ = lean_nat_dec_eq(v_patch_453_, v_patch_456_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
v___x_465_ = 2;
return v___x_465_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = 1;
return v___x_466_;
}
}
else
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
}
}
else
{
uint8_t v___x_468_; 
v___x_468_ = 0;
return v___x_468_;
}
}
}
else
{
uint8_t v___x_469_; 
v___x_469_ = 0;
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdSemVerCore_ord___boxed(lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Lake_instOrdSemVerCore_ord(v_x_470_, v_x_471_);
lean_dec_ref(v_x_471_);
lean_dec_ref(v_x_470_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
static lean_object* _init_l_Lake_SemVerCore_instLT(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_box(0);
return v___x_476_;
}
}
static lean_object* _init_l_Lake_SemVerCore_instLE(void){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = lean_box(0);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0(lean_object* v_x_478_, lean_object* v_y_479_){
_start:
{
uint8_t v___x_480_; 
v___x_480_ = l_Lake_instOrdSemVerCore_ord(v_x_478_, v_y_479_);
if (v___x_480_ == 2)
{
lean_inc_ref(v_y_479_);
return v_y_479_;
}
else
{
lean_inc_ref(v_x_478_);
return v_x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0___boxed(lean_object* v_x_481_, lean_object* v_y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lake_SemVerCore_instMin___lam__0(v_x_481_, v_y_482_);
lean_dec_ref(v_y_482_);
lean_dec_ref(v_x_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0(lean_object* v_x_486_, lean_object* v_y_487_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = l_Lake_instOrdSemVerCore_ord(v_x_486_, v_y_487_);
if (v___x_488_ == 2)
{
lean_inc_ref(v_x_486_);
return v_x_486_;
}
else
{
lean_inc_ref(v_y_487_);
return v_y_487_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0___boxed(lean_object* v_x_489_, lean_object* v_y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lake_SemVerCore_instMax___lam__0(v_x_489_, v_y_490_);
lean_dec_ref(v_y_490_);
lean_dec_ref(v_x_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(lean_object* v_s_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_a_503_; lean_object* v_a_504_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_a_511_; lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_563_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_501_);
v___x_510_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_500_, v___x_509_, v_a_501_, v_a_501_);
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_a_512_ = lean_ctor_get(v___x_510_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_563_ == 0)
{
v___x_514_ = v___x_510_;
v_isShared_515_ = v_isSharedCheck_563_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_563_;
goto v_resetjp_513_;
}
v___jp_502_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0));
v___x_506_ = lean_string_append(v___x_505_, v_a_503_);
lean_dec_ref(v_a_503_);
v___x_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_a_504_);
return v___x_507_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_516_ = lean_array_get_size(v_a_511_);
v___x_517_ = lean_unsigned_to_nat(3u);
v___x_518_ = lean_nat_dec_eq(v___x_516_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_del_object(v___x_514_);
lean_dec(v_a_511_);
v___x_519_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1));
v___x_520_ = l_Nat_reprFast(v___x_516_);
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
lean_dec_ref(v___x_520_);
v___x_522_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2));
v___x_523_ = lean_string_append(v___x_521_, v___x_522_);
v_a_503_ = v___x_523_;
v_a_504_ = v_a_512_;
goto v___jp_502_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_array_fget_borrowed(v_a_511_, v___x_508_);
v___x_525_ = l_String_Slice_toNat_x3f(v___x_524_);
if (lean_obj_tag(v___x_525_) == 1)
{
lean_object* v_val_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_val_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_val_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_array_fget_borrowed(v_a_511_, v___x_527_);
v___x_529_ = l_String_Slice_toNat_x3f(v___x_528_);
if (lean_obj_tag(v___x_529_) == 1)
{
lean_object* v_val_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_val_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_val_530_);
lean_dec_ref_known(v___x_529_, 1);
v___x_531_ = lean_unsigned_to_nat(2u);
v___x_532_ = lean_array_fget(v_a_511_, v___x_531_);
lean_dec(v_a_511_);
v___x_533_ = l_String_Slice_toNat_x3f(v___x_532_);
if (lean_obj_tag(v___x_533_) == 1)
{
lean_object* v_val_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
lean_dec(v___x_532_);
v_val_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_val_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_535_, 0, v_val_526_);
lean_ctor_set(v___x_535_, 1, v_val_530_);
lean_ctor_set(v___x_535_, 2, v_val_534_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_535_);
v___x_537_ = v___x_514_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_a_512_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
else
{
lean_object* v_str_539_; lean_object* v_startInclusive_540_; lean_object* v_endExclusive_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v___x_533_);
lean_dec(v_val_530_);
lean_dec(v_val_526_);
lean_del_object(v___x_514_);
v_str_539_ = lean_ctor_get(v___x_532_, 0);
lean_inc_ref(v_str_539_);
v_startInclusive_540_ = lean_ctor_get(v___x_532_, 1);
lean_inc(v_startInclusive_540_);
v_endExclusive_541_ = lean_ctor_get(v___x_532_, 2);
lean_inc(v_endExclusive_541_);
lean_dec(v___x_532_);
v___x_542_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_543_ = lean_string_utf8_extract(v_str_539_, v_startInclusive_540_, v_endExclusive_541_);
lean_dec(v_endExclusive_541_);
lean_dec(v_startInclusive_540_);
lean_dec_ref(v_str_539_);
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
lean_dec_ref(v___x_543_);
v___x_545_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_546_ = lean_string_append(v___x_544_, v___x_545_);
v_a_503_ = v___x_546_;
v_a_504_ = v_a_512_;
goto v___jp_502_;
}
}
else
{
lean_object* v_str_547_; lean_object* v_startInclusive_548_; lean_object* v_endExclusive_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc(v___x_528_);
lean_dec(v___x_529_);
lean_dec(v_val_526_);
lean_del_object(v___x_514_);
lean_dec(v_a_511_);
v_str_547_ = lean_ctor_get(v___x_528_, 0);
lean_inc_ref(v_str_547_);
v_startInclusive_548_ = lean_ctor_get(v___x_528_, 1);
lean_inc(v_startInclusive_548_);
v_endExclusive_549_ = lean_ctor_get(v___x_528_, 2);
lean_inc(v_endExclusive_549_);
lean_dec(v___x_528_);
v___x_550_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_551_ = lean_string_utf8_extract(v_str_547_, v_startInclusive_548_, v_endExclusive_549_);
lean_dec(v_endExclusive_549_);
lean_dec(v_startInclusive_548_);
lean_dec_ref(v_str_547_);
v___x_552_ = lean_string_append(v___x_550_, v___x_551_);
lean_dec_ref(v___x_551_);
v___x_553_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
v_a_503_ = v___x_554_;
v_a_504_ = v_a_512_;
goto v___jp_502_;
}
}
else
{
lean_object* v_str_555_; lean_object* v_startInclusive_556_; lean_object* v_endExclusive_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_inc(v___x_524_);
lean_dec(v___x_525_);
lean_del_object(v___x_514_);
lean_dec(v_a_511_);
v_str_555_ = lean_ctor_get(v___x_524_, 0);
lean_inc_ref(v_str_555_);
v_startInclusive_556_ = lean_ctor_get(v___x_524_, 1);
lean_inc(v_startInclusive_556_);
v_endExclusive_557_ = lean_ctor_get(v___x_524_, 2);
lean_inc(v_endExclusive_557_);
lean_dec(v___x_524_);
v___x_558_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_559_ = lean_string_utf8_extract(v_str_555_, v_startInclusive_556_, v_endExclusive_557_);
lean_dec(v_endExclusive_557_);
lean_dec(v_startInclusive_556_);
lean_dec_ref(v_str_555_);
v___x_560_ = lean_string_append(v___x_558_, v___x_559_);
lean_dec_ref(v___x_559_);
v___x_561_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_562_ = lean_string_append(v___x_560_, v___x_561_);
v_a_503_ = v___x_562_;
v_a_504_ = v_a_512_;
goto v___jp_502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_parse(lean_object* v_s_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_string_utf8_byte_size(v_s_564_);
lean_inc_ref(v_s_564_);
v___x_567_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_564_, v___x_565_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v_a_569_; uint8_t v___x_570_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
v_a_569_ = lean_ctor_get(v___x_567_, 1);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_567_, 2);
v___x_570_ = lean_nat_dec_eq(v_a_569_, v___x_566_);
if (v___x_570_ == 0)
{
lean_object* v_tail_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v_a_568_);
v_tail_571_ = lean_string_utf8_extract(v_s_564_, v_a_569_, v___x_566_);
lean_dec(v_a_569_);
lean_dec_ref(v_s_564_);
v___x_572_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_573_ = lean_string_append(v___x_572_, v_tail_571_);
lean_dec_ref(v_tail_571_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; 
lean_dec(v_a_569_);
lean_dec_ref(v_s_564_);
v___x_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_575_, 0, v_a_568_);
return v___x_575_;
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_577_; 
lean_dec_ref(v_s_564_);
v_a_576_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_567_, 2);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v_a_576_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_toString(lean_object* v_ver_579_){
_start:
{
lean_object* v_major_580_; lean_object* v_minor_581_; lean_object* v_patch_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_major_580_ = lean_ctor_get(v_ver_579_, 0);
lean_inc(v_major_580_);
v_minor_581_ = lean_ctor_get(v_ver_579_, 1);
lean_inc(v_minor_581_);
v_patch_582_ = lean_ctor_get(v_ver_579_, 2);
lean_inc(v_patch_582_);
lean_dec_ref(v_ver_579_);
v___x_583_ = l_Nat_reprFast(v_major_580_);
v___x_584_ = ((lean_object*)(l_Lake_SemVerCore_toString___closed__0));
v___x_585_ = lean_string_append(v___x_583_, v___x_584_);
v___x_586_ = l_Nat_reprFast(v_minor_581_);
v___x_587_ = lean_string_append(v___x_585_, v___x_586_);
lean_dec_ref(v___x_586_);
v___x_588_ = lean_string_append(v___x_587_, v___x_584_);
v___x_589_ = l_Nat_reprFast(v_patch_582_);
v___x_590_ = lean_string_append(v___x_588_, v___x_589_);
lean_dec_ref(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instToJson___lam__0(lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_Lake_SemVerCore_toString(v_x_593_);
v___x_595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instFromJson___lam__0(lean_object* v_x_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Json_getStr_x3f(v_x_598_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_599_, 1);
v___x_609_ = l_Lake_SemVerCore_parse(v_a_608_);
return v___x_609_;
}
}
}
static lean_object* _init_l_Lake_instReprStdVer_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(16u);
v___x_627_ = lean_nat_to_int(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___redArg(lean_object* v_x_631_){
_start:
{
lean_object* v_toSemVerCore_632_; lean_object* v_specialDescr_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_666_; 
v_toSemVerCore_632_ = lean_ctor_get(v_x_631_, 0);
v_specialDescr_633_ = lean_ctor_get(v_x_631_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_631_);
if (v_isSharedCheck_666_ == 0)
{
v___x_635_ = v_x_631_;
v_isShared_636_ = v_isSharedCheck_666_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_specialDescr_633_);
lean_inc(v_toSemVerCore_632_);
lean_dec(v_x_631_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_666_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_637_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_638_ = ((lean_object*)(l_Lake_instReprStdVer_repr___redArg___closed__3));
v___x_639_ = lean_obj_once(&l_Lake_instReprStdVer_repr___redArg___closed__4, &l_Lake_instReprStdVer_repr___redArg___closed__4_once, _init_l_Lake_instReprStdVer_repr___redArg___closed__4);
v___x_640_ = l_Lake_instReprSemVerCore_repr___redArg(v_toSemVerCore_632_);
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 4);
lean_ctor_set(v___x_635_, 1, v___x_640_);
lean_ctor_set(v___x_635_, 0, v___x_639_);
v___x_642_ = v___x_635_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_665_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_643_ = 0;
v___x_644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*1, v___x_643_);
v___x_645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_638_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_box(1);
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = ((lean_object*)(l_Lake_instReprStdVer_repr___redArg___closed__6));
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_637_);
v___x_653_ = l_String_quote(v_specialDescr_633_);
v___x_654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
v___x_655_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_639_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*1, v___x_643_);
v___x_657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_652_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_659_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_657_);
v___x_661_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_658_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*1, v___x_643_);
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr(lean_object* v_x_667_, lean_object* v_prec_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lake_instReprStdVer_repr___redArg(v_x_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___boxed(lean_object* v_x_670_, lean_object* v_prec_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lake_instReprStdVer_repr(v_x_670_, v_prec_671_);
lean_dec(v_prec_671_);
return v_res_672_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer_decEq(lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v_toSemVerCore_677_; lean_object* v_specialDescr_678_; lean_object* v_toSemVerCore_679_; lean_object* v_specialDescr_680_; uint8_t v___x_681_; 
v_toSemVerCore_677_ = lean_ctor_get(v_x_675_, 0);
v_specialDescr_678_ = lean_ctor_get(v_x_675_, 1);
v_toSemVerCore_679_ = lean_ctor_get(v_x_676_, 0);
v_specialDescr_680_ = lean_ctor_get(v_x_676_, 1);
v___x_681_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_677_, v_toSemVerCore_679_);
if (v___x_681_ == 0)
{
return v___x_681_;
}
else
{
uint8_t v___x_682_; 
v___x_682_ = lean_string_dec_eq(v_specialDescr_678_, v_specialDescr_680_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer_decEq___boxed(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Lake_instDecidableEqStdVer_decEq(v_x_683_, v_x_684_);
lean_dec_ref(v_x_684_);
lean_dec_ref(v_x_683_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer(lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = l_Lake_instDecidableEqStdVer_decEq(v_x_687_, v_x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer___boxed(lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
uint8_t v_res_692_; lean_object* v_r_693_; 
v_res_692_ = l_Lake_instDecidableEqStdVer(v_x_690_, v_x_691_);
lean_dec_ref(v_x_691_);
lean_dec_ref(v_x_690_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0(lean_object* v_self_694_){
_start:
{
lean_object* v_toSemVerCore_695_; 
v_toSemVerCore_695_ = lean_ctor_get(v_self_694_, 0);
lean_inc_ref(v_toSemVerCore_695_);
return v_toSemVerCore_695_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed(lean_object* v_self_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lake_StdVer_instCoeSemVerCore___lam__0(v_self_696_);
lean_dec_ref(v_self_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_ofSemVerCore(lean_object* v_ver_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_ver_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT uint8_t l_Lake_StdVer_compare(lean_object* v_a_705_, lean_object* v_b_706_){
_start:
{
lean_object* v_toSemVerCore_707_; lean_object* v_specialDescr_708_; lean_object* v_toSemVerCore_709_; lean_object* v_specialDescr_710_; uint8_t v___x_711_; 
v_toSemVerCore_707_ = lean_ctor_get(v_a_705_, 0);
v_specialDescr_708_ = lean_ctor_get(v_a_705_, 1);
v_toSemVerCore_709_ = lean_ctor_get(v_b_706_, 0);
v_specialDescr_710_ = lean_ctor_get(v_b_706_, 1);
v___x_711_ = l_Lake_instOrdSemVerCore_ord(v_toSemVerCore_707_, v_toSemVerCore_709_);
if (v___x_711_ == 1)
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_713_ = lean_string_dec_eq(v_specialDescr_708_, v___x_712_);
if (v___x_713_ == 0)
{
uint8_t v___x_714_; 
v___x_714_ = lean_string_dec_eq(v_specialDescr_710_, v___x_712_);
if (v___x_714_ == 0)
{
uint8_t v___x_715_; 
v___x_715_ = lean_string_compare(v_specialDescr_708_, v_specialDescr_710_);
return v___x_715_;
}
else
{
uint8_t v___x_716_; 
v___x_716_ = 0;
return v___x_716_;
}
}
else
{
uint8_t v___x_717_; 
v___x_717_ = lean_string_dec_eq(v_specialDescr_710_, v___x_712_);
if (v___x_717_ == 0)
{
uint8_t v___x_718_; 
v___x_718_ = 2;
return v___x_718_;
}
else
{
return v___x_711_;
}
}
}
else
{
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_compare___boxed(lean_object* v_a_719_, lean_object* v_b_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lake_StdVer_compare(v_a_719_, v_b_720_);
lean_dec_ref(v_b_720_);
lean_dec_ref(v_a_719_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
static lean_object* _init_l_Lake_StdVer_instLT(void){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_box(0);
return v___x_725_;
}
}
static lean_object* _init_l_Lake_StdVer_instLE(void){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_box(0);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0(lean_object* v_x_727_, lean_object* v_y_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = l_Lake_StdVer_compare(v_x_727_, v_y_728_);
if (v___x_729_ == 2)
{
lean_inc_ref(v_y_728_);
return v_y_728_;
}
else
{
lean_inc_ref(v_x_727_);
return v_x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0___boxed(lean_object* v_x_730_, lean_object* v_y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lake_StdVer_instMin___lam__0(v_x_730_, v_y_731_);
lean_dec_ref(v_y_731_);
lean_dec_ref(v_x_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0(lean_object* v_x_735_, lean_object* v_y_736_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = l_Lake_StdVer_compare(v_x_735_, v_y_736_);
if (v___x_737_ == 2)
{
lean_inc_ref(v_x_735_);
return v_x_735_;
}
else
{
lean_inc_ref(v_y_736_);
return v_y_736_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0___boxed(lean_object* v_x_738_, lean_object* v_y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lake_StdVer_instMax___lam__0(v_x_738_, v_y_739_);
lean_dec_ref(v_y_739_);
lean_dec_ref(v_x_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parseM(lean_object* v_s_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_745_; 
lean_inc_ref(v_s_743_);
v___x_745_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_743_, v_a_744_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
v_a_747_ = lean_ctor_get(v___x_745_, 1);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_745_, 2);
v___x_748_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_743_, v_a_747_);
lean_dec_ref(v_s_743_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_a_750_ = lean_ctor_get(v___x_748_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_758_ == 0)
{
v___x_752_ = v___x_748_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_a_746_);
lean_ctor_set(v___x_754_, 1, v_a_749_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_a_750_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_a_746_);
v_a_759_ = lean_ctor_get(v___x_748_, 0);
v_a_760_ = lean_ctor_get(v___x_748_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_748_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_inc(v_a_759_);
lean_dec(v___x_748_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_759_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_s_743_);
v_a_768_ = lean_ctor_get(v___x_745_, 0);
v_a_769_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_745_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_inc(v_a_768_);
lean_dec(v___x_745_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_768_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parse(lean_object* v_s_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_string_utf8_byte_size(v_s_777_);
lean_inc_ref(v_s_777_);
v___x_780_ = l_Lake_StdVer_parseM(v_s_777_, v___x_778_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v_a_782_; uint8_t v___x_783_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
v_a_782_ = lean_ctor_get(v___x_780_, 1);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_780_, 2);
v___x_783_ = lean_nat_dec_eq(v_a_782_, v___x_779_);
if (v___x_783_ == 0)
{
lean_object* v_tail_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec(v_a_781_);
v_tail_784_ = lean_string_utf8_extract(v_s_777_, v_a_782_, v___x_779_);
lean_dec(v_a_782_);
lean_dec_ref(v_s_777_);
v___x_785_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_786_ = lean_string_append(v___x_785_, v_tail_784_);
lean_dec_ref(v_tail_784_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
else
{
lean_object* v___x_788_; 
lean_dec(v_a_782_);
lean_dec_ref(v_s_777_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_a_781_);
return v___x_788_;
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_790_; 
lean_dec_ref(v_s_777_);
v_a_789_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_780_, 2);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_a_789_);
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_toString(lean_object* v_ver_792_){
_start:
{
lean_object* v_toSemVerCore_793_; lean_object* v_specialDescr_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_toSemVerCore_793_ = lean_ctor_get(v_ver_792_, 0);
lean_inc_ref(v_toSemVerCore_793_);
v_specialDescr_794_ = lean_ctor_get(v_ver_792_, 1);
lean_inc_ref(v_specialDescr_794_);
lean_dec_ref(v_ver_792_);
v___x_795_ = lean_string_utf8_byte_size(v_specialDescr_794_);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_nat_dec_eq(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_798_ = l_Lake_SemVerCore_toString(v_toSemVerCore_793_);
v___x_799_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_800_ = lean_string_append(v___x_798_, v___x_799_);
v___x_801_ = lean_string_append(v___x_800_, v_specialDescr_794_);
lean_dec_ref(v_specialDescr_794_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; 
lean_dec_ref(v_specialDescr_794_);
v___x_802_ = l_Lake_SemVerCore_toString(v_toSemVerCore_793_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instToJson___lam__0(lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = l_Lake_StdVer_toString(v_x_805_);
v___x_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instFromJson___lam__0(lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Json_getStr_x3f(v_x_810_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_811_, 1);
v___x_821_ = l_Lake_StdVer_parse(v_a_820_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx(lean_object* v_x_830_){
_start:
{
switch(lean_obj_tag(v_x_830_))
{
case 0:
{
lean_object* v___x_831_; 
v___x_831_ = lean_unsigned_to_nat(0u);
return v___x_831_;
}
case 1:
{
lean_object* v___x_832_; 
v___x_832_ = lean_unsigned_to_nat(1u);
return v___x_832_;
}
case 2:
{
lean_object* v___x_833_; 
v___x_833_ = lean_unsigned_to_nat(2u);
return v___x_833_;
}
default: 
{
lean_object* v___x_834_; 
v___x_834_ = lean_unsigned_to_nat(3u);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___boxed(lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lake_ToolchainVer_ctorIdx(v_x_835_);
lean_dec_ref(v_x_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___redArg(lean_object* v_t_837_, lean_object* v_k_838_){
_start:
{
switch(lean_obj_tag(v_t_837_))
{
case 1:
{
lean_object* v_date_839_; lean_object* v_rev_840_; lean_object* v___x_841_; 
v_date_839_ = lean_ctor_get(v_t_837_, 0);
lean_inc_ref(v_date_839_);
v_rev_840_ = lean_ctor_get(v_t_837_, 1);
lean_inc(v_rev_840_);
lean_dec_ref_known(v_t_837_, 2);
v___x_841_ = lean_apply_2(v_k_838_, v_date_839_, v_rev_840_);
return v___x_841_;
}
case 2:
{
lean_object* v_n_842_; lean_object* v___x_843_; 
v_n_842_ = lean_ctor_get(v_t_837_, 0);
lean_inc(v_n_842_);
lean_dec_ref_known(v_t_837_, 1);
v___x_843_ = lean_apply_1(v_k_838_, v_n_842_);
return v___x_843_;
}
default: 
{
lean_object* v_ver_844_; lean_object* v___x_845_; 
v_ver_844_ = lean_ctor_get(v_t_837_, 0);
lean_inc_ref(v_ver_844_);
lean_dec_ref(v_t_837_);
v___x_845_ = lean_apply_1(v_k_838_, v_ver_844_);
return v___x_845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim(lean_object* v_motive_846_, lean_object* v_ctorIdx_847_, lean_object* v_t_848_, lean_object* v_h_849_, lean_object* v_k_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_848_, v_k_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___boxed(lean_object* v_motive_852_, lean_object* v_ctorIdx_853_, lean_object* v_t_854_, lean_object* v_h_855_, lean_object* v_k_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lake_ToolchainVer_ctorElim(v_motive_852_, v_ctorIdx_853_, v_t_854_, v_h_855_, v_k_856_);
lean_dec(v_ctorIdx_853_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim___redArg(lean_object* v_t_858_, lean_object* v_release_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_858_, v_release_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim(lean_object* v_motive_861_, lean_object* v_t_862_, lean_object* v_h_863_, lean_object* v_release_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_862_, v_release_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim___redArg(lean_object* v_t_866_, lean_object* v_nightly_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_866_, v_nightly_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim(lean_object* v_motive_869_, lean_object* v_t_870_, lean_object* v_h_871_, lean_object* v_nightly_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_870_, v_nightly_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim___redArg(lean_object* v_t_874_, lean_object* v_pr_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_874_, v_pr_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim(lean_object* v_motive_877_, lean_object* v_t_878_, lean_object* v_h_879_, lean_object* v_pr_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_878_, v_pr_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim___redArg(lean_object* v_t_882_, lean_object* v_other_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_882_, v_other_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim(lean_object* v_motive_885_, lean_object* v_t_886_, lean_object* v_h_887_, lean_object* v_other_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_886_, v_other_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override___redArg(lean_object* v_t_890_, lean_object* v_release_891_, lean_object* v_nightly_892_, lean_object* v_pr_893_, lean_object* v_other_894_){
_start:
{
switch(lean_obj_tag(v_t_890_))
{
case 0:
{
lean_object* v_ver_895_; lean_object* v___x_896_; 
lean_dec(v_other_894_);
lean_dec(v_pr_893_);
lean_dec(v_nightly_892_);
v_ver_895_ = lean_ctor_get(v_t_890_, 1);
lean_inc_ref(v_ver_895_);
lean_dec_ref_known(v_t_890_, 2);
v___x_896_ = lean_apply_1(v_release_891_, v_ver_895_);
return v___x_896_;
}
case 1:
{
lean_object* v_date_897_; lean_object* v_rev_898_; lean_object* v___x_899_; 
lean_dec(v_other_894_);
lean_dec(v_pr_893_);
lean_dec(v_release_891_);
v_date_897_ = lean_ctor_get(v_t_890_, 1);
lean_inc_ref(v_date_897_);
v_rev_898_ = lean_ctor_get(v_t_890_, 2);
lean_inc(v_rev_898_);
lean_dec_ref_known(v_t_890_, 3);
v___x_899_ = lean_apply_2(v_nightly_892_, v_date_897_, v_rev_898_);
return v___x_899_;
}
case 2:
{
lean_object* v_n_900_; lean_object* v___x_901_; 
lean_dec(v_other_894_);
lean_dec(v_nightly_892_);
lean_dec(v_release_891_);
v_n_900_ = lean_ctor_get(v_t_890_, 1);
lean_inc(v_n_900_);
lean_dec_ref_known(v_t_890_, 2);
v___x_901_ = lean_apply_1(v_pr_893_, v_n_900_);
return v___x_901_;
}
default: 
{
lean_object* v_v_902_; lean_object* v___x_903_; 
lean_dec(v_pr_893_);
lean_dec(v_nightly_892_);
lean_dec(v_release_891_);
v_v_902_ = lean_ctor_get(v_t_890_, 1);
lean_inc_ref(v_v_902_);
lean_dec_ref_known(v_t_890_, 2);
v___x_903_ = lean_apply_1(v_other_894_, v_v_902_);
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override(lean_object* v_motive_904_, lean_object* v_t_905_, lean_object* v_release_906_, lean_object* v_nightly_907_, lean_object* v_pr_908_, lean_object* v_other_909_){
_start:
{
switch(lean_obj_tag(v_t_905_))
{
case 0:
{
lean_object* v_ver_910_; lean_object* v___x_911_; 
lean_dec(v_other_909_);
lean_dec(v_pr_908_);
lean_dec(v_nightly_907_);
v_ver_910_ = lean_ctor_get(v_t_905_, 1);
lean_inc_ref(v_ver_910_);
lean_dec_ref_known(v_t_905_, 2);
v___x_911_ = lean_apply_1(v_release_906_, v_ver_910_);
return v___x_911_;
}
case 1:
{
lean_object* v_date_912_; lean_object* v_rev_913_; lean_object* v___x_914_; 
lean_dec(v_other_909_);
lean_dec(v_pr_908_);
lean_dec(v_release_906_);
v_date_912_ = lean_ctor_get(v_t_905_, 1);
lean_inc_ref(v_date_912_);
v_rev_913_ = lean_ctor_get(v_t_905_, 2);
lean_inc(v_rev_913_);
lean_dec_ref_known(v_t_905_, 3);
v___x_914_ = lean_apply_2(v_nightly_907_, v_date_912_, v_rev_913_);
return v___x_914_;
}
case 2:
{
lean_object* v_n_915_; lean_object* v___x_916_; 
lean_dec(v_other_909_);
lean_dec(v_nightly_907_);
lean_dec(v_release_906_);
v_n_915_ = lean_ctor_get(v_t_905_, 1);
lean_inc(v_n_915_);
lean_dec_ref_known(v_t_905_, 2);
v___x_916_ = lean_apply_1(v_pr_908_, v_n_915_);
return v___x_916_;
}
default: 
{
lean_object* v_v_917_; lean_object* v___x_918_; 
lean_dec(v_pr_908_);
lean_dec(v_nightly_907_);
lean_dec(v_release_906_);
v_v_917_ = lean_ctor_get(v_t_905_, 1);
lean_inc_ref(v_v_917_);
lean_dec_ref_known(v_t_905_, 2);
v___x_918_ = lean_apply_1(v_other_909_, v_v_917_);
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release___override(lean_object* v_ver_920_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_921_ = ((lean_object*)(l_Lake_ToolchainVer_release___override___closed__0));
lean_inc_ref(v_ver_920_);
v___x_922_ = l_Lake_StdVer_toString(v_ver_920_);
v___x_923_ = lean_string_append(v___x_921_, v___x_922_);
lean_dec_ref(v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v_ver_920_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly___override(lean_object* v_date_927_, lean_object* v_rev_928_){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___y_933_; 
v___x_929_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__0));
lean_inc_ref(v_date_927_);
v___x_930_ = l_Lake_Date_toString(v_date_927_);
v___x_931_ = lean_string_append(v___x_929_, v___x_930_);
lean_dec_ref(v___x_930_);
if (lean_obj_tag(v_rev_928_) == 0)
{
lean_object* v___x_936_; 
v___x_936_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___y_933_ = v___x_936_;
goto v___jp_932_;
}
else
{
lean_object* v_val_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_val_937_ = lean_ctor_get(v_rev_928_, 0);
v___x_938_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
lean_inc(v_val_937_);
v___x_939_ = l_Nat_reprFast(v_val_937_);
v___x_940_ = lean_string_append(v___x_938_, v___x_939_);
lean_dec_ref(v___x_939_);
v___y_933_ = v___x_940_;
goto v___jp_932_;
}
v___jp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_string_append(v___x_931_, v___y_933_);
lean_dec_ref(v___y_933_);
v___x_935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v_date_927_);
lean_ctor_set(v___x_935_, 2, v_rev_928_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr___override(lean_object* v_n_942_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_943_ = ((lean_object*)(l_Lake_ToolchainVer_pr___override___closed__0));
lean_inc(v_n_942_);
v___x_944_ = l_Nat_reprFast(v_n_942_);
v___x_945_ = lean_string_append(v___x_943_, v___x_944_);
lean_dec_ref(v___x_944_);
v___x_946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v_n_942_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other___override(lean_object* v_v_947_){
_start:
{
lean_object* v___x_948_; 
lean_inc_ref(v_v_947_);
v___x_948_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_948_, 0, v_v_947_);
lean_ctor_set(v___x_948_, 1, v_v_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override(lean_object* v_x_949_){
_start:
{
lean_object* v_toString_950_; 
v_toString_950_ = lean_ctor_get(v_x_949_, 0);
lean_inc_ref(v_toString_950_);
return v_toString_950_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override___boxed(lean_object* v_x_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lake_ToolchainVer_toString___override(v_x_951_);
lean_dec_ref(v_x_951_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
if (lean_obj_tag(v_x_959_) == 0)
{
lean_object* v___x_961_; 
v___x_961_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1));
return v___x_961_;
}
else
{
lean_object* v_val_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_973_; 
v_val_962_ = lean_ctor_get(v_x_959_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v_x_959_);
if (v_isSharedCheck_973_ == 0)
{
v___x_964_ = v_x_959_;
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_val_962_);
lean_dec(v_x_959_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3));
v___x_967_ = l_Nat_reprFast(v_val_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 3);
lean_ctor_set(v___x_964_, 0, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_972_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_966_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Repr_addAppParen(v___x_970_, v_x_960_);
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___boxed(lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_x_974_, v_x_975_);
lean_dec(v_x_975_);
return v_res_976_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__3(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_unsigned_to_nat(2u);
v___x_984_ = lean_nat_to_int(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__4(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_nat_to_int(v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr(lean_object* v_x_1005_, lean_object* v_prec_1006_){
_start:
{
switch(lean_obj_tag(v_x_1005_))
{
case 0:
{
lean_object* v_ver_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1026_; 
v_ver_1007_ = lean_ctor_get(v_x_1005_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_x_1005_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v_x_1005_, 0);
lean_dec(v_unused_1027_);
v___x_1009_ = v_x_1005_;
v_isShared_1010_ = v_isSharedCheck_1026_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_ver_1007_);
lean_dec(v_x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1026_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___y_1012_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_unsigned_to_nat(1024u);
v___x_1023_ = lean_nat_dec_le(v___x_1022_, v_prec_1006_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1012_ = v___x_1024_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1012_ = v___x_1025_;
goto v___jp_1011_;
}
v___jp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1013_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__2));
v___x_1014_ = l_Lake_instReprStdVer_repr___redArg(v_ver_1007_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 5);
lean_ctor_set(v___x_1009_, 1, v___x_1014_);
lean_ctor_set(v___x_1009_, 0, v___x_1013_);
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_inc(v___y_1012_);
v___x_1017_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___y_1012_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = 0;
v___x_1019_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set_uint8(v___x_1019_, sizeof(void*)*1, v___x_1018_);
v___x_1020_ = l_Repr_addAppParen(v___x_1019_, v_prec_1006_);
return v___x_1020_;
}
}
}
}
case 1:
{
lean_object* v_date_1028_; lean_object* v_rev_1029_; lean_object* v___y_1031_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_date_1028_ = lean_ctor_get(v_x_1005_, 1);
lean_inc_ref(v_date_1028_);
v_rev_1029_ = lean_ctor_get(v_x_1005_, 2);
lean_inc(v_rev_1029_);
lean_dec_ref_known(v_x_1005_, 3);
v___x_1044_ = lean_unsigned_to_nat(1024u);
v___x_1045_ = lean_nat_dec_le(v___x_1044_, v_prec_1006_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1031_ = v___x_1046_;
goto v___jp_1030_;
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1031_ = v___x_1047_;
goto v___jp_1030_;
}
v___jp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1032_ = lean_box(1);
v___x_1033_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__7));
v___x_1034_ = lean_unsigned_to_nat(1024u);
v___x_1035_ = l_Lake_instReprDate_repr___redArg(v_date_1028_);
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1033_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1032_);
v___x_1038_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_rev_1029_, v___x_1034_);
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
lean_inc(v___y_1031_);
v___x_1040_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___y_1031_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = 0;
v___x_1042_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*1, v___x_1041_);
v___x_1043_ = l_Repr_addAppParen(v___x_1042_, v_prec_1006_);
return v___x_1043_;
}
}
case 2:
{
lean_object* v_n_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1068_; 
v_n_1048_ = lean_ctor_get(v_x_1005_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_x_1005_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_x_1005_, 0);
lean_dec(v_unused_1069_);
v___x_1050_ = v_x_1005_;
v_isShared_1051_ = v_isSharedCheck_1068_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_n_1048_);
lean_dec(v_x_1005_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1068_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___y_1053_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(1024u);
v___x_1065_ = lean_nat_dec_le(v___x_1064_, v_prec_1006_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1053_ = v___x_1066_;
goto v___jp_1052_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1053_ = v___x_1067_;
goto v___jp_1052_;
}
v___jp_1052_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1054_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__10));
v___x_1055_ = l_Nat_reprFast(v_n_1048_);
v___x_1056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 5);
lean_ctor_set(v___x_1050_, 1, v___x_1056_);
lean_ctor_set(v___x_1050_, 0, v___x_1054_);
v___x_1058_ = v___x_1050_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_inc(v___y_1053_);
v___x_1059_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___y_1053_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = 0;
v___x_1061_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*1, v___x_1060_);
v___x_1062_ = l_Repr_addAppParen(v___x_1061_, v_prec_1006_);
return v___x_1062_;
}
}
}
}
default: 
{
lean_object* v_v_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1090_; 
v_v_1070_ = lean_ctor_get(v_x_1005_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_x_1005_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_x_1005_, 0);
lean_dec(v_unused_1091_);
v___x_1072_ = v_x_1005_;
v_isShared_1073_ = v_isSharedCheck_1090_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_v_1070_);
lean_dec(v_x_1005_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1090_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___y_1075_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_unsigned_to_nat(1024u);
v___x_1087_ = lean_nat_dec_le(v___x_1086_, v_prec_1006_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1075_ = v___x_1088_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1075_ = v___x_1089_;
goto v___jp_1074_;
}
v___jp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1076_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__13));
v___x_1077_ = l_String_quote(v_v_1070_);
v___x_1078_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 5);
lean_ctor_set(v___x_1072_, 1, v___x_1078_);
lean_ctor_set(v___x_1072_, 0, v___x_1076_);
v___x_1080_ = v___x_1072_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_inc(v___y_1075_);
v___x_1081_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___y_1075_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = 0;
v___x_1083_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*1, v___x_1082_);
v___x_1084_ = l_Repr_addAppParen(v___x_1083_, v_prec_1006_);
return v___x_1084_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr___boxed(lean_object* v_x_1092_, lean_object* v_prec_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lake_instReprToolchainVer_repr(v_x_1092_, v_prec_1093_);
lean_dec(v_prec_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer_decEq(lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
switch(lean_obj_tag(v_x_1097_))
{
case 0:
{
if (lean_obj_tag(v_x_1098_) == 0)
{
lean_object* v_ver_1099_; lean_object* v_ver_1100_; uint8_t v___x_1101_; 
v_ver_1099_ = lean_ctor_get(v_x_1097_, 1);
lean_inc_ref(v_ver_1099_);
lean_dec_ref_known(v_x_1097_, 2);
v_ver_1100_ = lean_ctor_get(v_x_1098_, 1);
lean_inc_ref(v_ver_1100_);
lean_dec_ref_known(v_x_1098_, 2);
v___x_1101_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_1099_, v_ver_1100_);
lean_dec_ref(v_ver_1100_);
lean_dec_ref(v_ver_1099_);
return v___x_1101_;
}
else
{
uint8_t v___x_1102_; 
lean_dec_ref_known(v_x_1097_, 2);
lean_dec_ref(v_x_1098_);
v___x_1102_ = 0;
return v___x_1102_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1098_) == 1)
{
lean_object* v_date_1103_; lean_object* v_rev_1104_; lean_object* v_date_1105_; lean_object* v_rev_1106_; uint8_t v___x_1107_; 
v_date_1103_ = lean_ctor_get(v_x_1097_, 1);
lean_inc_ref(v_date_1103_);
v_rev_1104_ = lean_ctor_get(v_x_1097_, 2);
lean_inc(v_rev_1104_);
lean_dec_ref_known(v_x_1097_, 3);
v_date_1105_ = lean_ctor_get(v_x_1098_, 1);
lean_inc_ref(v_date_1105_);
v_rev_1106_ = lean_ctor_get(v_x_1098_, 2);
lean_inc(v_rev_1106_);
lean_dec_ref_known(v_x_1098_, 3);
v___x_1107_ = l_Lake_instDecidableEqDate_decEq(v_date_1103_, v_date_1105_);
lean_dec_ref(v_date_1105_);
lean_dec_ref(v_date_1103_);
if (v___x_1107_ == 0)
{
lean_dec(v_rev_1106_);
lean_dec(v_rev_1104_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_1109_ = l_Option_instDecidableEq___redArg(v___x_1108_, v_rev_1104_, v_rev_1106_);
return v___x_1109_;
}
}
else
{
uint8_t v___x_1110_; 
lean_dec_ref_known(v_x_1097_, 3);
lean_dec_ref(v_x_1098_);
v___x_1110_ = 0;
return v___x_1110_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1098_) == 2)
{
lean_object* v_n_1111_; lean_object* v_n_1112_; uint8_t v___x_1113_; 
v_n_1111_ = lean_ctor_get(v_x_1097_, 1);
lean_inc(v_n_1111_);
lean_dec_ref_known(v_x_1097_, 2);
v_n_1112_ = lean_ctor_get(v_x_1098_, 1);
lean_inc(v_n_1112_);
lean_dec_ref_known(v_x_1098_, 2);
v___x_1113_ = lean_nat_dec_eq(v_n_1111_, v_n_1112_);
lean_dec(v_n_1112_);
lean_dec(v_n_1111_);
return v___x_1113_;
}
else
{
uint8_t v___x_1114_; 
lean_dec_ref_known(v_x_1097_, 2);
lean_dec_ref(v_x_1098_);
v___x_1114_ = 0;
return v___x_1114_;
}
}
default: 
{
if (lean_obj_tag(v_x_1098_) == 3)
{
lean_object* v_v_1115_; lean_object* v_v_1116_; uint8_t v___x_1117_; 
v_v_1115_ = lean_ctor_get(v_x_1097_, 1);
lean_inc_ref(v_v_1115_);
lean_dec_ref_known(v_x_1097_, 2);
v_v_1116_ = lean_ctor_get(v_x_1098_, 1);
lean_inc_ref(v_v_1116_);
lean_dec_ref_known(v_x_1098_, 2);
v___x_1117_ = lean_string_dec_eq(v_v_1115_, v_v_1116_);
lean_dec_ref(v_v_1116_);
lean_dec_ref(v_v_1115_);
return v___x_1117_;
}
else
{
uint8_t v___x_1118_; 
lean_dec_ref_known(v_x_1097_, 2);
lean_dec_ref(v_x_1098_);
v___x_1118_ = 0;
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer_decEq___boxed(lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1119_, v_x_1120_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer(lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1123_, v_x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer___boxed(lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
uint8_t v_res_1128_; lean_object* v_r_1129_; 
v_res_1128_ = l_Lake_instDecidableEqToolchainVer(v_x_1126_, v_x_1127_);
v_r_1129_ = lean_box(v_res_1128_);
return v_r_1129_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1134_ = lean_string_utf8_byte_size(v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(lean_object* v_s_1135_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1136_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1137_ = lean_string_utf8_byte_size(v_s_1135_);
v___x_1138_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1);
v___x_1139_ = lean_nat_dec_le(v___x_1138_, v___x_1137_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_dec_ref(v_s_1135_);
v___x_1140_ = lean_box(0);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_string_memcmp(v_s_1135_, v___x_1136_, v___x_1141_, v___x_1141_, v___x_1138_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref(v_s_1135_);
v___x_1143_ = lean_box(0);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_inc_ref(v_s_1135_);
v___x_1144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1144_, 0, v_s_1135_);
lean_ctor_set(v___x_1144_, 1, v___x_1141_);
lean_ctor_set(v___x_1144_, 2, v___x_1137_);
v___x_1145_ = l_String_Slice_pos_x21(v___x_1144_, v___x_1138_);
lean_dec_ref_known(v___x_1144_, 3);
v___x_1146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1146_, 0, v_s_1135_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
lean_ctor_set(v___x_1146_, 2, v___x_1137_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(lean_object* v_s_1148_, lean_object* v_pat_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v_s_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(lean_object* v_s_1151_, lean_object* v_pat_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(v_s_1151_, v_pat_1152_);
lean_dec_ref(v_pat_1152_);
return v_res_1153_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1155_ = lean_string_utf8_byte_size(v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(lean_object* v_s_1156_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1157_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1158_ = lean_string_utf8_byte_size(v_s_1156_);
v___x_1159_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0);
v___x_1160_ = lean_nat_dec_le(v___x_1159_, v___x_1158_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec_ref(v_s_1156_);
v___x_1161_ = lean_box(0);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = lean_string_memcmp(v_s_1156_, v___x_1157_, v___x_1162_, v___x_1162_, v___x_1159_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
lean_dec_ref(v_s_1156_);
v___x_1164_ = lean_box(0);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_inc_ref(v_s_1156_);
v___x_1165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1165_, 0, v_s_1156_);
lean_ctor_set(v___x_1165_, 1, v___x_1162_);
lean_ctor_set(v___x_1165_, 2, v___x_1158_);
v___x_1166_ = l_String_Slice_pos_x21(v___x_1165_, v___x_1159_);
lean_dec_ref_known(v___x_1165_, 3);
v___x_1167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1167_, 0, v_s_1156_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
lean_ctor_set(v___x_1167_, 2, v___x_1158_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(lean_object* v_s_1169_, lean_object* v_pat_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v_s_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(lean_object* v_s_1172_, lean_object* v_pat_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(v_s_1172_, v_pat_1173_);
lean_dec_ref(v_pat_1173_);
return v_res_1174_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0));
v___x_1177_ = lean_string_utf8_byte_size(v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object* v_s_1178_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1179_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0));
v___x_1180_ = lean_string_utf8_byte_size(v_s_1178_);
v___x_1181_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1);
v___x_1182_ = lean_nat_dec_le(v___x_1181_, v___x_1180_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec_ref(v_s_1178_);
v___x_1183_ = lean_box(0);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = lean_string_memcmp(v_s_1178_, v___x_1179_, v___x_1184_, v___x_1184_, v___x_1181_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec_ref(v_s_1178_);
v___x_1186_ = lean_box(0);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_inc_ref(v_s_1178_);
v___x_1187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1187_, 0, v_s_1178_);
lean_ctor_set(v___x_1187_, 1, v___x_1184_);
lean_ctor_set(v___x_1187_, 2, v___x_1180_);
v___x_1188_ = l_String_Slice_pos_x21(v___x_1187_, v___x_1181_);
lean_dec_ref_known(v___x_1187_, 3);
v___x_1189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1189_, 0, v_s_1178_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
lean_ctor_set(v___x_1189_, 2, v___x_1180_);
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(lean_object* v_s_1191_, lean_object* v_pat_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v_s_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object* v_s_1194_, lean_object* v_pat_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(v_s_1194_, v_pat_1195_);
lean_dec_ref(v_pat_1195_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(lean_object* v___x_1197_, lean_object* v_ver_1198_, lean_object* v_a_1199_, lean_object* v_b_1200_){
_start:
{
lean_object* v_startInclusive_1201_; lean_object* v_endExclusive_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v_startInclusive_1201_ = lean_ctor_get(v___x_1197_, 1);
v_endExclusive_1202_ = lean_ctor_get(v___x_1197_, 2);
v___x_1203_ = lean_nat_sub(v_endExclusive_1202_, v_startInclusive_1201_);
v___x_1204_ = lean_nat_dec_eq(v_a_1199_, v___x_1203_);
lean_dec(v___x_1203_);
if (v___x_1204_ == 0)
{
uint32_t v___x_1205_; uint32_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1205_ = lean_string_utf8_get_fast(v_ver_1198_, v_a_1199_);
v___x_1206_ = 58;
v___x_1207_ = lean_uint32_dec_eq(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_string_utf8_next_fast(v_ver_1198_, v_a_1199_);
lean_dec(v_a_1199_);
v_a_1199_ = v___x_1209_;
v_b_1200_ = v___x_1208_;
goto _start;
}
else
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_a_1199_);
return v___x_1211_;
}
}
else
{
lean_dec(v_a_1199_);
lean_inc(v_b_1200_);
return v_b_1200_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg___boxed(lean_object* v___x_1212_, lean_object* v_ver_1213_, lean_object* v_a_1214_, lean_object* v_b_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1212_, v_ver_1213_, v_a_1214_, v_b_1215_);
lean_dec(v_b_1215_);
lean_dec_ref(v_ver_1213_);
lean_dec_ref(v___x_1212_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object* v___x_1217_, lean_object* v_rest_1218_, lean_object* v_a_1219_, lean_object* v_b_1220_){
_start:
{
lean_object* v_startInclusive_1221_; lean_object* v_endExclusive_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_startInclusive_1221_ = lean_ctor_get(v___x_1217_, 1);
v_endExclusive_1222_ = lean_ctor_get(v___x_1217_, 2);
v___x_1223_ = lean_nat_sub(v_endExclusive_1222_, v_startInclusive_1221_);
v___x_1224_ = lean_nat_dec_eq(v_a_1219_, v___x_1223_);
lean_dec(v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_string_utf8_next_fast(v_rest_1218_, v_a_1219_);
lean_dec(v_a_1219_);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_add(v_b_1220_, v___x_1226_);
lean_dec(v_b_1220_);
v_a_1219_ = v___x_1225_;
v_b_1220_ = v___x_1227_;
goto _start;
}
else
{
lean_dec(v_a_1219_);
return v_b_1220_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg___boxed(lean_object* v___x_1229_, lean_object* v_rest_1230_, lean_object* v_a_1231_, lean_object* v_b_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___x_1229_, v_rest_1230_, v_a_1231_, v_b_1232_);
lean_dec_ref(v_rest_1230_);
lean_dec_ref(v___x_1229_);
return v_res_1233_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__1(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1236_ = lean_string_utf8_byte_size(v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__2(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1238_ = lean_string_utf8_byte_size(v___x_1237_);
return v___x_1238_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__4(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__3));
v___x_1241_ = lean_string_utf8_byte_size(v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofString(lean_object* v_ver_1242_){
_start:
{
lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; uint8_t v___y_1248_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; uint8_t v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; uint8_t v___y_1284_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; uint8_t v___y_1290_; lean_object* v_fst_1337_; lean_object* v_snd_1338_; lean_object* v___y_1361_; lean_object* v_searcher_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_searcher_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_string_utf8_byte_size(v_ver_1242_);
lean_inc_ref(v_ver_1242_);
v___x_1371_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1371_, 0, v_ver_1242_);
lean_ctor_set(v___x_1371_, 1, v_searcher_1369_);
lean_ctor_set(v___x_1371_, 2, v___x_1370_);
v___x_1372_ = lean_box(0);
v___x_1373_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1371_, v_ver_1242_, v_searcher_1369_, v___x_1372_);
lean_dec_ref_known(v___x_1371_, 3);
if (lean_obj_tag(v___x_1373_) == 0)
{
v___y_1361_ = v___x_1370_;
goto v___jp_1360_;
}
else
{
lean_object* v_val_1374_; 
v_val_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___y_1361_ = v_val_1374_;
goto v___jp_1360_;
}
v___jp_1243_:
{
if (v___y_1248_ == 0)
{
lean_object* v___x_1249_; 
v___x_1249_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v___y_1245_);
if (lean_obj_tag(v___x_1249_) == 1)
{
lean_object* v_val_1250_; lean_object* v_startInclusive_1251_; lean_object* v_endExclusive_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v_val_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_val_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v_startInclusive_1251_ = lean_ctor_get(v_val_1250_, 1);
v_endExclusive_1252_ = lean_ctor_get(v_val_1250_, 2);
v___x_1253_ = lean_nat_sub(v_endExclusive_1252_, v_startInclusive_1251_);
v___x_1254_ = lean_nat_dec_eq(v___x_1253_, v___y_1246_);
lean_dec(v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1255_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1256_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__1, &l_Lake_ToolchainVer_ofString___closed__1_once, _init_l_Lake_ToolchainVer_ofString___closed__1);
v___x_1257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___y_1246_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
v___x_1258_ = l_String_Slice_beq(v_val_1250_, v___x_1257_);
lean_dec_ref_known(v___x_1257_, 3);
lean_dec(v_val_1250_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; 
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1244_);
lean_inc_ref(v_ver_1242_);
v___x_1259_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_ver_1242_);
lean_ctor_set(v___x_1259_, 1, v_ver_1242_);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; 
lean_dec_ref(v_ver_1242_);
v___x_1260_ = l_Lake_ToolchainVer_nightly___override(v___y_1244_, v___y_1247_);
return v___x_1260_;
}
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_val_1250_);
lean_dec(v___y_1246_);
lean_dec_ref(v_ver_1242_);
v___x_1261_ = l_Lake_ToolchainVer_nightly___override(v___y_1244_, v___y_1247_);
return v___x_1261_;
}
}
else
{
lean_object* v___x_1262_; 
lean_dec(v___x_1249_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1244_);
lean_inc_ref(v_ver_1242_);
v___x_1262_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_ver_1242_);
lean_ctor_set(v___x_1262_, 1, v_ver_1242_);
return v___x_1262_;
}
}
else
{
lean_object* v___x_1263_; 
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v_ver_1242_);
v___x_1263_ = l_Lake_ToolchainVer_nightly___override(v___y_1244_, v___y_1247_);
return v___x_1263_;
}
}
v___jp_1264_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1273_ = l_String_Slice_positions(v___y_1267_);
lean_inc(v___y_1270_);
v___x_1274_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___y_1267_, v___y_1265_, v___x_1273_, v___y_1270_);
lean_dec_ref(v___y_1265_);
lean_dec_ref(v___y_1267_);
v___x_1275_ = lean_nat_dec_le(v___x_1274_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec(v___x_1274_);
if (v___x_1275_ == 0)
{
if (lean_obj_tag(v___y_1272_) == 0)
{
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_inc_ref(v_ver_1242_);
v___x_1276_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_ver_1242_);
lean_ctor_set(v___x_1276_, 1, v_ver_1242_);
return v___x_1276_;
}
else
{
v___y_1244_ = v___y_1268_;
v___y_1245_ = v___y_1269_;
v___y_1246_ = v___y_1270_;
v___y_1247_ = v___y_1272_;
v___y_1248_ = v___y_1271_;
goto v___jp_1243_;
}
}
else
{
v___y_1244_ = v___y_1268_;
v___y_1245_ = v___y_1269_;
v___y_1246_ = v___y_1270_;
v___y_1247_ = v___y_1272_;
v___y_1248_ = v___y_1271_;
goto v___jp_1243_;
}
}
else
{
v___y_1244_ = v___y_1268_;
v___y_1245_ = v___y_1269_;
v___y_1246_ = v___y_1270_;
v___y_1247_ = v___y_1272_;
v___y_1248_ = v___y_1271_;
goto v___jp_1243_;
}
}
v___jp_1277_:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_box(0);
v___y_1265_ = v___y_1278_;
v___y_1266_ = v___y_1280_;
v___y_1267_ = v___y_1279_;
v___y_1268_ = v___y_1281_;
v___y_1269_ = v___y_1282_;
v___y_1270_ = v___y_1283_;
v___y_1271_ = v___y_1284_;
v___y_1272_ = v___x_1285_;
goto v___jp_1264_;
}
v___jp_1286_:
{
lean_object* v___x_1291_; 
lean_inc_ref(v___y_1289_);
v___x_1291_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v___y_1289_);
if (lean_obj_tag(v___x_1291_) == 1)
{
lean_object* v_val_1292_; lean_object* v_rest_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v___y_1289_);
v_val_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_val_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v_rest_1293_ = l_String_Slice_toString(v_val_1292_);
lean_dec(v_val_1292_);
v___x_1294_ = lean_unsigned_to_nat(10u);
v___x_1295_ = lean_string_utf8_byte_size(v_rest_1293_);
lean_inc_n(v___y_1288_, 3);
lean_inc_ref_n(v_rest_1293_, 2);
v___x_1296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1296_, 0, v_rest_1293_);
lean_ctor_set(v___x_1296_, 1, v___y_1288_);
lean_ctor_set(v___x_1296_, 2, v___x_1295_);
v___x_1297_ = l_String_Slice_Pos_nextn(v___x_1296_, v___y_1288_, v___x_1294_);
lean_inc(v___x_1297_);
v___x_1298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1298_, 0, v_rest_1293_);
lean_ctor_set(v___x_1298_, 1, v___y_1288_);
lean_ctor_set(v___x_1298_, 2, v___x_1297_);
v___x_1299_ = l_String_Slice_toString(v___x_1298_);
lean_dec_ref_known(v___x_1298_, 3);
v___x_1300_ = l_Lake_Date_ofString_x3f(v___x_1299_);
if (lean_obj_tag(v___x_1300_) == 1)
{
lean_object* v_val_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_val_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_val_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1303_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__2, &l_Lake_ToolchainVer_ofString___closed__2_once, _init_l_Lake_ToolchainVer_ofString___closed__2);
v___x_1304_ = lean_nat_sub(v___x_1295_, v___x_1297_);
v___x_1305_ = lean_nat_dec_le(v___x_1303_, v___x_1304_);
lean_dec(v___x_1304_);
if (v___x_1305_ == 0)
{
lean_dec(v___x_1297_);
v___y_1278_ = v_rest_1293_;
v___y_1279_ = v___x_1296_;
v___y_1280_ = v___x_1294_;
v___y_1281_ = v_val_1301_;
v___y_1282_ = v___y_1287_;
v___y_1283_ = v___y_1288_;
v___y_1284_ = v___y_1290_;
goto v___jp_1277_;
}
else
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_string_memcmp(v_rest_1293_, v___x_1302_, v___x_1297_, v___y_1288_, v___x_1303_);
if (v___x_1306_ == 0)
{
lean_dec(v___x_1297_);
v___y_1278_ = v_rest_1293_;
v___y_1279_ = v___x_1296_;
v___y_1280_ = v___x_1294_;
v___y_1281_ = v_val_1301_;
v___y_1282_ = v___y_1287_;
v___y_1283_ = v___y_1288_;
v___y_1284_ = v___y_1290_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_inc(v___x_1297_);
lean_inc_ref_n(v_rest_1293_, 2);
v___x_1307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1307_, 0, v_rest_1293_);
lean_ctor_set(v___x_1307_, 1, v___x_1297_);
lean_ctor_set(v___x_1307_, 2, v___x_1295_);
v___x_1308_ = l_String_Slice_pos_x21(v___x_1307_, v___x_1303_);
lean_dec_ref_known(v___x_1307_, 3);
v___x_1309_ = lean_nat_add(v___x_1297_, v___x_1308_);
lean_dec(v___x_1308_);
lean_dec(v___x_1297_);
v___x_1310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1310_, 0, v_rest_1293_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
lean_ctor_set(v___x_1310_, 2, v___x_1295_);
v___x_1311_ = l_String_Slice_toString(v___x_1310_);
lean_dec_ref_known(v___x_1310_, 3);
v___x_1312_ = lean_string_utf8_byte_size(v___x_1311_);
lean_inc(v___y_1288_);
v___x_1313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___y_1288_);
lean_ctor_set(v___x_1313_, 2, v___x_1312_);
v___x_1314_ = l_String_Slice_toNat_x3f(v___x_1313_);
lean_dec_ref_known(v___x_1313_, 3);
v___y_1265_ = v_rest_1293_;
v___y_1266_ = v___x_1294_;
v___y_1267_ = v___x_1296_;
v___y_1268_ = v_val_1301_;
v___y_1269_ = v___y_1287_;
v___y_1270_ = v___y_1288_;
v___y_1271_ = v___y_1290_;
v___y_1272_ = v___x_1314_;
goto v___jp_1264_;
}
}
}
else
{
lean_object* v___x_1315_; 
lean_dec(v___x_1300_);
lean_dec(v___x_1297_);
lean_dec_ref_known(v___x_1296_, 3);
lean_dec_ref(v_rest_1293_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_inc_ref(v_ver_1242_);
v___x_1315_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1315_, 0, v_ver_1242_);
lean_ctor_set(v___x_1315_, 1, v_ver_1242_);
return v___x_1315_;
}
}
else
{
lean_object* v___x_1316_; 
lean_dec(v___x_1291_);
lean_dec(v___y_1288_);
v___x_1316_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___y_1289_);
if (lean_obj_tag(v___x_1316_) == 1)
{
lean_object* v_val_1317_; lean_object* v___x_1318_; 
v_val_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_val_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = l_String_Slice_toNat_x3f(v_val_1317_);
lean_dec(v_val_1317_);
if (lean_obj_tag(v___x_1318_) == 1)
{
if (v___y_1290_ == 0)
{
lean_object* v_val_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_val_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_val_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = ((lean_object*)(l_Lake_ToolchainVer_prOrigin___closed__0));
v___x_1321_ = lean_string_dec_eq(v___y_1287_, v___x_1320_);
lean_dec_ref(v___y_1287_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_dec(v_val_1319_);
lean_inc_ref(v_ver_1242_);
v___x_1322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_ver_1242_);
lean_ctor_set(v___x_1322_, 1, v_ver_1242_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; 
lean_dec_ref(v_ver_1242_);
v___x_1323_ = l_Lake_ToolchainVer_pr___override(v_val_1319_);
return v___x_1323_;
}
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1325_; 
lean_dec_ref(v___y_1287_);
lean_dec_ref(v_ver_1242_);
v_val_1324_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1325_ = l_Lake_ToolchainVer_pr___override(v_val_1324_);
return v___x_1325_;
}
}
else
{
lean_object* v___x_1326_; 
lean_dec(v___x_1318_);
lean_dec_ref(v___y_1287_);
lean_inc_ref(v_ver_1242_);
v___x_1326_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1326_, 0, v_ver_1242_);
lean_ctor_set(v___x_1326_, 1, v_ver_1242_);
return v___x_1326_;
}
}
else
{
lean_object* v___x_1327_; 
lean_dec(v___x_1316_);
lean_inc_ref(v_ver_1242_);
v___x_1327_ = l_Lake_StdVer_parse(v_ver_1242_);
if (lean_obj_tag(v___x_1327_) == 1)
{
if (v___y_1290_ == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1330_ = lean_string_dec_eq(v___y_1287_, v___x_1329_);
lean_dec_ref(v___y_1287_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
lean_dec(v_a_1328_);
lean_inc_ref(v_ver_1242_);
v___x_1331_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_ver_1242_);
lean_ctor_set(v___x_1331_, 1, v_ver_1242_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; 
lean_dec_ref(v_ver_1242_);
v___x_1332_ = l_Lake_ToolchainVer_release___override(v_a_1328_);
return v___x_1332_;
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v___y_1287_);
lean_dec_ref(v_ver_1242_);
v_a_1333_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1334_ = l_Lake_ToolchainVer_release___override(v_a_1333_);
return v___x_1334_;
}
}
else
{
lean_object* v___x_1335_; 
lean_dec_ref(v___x_1327_);
lean_dec_ref(v___y_1287_);
lean_inc_ref(v_ver_1242_);
v___x_1335_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_ver_1242_);
lean_ctor_set(v___x_1335_, 1, v_ver_1242_);
return v___x_1335_;
}
}
}
}
v___jp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v_noOrigin_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1339_ = lean_string_utf8_byte_size(v_fst_1337_);
v___x_1340_ = lean_unsigned_to_nat(0u);
v_noOrigin_1341_ = lean_nat_dec_eq(v___x_1339_, v___x_1340_);
v___x_1342_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__3));
v___x_1343_ = lean_string_utf8_byte_size(v_snd_1338_);
v___x_1344_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__4, &l_Lake_ToolchainVer_ofString___closed__4_once, _init_l_Lake_ToolchainVer_ofString___closed__4);
v___x_1345_ = lean_nat_dec_le(v___x_1344_, v___x_1343_);
if (v___x_1345_ == 0)
{
v___y_1287_ = v_fst_1337_;
v___y_1288_ = v___x_1340_;
v___y_1289_ = v_snd_1338_;
v___y_1290_ = v_noOrigin_1341_;
goto v___jp_1286_;
}
else
{
uint8_t v___x_1346_; 
v___x_1346_ = lean_string_memcmp(v_snd_1338_, v___x_1342_, v___x_1340_, v___x_1340_, v___x_1344_);
if (v___x_1346_ == 0)
{
v___y_1287_ = v_fst_1337_;
v___y_1288_ = v___x_1340_;
v___y_1289_ = v_snd_1338_;
v___y_1290_ = v_noOrigin_1341_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1347_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_snd_1338_);
v___x_1348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1348_, 0, v_snd_1338_);
lean_ctor_set(v___x_1348_, 1, v___x_1340_);
lean_ctor_set(v___x_1348_, 2, v___x_1343_);
v___x_1349_ = l_String_Slice_Pos_nextn(v___x_1348_, v___x_1340_, v___x_1347_);
lean_dec_ref_known(v___x_1348_, 3);
v___x_1350_ = lean_string_utf8_extract(v_snd_1338_, v___x_1349_, v___x_1343_);
lean_dec(v___x_1349_);
lean_dec_ref(v_snd_1338_);
v___x_1351_ = l_Lake_StdVer_parse(v___x_1350_);
if (lean_obj_tag(v___x_1351_) == 1)
{
if (v_noOrigin_1341_ == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1354_ = lean_string_dec_eq(v_fst_1337_, v___x_1353_);
lean_dec_ref(v_fst_1337_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
lean_dec(v_a_1352_);
lean_inc_ref(v_ver_1242_);
v___x_1355_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_ver_1242_);
lean_ctor_set(v___x_1355_, 1, v_ver_1242_);
return v___x_1355_;
}
else
{
lean_object* v___x_1356_; 
lean_dec_ref(v_ver_1242_);
v___x_1356_ = l_Lake_ToolchainVer_release___override(v_a_1352_);
return v___x_1356_;
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1358_; 
lean_dec_ref(v_fst_1337_);
lean_dec_ref(v_ver_1242_);
v_a_1357_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1358_ = l_Lake_ToolchainVer_release___override(v_a_1357_);
return v___x_1358_;
}
}
else
{
lean_object* v___x_1359_; 
lean_dec_ref(v___x_1351_);
lean_dec_ref(v_fst_1337_);
lean_inc_ref(v_ver_1242_);
v___x_1359_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_ver_1242_);
lean_ctor_set(v___x_1359_, 1, v_ver_1242_);
return v___x_1359_;
}
}
}
}
v___jp_1360_:
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_string_utf8_byte_size(v_ver_1242_);
v___x_1363_ = lean_nat_dec_eq(v___y_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v_pos_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_pos_1364_ = lean_string_utf8_next_fast(v_ver_1242_, v___y_1361_);
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = lean_string_utf8_extract(v_ver_1242_, v___x_1365_, v___y_1361_);
lean_dec(v___y_1361_);
v___x_1367_ = lean_string_utf8_extract(v_ver_1242_, v_pos_1364_, v___x_1362_);
v_fst_1337_ = v___x_1366_;
v_snd_1338_ = v___x_1367_;
goto v___jp_1336_;
}
else
{
lean_object* v___x_1368_; 
lean_dec(v___y_1361_);
v___x_1368_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
lean_inc_ref(v_ver_1242_);
v_fst_1337_ = v___x_1368_;
v_snd_1338_ = v_ver_1242_;
goto v___jp_1336_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(lean_object* v___x_1375_, lean_object* v_rest_1376_, lean_object* v_inst_1377_, lean_object* v_R_1378_, lean_object* v_a_1379_, lean_object* v_b_1380_, lean_object* v_c_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___x_1375_, v_rest_1376_, v_a_1379_, v_b_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object* v___x_1383_, lean_object* v_rest_1384_, lean_object* v_inst_1385_, lean_object* v_R_1386_, lean_object* v_a_1387_, lean_object* v_b_1388_, lean_object* v_c_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(v___x_1383_, v_rest_1384_, v_inst_1385_, v_R_1386_, v_a_1387_, v_b_1388_, v_c_1389_);
lean_dec_ref(v_rest_1384_);
lean_dec_ref(v___x_1383_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(lean_object* v___x_1391_, lean_object* v_ver_1392_, lean_object* v_inst_1393_, lean_object* v_R_1394_, lean_object* v_a_1395_, lean_object* v_b_1396_, lean_object* v_c_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1391_, v_ver_1392_, v_a_1395_, v_b_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___boxed(lean_object* v___x_1399_, lean_object* v_ver_1400_, lean_object* v_inst_1401_, lean_object* v_R_1402_, lean_object* v_a_1403_, lean_object* v_b_1404_, lean_object* v_c_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(v___x_1399_, v_ver_1400_, v_inst_1401_, v_R_1402_, v_a_1403_, v_b_1404_, v_c_1405_);
lean_dec(v_b_1404_);
lean_dec_ref(v_ver_1400_);
lean_dec_ref(v___x_1399_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object* v_toolchainFile_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_IO_FS_readFile(v_toolchainFile_1407_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1427_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1427_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1427_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v_str_1418_; lean_object* v_startInclusive_1419_; lean_object* v_endExclusive_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = lean_string_utf8_byte_size(v_a_1410_);
v___x_1416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1416_, 0, v_a_1410_);
lean_ctor_set(v___x_1416_, 1, v___x_1414_);
lean_ctor_set(v___x_1416_, 2, v___x_1415_);
v___x_1417_ = l_String_Slice_trimAscii(v___x_1416_);
v_str_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_str_1418_);
v_startInclusive_1419_ = lean_ctor_get(v___x_1417_, 1);
lean_inc(v_startInclusive_1419_);
v_endExclusive_1420_ = lean_ctor_get(v___x_1417_, 2);
lean_inc(v_endExclusive_1420_);
lean_dec_ref(v___x_1417_);
v___x_1421_ = lean_string_utf8_extract(v_str_1418_, v_startInclusive_1419_, v_endExclusive_1420_);
lean_dec(v_endExclusive_1420_);
lean_dec(v_startInclusive_1419_);
lean_dec_ref(v_str_1418_);
v___x_1422_ = l_Lake_ToolchainVer_ofString(v___x_1421_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1423_);
v___x_1425_ = v___x_1412_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1439_; 
v_a_1428_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1430_ = v___x_1409_;
v_isShared_1431_ = v_isSharedCheck_1439_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1409_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1439_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
if (lean_obj_tag(v_a_1428_) == 11)
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_dec_ref_known(v_a_1428_, 2);
v___x_1432_ = lean_box(0);
if (v_isShared_1431_ == 0)
{
lean_ctor_set_tag(v___x_1430_, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
else
{
lean_object* v___x_1437_; 
if (v_isShared_1431_ == 0)
{
v___x_1437_ = v___x_1430_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1428_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f___boxed(lean_object* v_toolchainFile_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lake_ToolchainVer_ofFile_x3f(v_toolchainFile_1440_);
lean_dec_ref(v_toolchainFile_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f(lean_object* v_dir_1443_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = ((lean_object*)(l_Lake_toolchainFileName___closed__0));
v___x_1446_ = l_System_FilePath_join(v_dir_1443_, v___x_1445_);
v___x_1447_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1446_);
lean_dec_ref(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f___boxed(lean_object* v_dir_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lake_ToolchainVer_ofDir_x3f(v_dir_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0(lean_object* v_x_1453_){
_start:
{
lean_object* v_toString_1454_; lean_object* v___x_1455_; 
v_toString_1454_ = lean_ctor_get(v_x_1453_, 0);
lean_inc_ref(v_toString_1454_);
v___x_1455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_toString_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0___boxed(lean_object* v_x_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lake_ToolchainVer_instToJson___lam__0(v_x_1456_);
lean_dec_ref(v_x_1456_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instFromJson___lam__0(lean_object* v_x_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Json_getStr_x3f(v_x_1460_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1478_; 
v_a_1470_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1472_ = v___x_1461_;
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1461_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = l_Lake_ToolchainVer_ofString(v_a_1470_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1474_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_blt(lean_object* v_a_1481_, lean_object* v_b_1482_){
_start:
{
switch(lean_obj_tag(v_a_1481_))
{
case 0:
{
if (lean_obj_tag(v_b_1482_) == 0)
{
lean_object* v_ver_1483_; lean_object* v_ver_1484_; uint8_t v___x_1485_; 
v_ver_1483_ = lean_ctor_get(v_a_1481_, 1);
v_ver_1484_ = lean_ctor_get(v_b_1482_, 1);
v___x_1485_ = l_Lake_StdVer_compare(v_ver_1483_, v_ver_1484_);
if (v___x_1485_ == 0)
{
uint8_t v___x_1486_; 
v___x_1486_ = 1;
return v___x_1486_;
}
else
{
uint8_t v___x_1487_; 
v___x_1487_ = 0;
return v___x_1487_;
}
}
else
{
uint8_t v___x_1488_; 
v___x_1488_ = 0;
return v___x_1488_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1482_) == 1)
{
lean_object* v_date_1489_; lean_object* v_rev_1490_; lean_object* v_date_1491_; lean_object* v_rev_1492_; lean_object* v___y_1494_; uint8_t v___x_1499_; 
v_date_1489_ = lean_ctor_get(v_a_1481_, 1);
v_rev_1490_ = lean_ctor_get(v_a_1481_, 2);
v_date_1491_ = lean_ctor_get(v_b_1482_, 1);
v_rev_1492_ = lean_ctor_get(v_b_1482_, 2);
v___x_1499_ = l_Lake_instOrdDate_ord(v_date_1489_, v_date_1491_);
if (v___x_1499_ == 0)
{
uint8_t v___x_1500_; 
v___x_1500_ = 1;
return v___x_1500_;
}
else
{
uint8_t v___x_1501_; 
v___x_1501_ = l_Lake_instDecidableEqDate_decEq(v_date_1489_, v_date_1491_);
if (v___x_1501_ == 0)
{
return v___x_1501_;
}
else
{
if (lean_obj_tag(v_rev_1490_) == 0)
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_unsigned_to_nat(0u);
v___y_1494_ = v___x_1502_;
goto v___jp_1493_;
}
else
{
lean_object* v_val_1503_; 
v_val_1503_ = lean_ctor_get(v_rev_1490_, 0);
v___y_1494_ = v_val_1503_;
goto v___jp_1493_;
}
}
}
v___jp_1493_:
{
if (lean_obj_tag(v_rev_1492_) == 0)
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = lean_nat_dec_lt(v___y_1494_, v___x_1495_);
return v___x_1496_;
}
else
{
lean_object* v_val_1497_; uint8_t v___x_1498_; 
v_val_1497_ = lean_ctor_get(v_rev_1492_, 0);
v___x_1498_ = lean_nat_dec_lt(v___y_1494_, v_val_1497_);
return v___x_1498_;
}
}
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = 0;
return v___x_1504_;
}
}
default: 
{
uint8_t v___x_1505_; 
v___x_1505_ = 0;
return v___x_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_blt___boxed(lean_object* v_a_1506_, lean_object* v_b_1507_){
_start:
{
uint8_t v_res_1508_; lean_object* v_r_1509_; 
v_res_1508_ = l_Lake_ToolchainVer_blt(v_a_1506_, v_b_1507_);
lean_dec_ref(v_b_1507_);
lean_dec_ref(v_a_1506_);
v_r_1509_ = lean_box(v_res_1508_);
return v_r_1509_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLT(void){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_box(0);
return v___x_1510_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLt(lean_object* v_a_1511_, lean_object* v_b_1512_){
_start:
{
uint8_t v___x_1513_; 
v___x_1513_ = l_Lake_ToolchainVer_blt(v_a_1511_, v_b_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLt___boxed(lean_object* v_a_1514_, lean_object* v_b_1515_){
_start:
{
uint8_t v_res_1516_; lean_object* v_r_1517_; 
v_res_1516_ = l_Lake_ToolchainVer_decLt(v_a_1514_, v_b_1515_);
lean_dec_ref(v_b_1515_);
lean_dec_ref(v_a_1514_);
v_r_1517_ = lean_box(v_res_1516_);
return v_r_1517_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_ble(lean_object* v_a_1518_, lean_object* v_b_1519_){
_start:
{
switch(lean_obj_tag(v_a_1518_))
{
case 0:
{
if (lean_obj_tag(v_b_1519_) == 0)
{
lean_object* v_ver_1520_; lean_object* v_ver_1521_; uint8_t v___x_1522_; 
v_ver_1520_ = lean_ctor_get(v_a_1518_, 1);
v_ver_1521_ = lean_ctor_get(v_b_1519_, 1);
v___x_1522_ = l_Lake_StdVer_compare(v_ver_1520_, v_ver_1521_);
if (v___x_1522_ == 2)
{
uint8_t v___x_1523_; 
v___x_1523_ = 0;
return v___x_1523_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = 1;
return v___x_1524_;
}
}
else
{
uint8_t v___x_1525_; 
v___x_1525_ = 0;
return v___x_1525_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1519_) == 1)
{
lean_object* v_date_1526_; lean_object* v_rev_1527_; lean_object* v_date_1528_; lean_object* v_rev_1529_; lean_object* v___y_1531_; uint8_t v___x_1536_; 
v_date_1526_ = lean_ctor_get(v_a_1518_, 1);
v_rev_1527_ = lean_ctor_get(v_a_1518_, 2);
v_date_1528_ = lean_ctor_get(v_b_1519_, 1);
v_rev_1529_ = lean_ctor_get(v_b_1519_, 2);
v___x_1536_ = l_Lake_instOrdDate_ord(v_date_1526_, v_date_1528_);
if (v___x_1536_ == 0)
{
uint8_t v___x_1537_; 
v___x_1537_ = 1;
return v___x_1537_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = l_Lake_instDecidableEqDate_decEq(v_date_1526_, v_date_1528_);
if (v___x_1538_ == 0)
{
return v___x_1538_;
}
else
{
if (lean_obj_tag(v_rev_1527_) == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v___y_1531_ = v___x_1539_;
goto v___jp_1530_;
}
else
{
lean_object* v_val_1540_; 
v_val_1540_ = lean_ctor_get(v_rev_1527_, 0);
v___y_1531_ = v_val_1540_;
goto v___jp_1530_;
}
}
}
v___jp_1530_:
{
if (lean_obj_tag(v_rev_1529_) == 0)
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = lean_nat_dec_le(v___y_1531_, v___x_1532_);
return v___x_1533_;
}
else
{
lean_object* v_val_1534_; uint8_t v___x_1535_; 
v_val_1534_ = lean_ctor_get(v_rev_1529_, 0);
v___x_1535_ = lean_nat_dec_le(v___y_1531_, v_val_1534_);
return v___x_1535_;
}
}
}
else
{
uint8_t v___x_1541_; 
v___x_1541_ = 0;
return v___x_1541_;
}
}
case 2:
{
if (lean_obj_tag(v_b_1519_) == 2)
{
lean_object* v_n_1542_; lean_object* v_n_1543_; uint8_t v___x_1544_; 
v_n_1542_ = lean_ctor_get(v_a_1518_, 1);
v_n_1543_ = lean_ctor_get(v_b_1519_, 1);
v___x_1544_ = lean_nat_dec_eq(v_n_1542_, v_n_1543_);
return v___x_1544_;
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = 0;
return v___x_1545_;
}
}
default: 
{
if (lean_obj_tag(v_b_1519_) == 3)
{
lean_object* v_v_1546_; lean_object* v_v_1547_; uint8_t v___x_1548_; 
v_v_1546_ = lean_ctor_get(v_a_1518_, 1);
v_v_1547_ = lean_ctor_get(v_b_1519_, 1);
v___x_1548_ = lean_string_dec_eq(v_v_1546_, v_v_1547_);
return v___x_1548_;
}
else
{
uint8_t v___x_1549_; 
v___x_1549_ = 0;
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ble___boxed(lean_object* v_a_1550_, lean_object* v_b_1551_){
_start:
{
uint8_t v_res_1552_; lean_object* v_r_1553_; 
v_res_1552_ = l_Lake_ToolchainVer_ble(v_a_1550_, v_b_1551_);
lean_dec_ref(v_b_1551_);
lean_dec_ref(v_a_1550_);
v_r_1553_ = lean_box(v_res_1552_);
return v_r_1553_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLE(void){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_box(0);
return v___x_1554_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLe(lean_object* v_a_1555_, lean_object* v_b_1556_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = l_Lake_ToolchainVer_ble(v_a_1555_, v_b_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLe___boxed(lean_object* v_a_1558_, lean_object* v_b_1559_){
_start:
{
uint8_t v_res_1560_; lean_object* v_r_1561_; 
v_res_1560_ = l_Lake_ToolchainVer_decLe(v_a_1558_, v_b_1559_);
lean_dec_ref(v_b_1559_);
lean_dec_ref(v_a_1558_);
v_r_1561_ = lean_box(v_res_1560_);
return v_r_1561_;
}
}
LEAN_EXPORT lean_object* l_Lake_normalizeToolchain(lean_object* v_s_1562_){
_start:
{
lean_object* v___x_1563_; lean_object* v_toString_1564_; 
v___x_1563_ = l_Lake_ToolchainVer_ofString(v_s_1562_);
v_toString_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_ref(v_toString_1564_);
lean_dec_ref(v___x_1563_);
return v_toString_1564_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeVersionToolchainVer___lam__0(lean_object* v_x_1569_){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = l_Lake_ToolchainVer_ofString(v_x_1569_);
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx(uint8_t v_x_1574_){
_start:
{
switch(v_x_1574_)
{
case 0:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_unsigned_to_nat(0u);
return v___x_1575_;
}
case 1:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_unsigned_to_nat(1u);
return v___x_1576_;
}
case 2:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_unsigned_to_nat(2u);
return v___x_1577_;
}
case 3:
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_unsigned_to_nat(3u);
return v___x_1578_;
}
case 4:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_unsigned_to_nat(4u);
return v___x_1579_;
}
default: 
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_unsigned_to_nat(5u);
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___boxed(lean_object* v_x_1581_){
_start:
{
uint8_t v_x_boxed_1582_; lean_object* v_res_1583_; 
v_x_boxed_1582_ = lean_unbox(v_x_1581_);
v_res_1583_ = l_Lake_ComparatorOp_ctorIdx(v_x_boxed_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx(uint8_t v_x_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lake_ComparatorOp_ctorIdx(v_x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx___boxed(lean_object* v_x_1586_){
_start:
{
uint8_t v_x_4__boxed_1587_; lean_object* v_res_1588_; 
v_x_4__boxed_1587_ = lean_unbox(v_x_1586_);
v_res_1588_ = l_Lake_ComparatorOp_toCtorIdx(v_x_4__boxed_1587_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg(lean_object* v_k_1589_){
_start:
{
lean_inc(v_k_1589_);
return v_k_1589_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg___boxed(lean_object* v_k_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lake_ComparatorOp_ctorElim___redArg(v_k_1590_);
lean_dec(v_k_1590_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim(lean_object* v_motive_1592_, lean_object* v_ctorIdx_1593_, uint8_t v_t_1594_, lean_object* v_h_1595_, lean_object* v_k_1596_){
_start:
{
lean_inc(v_k_1596_);
return v_k_1596_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___boxed(lean_object* v_motive_1597_, lean_object* v_ctorIdx_1598_, lean_object* v_t_1599_, lean_object* v_h_1600_, lean_object* v_k_1601_){
_start:
{
uint8_t v_t_boxed_1602_; lean_object* v_res_1603_; 
v_t_boxed_1602_ = lean_unbox(v_t_1599_);
v_res_1603_ = l_Lake_ComparatorOp_ctorElim(v_motive_1597_, v_ctorIdx_1598_, v_t_boxed_1602_, v_h_1600_, v_k_1601_);
lean_dec(v_k_1601_);
lean_dec(v_ctorIdx_1598_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg(lean_object* v_lt_1604_){
_start:
{
lean_inc(v_lt_1604_);
return v_lt_1604_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg___boxed(lean_object* v_lt_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lake_ComparatorOp_lt_elim___redArg(v_lt_1605_);
lean_dec(v_lt_1605_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim(lean_object* v_motive_1607_, uint8_t v_t_1608_, lean_object* v_h_1609_, lean_object* v_lt_1610_){
_start:
{
lean_inc(v_lt_1610_);
return v_lt_1610_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___boxed(lean_object* v_motive_1611_, lean_object* v_t_1612_, lean_object* v_h_1613_, lean_object* v_lt_1614_){
_start:
{
uint8_t v_t_boxed_1615_; lean_object* v_res_1616_; 
v_t_boxed_1615_ = lean_unbox(v_t_1612_);
v_res_1616_ = l_Lake_ComparatorOp_lt_elim(v_motive_1611_, v_t_boxed_1615_, v_h_1613_, v_lt_1614_);
lean_dec(v_lt_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg(lean_object* v_le_1617_){
_start:
{
lean_inc(v_le_1617_);
return v_le_1617_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg___boxed(lean_object* v_le_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lake_ComparatorOp_le_elim___redArg(v_le_1618_);
lean_dec(v_le_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim(lean_object* v_motive_1620_, uint8_t v_t_1621_, lean_object* v_h_1622_, lean_object* v_le_1623_){
_start:
{
lean_inc(v_le_1623_);
return v_le_1623_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___boxed(lean_object* v_motive_1624_, lean_object* v_t_1625_, lean_object* v_h_1626_, lean_object* v_le_1627_){
_start:
{
uint8_t v_t_boxed_1628_; lean_object* v_res_1629_; 
v_t_boxed_1628_ = lean_unbox(v_t_1625_);
v_res_1629_ = l_Lake_ComparatorOp_le_elim(v_motive_1624_, v_t_boxed_1628_, v_h_1626_, v_le_1627_);
lean_dec(v_le_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg(lean_object* v_gt_1630_){
_start:
{
lean_inc(v_gt_1630_);
return v_gt_1630_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg___boxed(lean_object* v_gt_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lake_ComparatorOp_gt_elim___redArg(v_gt_1631_);
lean_dec(v_gt_1631_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim(lean_object* v_motive_1633_, uint8_t v_t_1634_, lean_object* v_h_1635_, lean_object* v_gt_1636_){
_start:
{
lean_inc(v_gt_1636_);
return v_gt_1636_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___boxed(lean_object* v_motive_1637_, lean_object* v_t_1638_, lean_object* v_h_1639_, lean_object* v_gt_1640_){
_start:
{
uint8_t v_t_boxed_1641_; lean_object* v_res_1642_; 
v_t_boxed_1641_ = lean_unbox(v_t_1638_);
v_res_1642_ = l_Lake_ComparatorOp_gt_elim(v_motive_1637_, v_t_boxed_1641_, v_h_1639_, v_gt_1640_);
lean_dec(v_gt_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg(lean_object* v_ge_1643_){
_start:
{
lean_inc(v_ge_1643_);
return v_ge_1643_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg___boxed(lean_object* v_ge_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lake_ComparatorOp_ge_elim___redArg(v_ge_1644_);
lean_dec(v_ge_1644_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim(lean_object* v_motive_1646_, uint8_t v_t_1647_, lean_object* v_h_1648_, lean_object* v_ge_1649_){
_start:
{
lean_inc(v_ge_1649_);
return v_ge_1649_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___boxed(lean_object* v_motive_1650_, lean_object* v_t_1651_, lean_object* v_h_1652_, lean_object* v_ge_1653_){
_start:
{
uint8_t v_t_boxed_1654_; lean_object* v_res_1655_; 
v_t_boxed_1654_ = lean_unbox(v_t_1651_);
v_res_1655_ = l_Lake_ComparatorOp_ge_elim(v_motive_1650_, v_t_boxed_1654_, v_h_1652_, v_ge_1653_);
lean_dec(v_ge_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg(lean_object* v_eq_1656_){
_start:
{
lean_inc(v_eq_1656_);
return v_eq_1656_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg___boxed(lean_object* v_eq_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lake_ComparatorOp_eq_elim___redArg(v_eq_1657_);
lean_dec(v_eq_1657_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim(lean_object* v_motive_1659_, uint8_t v_t_1660_, lean_object* v_h_1661_, lean_object* v_eq_1662_){
_start:
{
lean_inc(v_eq_1662_);
return v_eq_1662_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___boxed(lean_object* v_motive_1663_, lean_object* v_t_1664_, lean_object* v_h_1665_, lean_object* v_eq_1666_){
_start:
{
uint8_t v_t_boxed_1667_; lean_object* v_res_1668_; 
v_t_boxed_1667_ = lean_unbox(v_t_1664_);
v_res_1668_ = l_Lake_ComparatorOp_eq_elim(v_motive_1663_, v_t_boxed_1667_, v_h_1665_, v_eq_1666_);
lean_dec(v_eq_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg(lean_object* v_ne_1669_){
_start:
{
lean_inc(v_ne_1669_);
return v_ne_1669_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg___boxed(lean_object* v_ne_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lake_ComparatorOp_ne_elim___redArg(v_ne_1670_);
lean_dec(v_ne_1670_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim(lean_object* v_motive_1672_, uint8_t v_t_1673_, lean_object* v_h_1674_, lean_object* v_ne_1675_){
_start:
{
lean_inc(v_ne_1675_);
return v_ne_1675_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___boxed(lean_object* v_motive_1676_, lean_object* v_t_1677_, lean_object* v_h_1678_, lean_object* v_ne_1679_){
_start:
{
uint8_t v_t_boxed_1680_; lean_object* v_res_1681_; 
v_t_boxed_1680_ = lean_unbox(v_t_1677_);
v_res_1681_ = l_Lake_ComparatorOp_ne_elim(v_motive_1676_, v_t_boxed_1680_, v_h_1678_, v_ne_1679_);
lean_dec(v_ne_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr(uint8_t v_x_1700_, lean_object* v_prec_1701_){
_start:
{
lean_object* v___y_1703_; lean_object* v___y_1710_; lean_object* v___y_1717_; lean_object* v___y_1724_; lean_object* v___y_1731_; lean_object* v___y_1738_; 
switch(v_x_1700_)
{
case 0:
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = lean_unsigned_to_nat(1024u);
v___x_1745_ = lean_nat_dec_le(v___x_1744_, v_prec_1701_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1703_ = v___x_1746_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1703_ = v___x_1747_;
goto v___jp_1702_;
}
}
case 1:
{
lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = lean_unsigned_to_nat(1024u);
v___x_1749_ = lean_nat_dec_le(v___x_1748_, v_prec_1701_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1710_ = v___x_1750_;
goto v___jp_1709_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1710_ = v___x_1751_;
goto v___jp_1709_;
}
}
case 2:
{
lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1752_ = lean_unsigned_to_nat(1024u);
v___x_1753_ = lean_nat_dec_le(v___x_1752_, v_prec_1701_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1717_ = v___x_1754_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1717_ = v___x_1755_;
goto v___jp_1716_;
}
}
case 3:
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_unsigned_to_nat(1024u);
v___x_1757_ = lean_nat_dec_le(v___x_1756_, v_prec_1701_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1724_ = v___x_1758_;
goto v___jp_1723_;
}
else
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1724_ = v___x_1759_;
goto v___jp_1723_;
}
}
case 4:
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = lean_unsigned_to_nat(1024u);
v___x_1761_ = lean_nat_dec_le(v___x_1760_, v_prec_1701_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1731_ = v___x_1762_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1731_ = v___x_1763_;
goto v___jp_1730_;
}
}
default: 
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_unsigned_to_nat(1024u);
v___x_1765_ = lean_nat_dec_le(v___x_1764_, v_prec_1701_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1738_ = v___x_1766_;
goto v___jp_1737_;
}
else
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1738_ = v___x_1767_;
goto v___jp_1737_;
}
}
}
v___jp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1704_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__1));
lean_inc(v___y_1703_);
v___x_1705_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___y_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = 0;
v___x_1707_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*1, v___x_1706_);
v___x_1708_ = l_Repr_addAppParen(v___x_1707_, v_prec_1701_);
return v___x_1708_;
}
v___jp_1709_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1711_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__3));
lean_inc(v___y_1710_);
v___x_1712_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___y_1710_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = 0;
v___x_1714_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1714_, 0, v___x_1712_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*1, v___x_1713_);
v___x_1715_ = l_Repr_addAppParen(v___x_1714_, v_prec_1701_);
return v___x_1715_;
}
v___jp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1718_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__5));
lean_inc(v___y_1717_);
v___x_1719_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___y_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = 0;
v___x_1721_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1721_, 0, v___x_1719_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*1, v___x_1720_);
v___x_1722_ = l_Repr_addAppParen(v___x_1721_, v_prec_1701_);
return v___x_1722_;
}
v___jp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1725_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__7));
lean_inc(v___y_1724_);
v___x_1726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = 0;
v___x_1728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set_uint8(v___x_1728_, sizeof(void*)*1, v___x_1727_);
v___x_1729_ = l_Repr_addAppParen(v___x_1728_, v_prec_1701_);
return v___x_1729_;
}
v___jp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1732_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__9));
lean_inc(v___y_1731_);
v___x_1733_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___y_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = 0;
v___x_1735_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*1, v___x_1734_);
v___x_1736_ = l_Repr_addAppParen(v___x_1735_, v_prec_1701_);
return v___x_1736_;
}
v___jp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1739_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__11));
lean_inc(v___y_1738_);
v___x_1740_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___y_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = 0;
v___x_1742_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*1, v___x_1741_);
v___x_1743_ = l_Repr_addAppParen(v___x_1742_, v_prec_1701_);
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr___boxed(lean_object* v_x_1768_, lean_object* v_prec_1769_){
_start:
{
uint8_t v_x_341__boxed_1770_; lean_object* v_res_1771_; 
v_x_341__boxed_1770_ = lean_unbox(v_x_1768_);
v_res_1771_ = l_Lake_instReprComparatorOp_repr(v_x_341__boxed_1770_, v_prec_1769_);
lean_dec(v_prec_1769_);
return v_res_1771_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp_default(void){
_start:
{
uint8_t v___x_1774_; 
v___x_1774_ = 0;
return v___x_1774_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp(void){
_start:
{
uint8_t v___x_1775_; 
v___x_1775_ = 0;
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(lean_object* v_sym_1776_, uint8_t v_cmp_1777_, lean_object* v_t_1778_){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = lean_box(v_cmp_1777_);
lean_inc_ref(v_sym_1776_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v_sym_1776_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = l_Lean_Data_Trie_insert___redArg(v_t_1778_, v_sym_1776_, v___x_1780_);
lean_dec_ref(v_sym_1776_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0___boxed(lean_object* v_sym_1782_, lean_object* v_cmp_1783_, lean_object* v_t_1784_){
_start:
{
uint8_t v_cmp_boxed_1785_; lean_object* v_res_1786_; 
v_cmp_boxed_1785_ = lean_unbox(v_cmp_1783_);
v_res_1786_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v_sym_1782_, v_cmp_boxed_1785_, v_t_1784_);
return v_res_1786_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9(void){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10(void){
_start:
{
lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1797_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9);
v___x_1798_ = 0;
v___x_1799_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
v___x_1800_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1799_, v___x_1798_, v___x_1797_);
return v___x_1800_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11(void){
_start:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1801_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10);
v___x_1802_ = 1;
v___x_1803_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7));
v___x_1804_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1803_, v___x_1802_, v___x_1801_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12(void){
_start:
{
lean_object* v___x_1805_; uint8_t v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11);
v___x_1806_ = 1;
v___x_1807_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
v___x_1808_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1807_, v___x_1806_, v___x_1805_);
return v___x_1808_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13(void){
_start:
{
lean_object* v___x_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1809_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12);
v___x_1810_ = 2;
v___x_1811_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
v___x_1812_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1811_, v___x_1810_, v___x_1809_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14(void){
_start:
{
lean_object* v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1813_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13);
v___x_1814_ = 3;
v___x_1815_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4));
v___x_1816_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1815_, v___x_1814_, v___x_1813_);
return v___x_1816_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15(void){
_start:
{
lean_object* v___x_1817_; uint8_t v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1817_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14);
v___x_1818_ = 3;
v___x_1819_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
v___x_1820_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1819_, v___x_1818_, v___x_1817_);
return v___x_1820_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16(void){
_start:
{
lean_object* v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1821_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15);
v___x_1822_ = 4;
v___x_1823_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
v___x_1824_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1823_, v___x_1822_, v___x_1821_);
return v___x_1824_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17(void){
_start:
{
lean_object* v___x_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1825_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16);
v___x_1826_ = 5;
v___x_1827_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1));
v___x_1828_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1827_, v___x_1826_, v___x_1825_);
return v___x_1828_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18(void){
_start:
{
lean_object* v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1829_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17);
v___x_1830_ = 5;
v___x_1831_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
v___x_1832_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1831_, v___x_1830_, v___x_1829_);
return v___x_1832_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie(void){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(lean_object* v_s_1836_, lean_object* v_p_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie;
v___x_1839_ = lean_string_utf8_byte_size(v_s_1836_);
lean_inc(v_p_1837_);
v___x_1840_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_1836_, v___x_1838_, v_p_1837_, v___x_1839_);
if (lean_obj_tag(v___x_1840_) == 1)
{
lean_object* v_val_1841_; lean_object* v_fst_1842_; lean_object* v_snd_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1857_; 
v_val_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_val_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v_fst_1842_ = lean_ctor_get(v_val_1841_, 0);
v_snd_1843_ = lean_ctor_get(v_val_1841_, 1);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_val_1841_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1845_ = v_val_1841_;
v_isShared_1846_ = v_isSharedCheck_1857_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_snd_1843_);
lean_inc(v_fst_1842_);
lean_dec(v_val_1841_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1857_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v_p_x27_1848_; uint8_t v___x_1849_; 
v___x_1847_ = lean_string_utf8_byte_size(v_fst_1842_);
lean_dec(v_fst_1842_);
v_p_x27_1848_ = lean_nat_add(v_p_1837_, v___x_1847_);
v___x_1849_ = lean_string_is_valid_pos(v_s_1836_, v_p_x27_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
lean_dec(v_p_x27_1848_);
lean_dec(v_snd_1843_);
v___x_1850_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0));
if (v_isShared_1846_ == 0)
{
lean_ctor_set_tag(v___x_1845_, 1);
lean_ctor_set(v___x_1845_, 1, v_p_1837_);
lean_ctor_set(v___x_1845_, 0, v___x_1850_);
v___x_1852_ = v___x_1845_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_p_1837_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v___x_1855_; 
lean_dec(v_p_1837_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v_p_x27_1848_);
lean_ctor_set(v___x_1845_, 0, v_snd_1843_);
v___x_1855_ = v___x_1845_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_snd_1843_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_p_x27_1848_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec(v___x_1840_);
v___x_1858_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1));
v___x_1859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v_p_1837_);
return v___x_1859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___boxed(lean_object* v_s_1860_, lean_object* v_p_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1860_, v_p_1861_);
lean_dec_ref(v_s_1860_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f(lean_object* v_s_1863_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1863_, v___x_1864_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v_a_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
v_a_1867_ = lean_ctor_get(v___x_1865_, 1);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1865_, 2);
v___x_1868_ = lean_string_utf8_byte_size(v_s_1863_);
v___x_1869_ = lean_nat_dec_eq(v_a_1867_, v___x_1868_);
lean_dec(v_a_1867_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
lean_dec(v_a_1866_);
v___x_1870_ = lean_box(0);
return v___x_1870_;
}
else
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_a_1866_);
return v___x_1871_;
}
}
else
{
lean_object* v___x_1872_; 
lean_dec_ref_known(v___x_1865_, 2);
v___x_1872_ = lean_box(0);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f___boxed(lean_object* v_s_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lake_ComparatorOp_ofString_x3f(v_s_1873_);
lean_dec_ref(v_s_1873_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString(uint8_t v_self_1875_){
_start:
{
switch(v_self_1875_)
{
case 0:
{
lean_object* v___x_1876_; 
v___x_1876_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
return v___x_1876_;
}
case 1:
{
lean_object* v___x_1877_; 
v___x_1877_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
return v___x_1877_;
}
case 2:
{
lean_object* v___x_1878_; 
v___x_1878_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
return v___x_1878_;
}
case 3:
{
lean_object* v___x_1879_; 
v___x_1879_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
return v___x_1879_;
}
case 4:
{
lean_object* v___x_1880_; 
v___x_1880_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
return v___x_1880_;
}
default: 
{
lean_object* v___x_1881_; 
v___x_1881_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString___boxed(lean_object* v_self_1882_){
_start:
{
uint8_t v_self_boxed_1883_; lean_object* v_res_1884_; 
v_self_boxed_1883_ = lean_unbox(v_self_1882_);
v_res_1884_ = l_Lake_ComparatorOp_toString(v_self_boxed_1883_);
return v_res_1884_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_unsigned_to_nat(7u);
v___x_1897_ = lean_nat_to_int(v___x_1896_);
return v___x_1897_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_unsigned_to_nat(6u);
v___x_1902_ = lean_nat_to_int(v___x_1901_);
return v___x_1902_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = lean_unsigned_to_nat(19u);
v___x_1907_ = lean_nat_to_int(v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___redArg(lean_object* v_x_1908_){
_start:
{
lean_object* v_ver_1909_; uint8_t v_op_1910_; uint8_t v_includeSuffixes_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_ver_1909_ = lean_ctor_get(v_x_1908_, 0);
lean_inc_ref(v_ver_1909_);
v_op_1910_ = lean_ctor_get_uint8(v_x_1908_, sizeof(void*)*1);
v_includeSuffixes_1911_ = lean_ctor_get_uint8(v_x_1908_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_1908_);
v___x_1912_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_1913_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__3));
v___x_1914_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__4, &l_Lake_instReprVerComparator_repr___redArg___closed__4_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__4);
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = l_Lake_instReprStdVer_repr___redArg(v_ver_1909_);
v___x_1917_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1914_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = 0;
v___x_1919_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set_uint8(v___x_1919_, sizeof(void*)*1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1913_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_1922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_box(1);
v___x_1924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__6));
v___x_1926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1912_);
v___x_1928_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__7, &l_Lake_instReprVerComparator_repr___redArg___closed__7_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__7);
v___x_1929_ = l_Lake_instReprComparatorOp_repr(v_op_1910_, v___x_1915_);
v___x_1930_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*1, v___x_1918_);
v___x_1932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1927_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v___x_1921_);
v___x_1934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v___x_1923_);
v___x_1935_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__9));
v___x_1936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v___x_1912_);
v___x_1938_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__10, &l_Lake_instReprVerComparator_repr___redArg___closed__10_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__10);
v___x_1939_ = l_Bool_repr___redArg(v_includeSuffixes_1911_);
v___x_1940_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*1, v___x_1918_);
v___x_1942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1937_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_1944_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_1945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v___x_1942_);
v___x_1946_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_1947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1943_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*1, v___x_1918_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr(lean_object* v_x_1950_, lean_object* v_prec_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lake_instReprVerComparator_repr___redArg(v_x_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___boxed(lean_object* v_x_1953_, lean_object* v_prec_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lake_instReprVerComparator_repr(v_x_1953_, v_prec_1954_);
lean_dec(v_prec_1954_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(lean_object* v_s_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1971_; 
lean_inc(v_a_1970_);
v___x_1971_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1969_, v_a_1970_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2038_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_a_1973_ = lean_ctor_get(v___x_1971_, 1);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_1975_ = v___x_1971_;
v_isShared_1976_ = v_isSharedCheck_2038_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2038_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = lean_string_utf8_byte_size(v_s_1969_);
v___x_1978_ = lean_nat_dec_eq(v_a_1973_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_del_object(v___x_1975_);
lean_dec(v_a_1970_);
lean_inc_ref(v_s_1969_);
v___x_1979_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_1969_, v_a_1973_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v_a_1981_; lean_object* v___x_1982_; lean_object* v_a_1983_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
v_a_1981_ = lean_ctor_get(v___x_1979_, 1);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1979_, 2);
v___x_1982_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_1969_, v_a_1981_);
lean_dec_ref(v_s_1969_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
if (lean_obj_tag(v_a_1983_) == 1)
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2005_; 
v_a_1984_ = lean_ctor_get(v___x_1982_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v___x_1982_, 0);
lean_dec(v_unused_2006_);
v___x_1986_ = v___x_1982_;
v_isShared_1987_ = v_isSharedCheck_2005_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1982_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2005_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_val_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_val_1988_ = lean_ctor_get(v_a_1983_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v_a_1983_, 1);
v___x_1989_ = lean_string_utf8_byte_size(v_val_1988_);
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = lean_nat_dec_eq(v___x_1989_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; lean_object* v___x_1996_; 
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v_a_1980_);
lean_ctor_set(v___x_1992_, 1, v_val_1988_);
v___x_1993_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
v___x_1994_ = lean_unbox(v_a_1972_);
lean_dec(v_a_1972_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*1, v___x_1994_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*1 + 1, v___x_1991_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1993_);
v___x_1996_ = v___x_1986_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_a_1984_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; lean_object* v___x_2003_; 
lean_dec(v_val_1988_);
v___x_1998_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_a_1980_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
v___x_2001_ = lean_unbox(v_a_1972_);
lean_dec(v_a_1972_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*1, v___x_2001_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*1 + 1, v___x_1991_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_2000_);
v___x_2003_ = v___x_1986_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_a_1984_);
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
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_a_1983_);
v_a_2007_ = lean_ctor_get(v___x_1982_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_1982_, 0);
lean_dec(v_unused_2019_);
v___x_2009_ = v___x_1982_;
v_isShared_2010_ = v_isSharedCheck_2018_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1982_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2018_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2016_; 
v___x_2011_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_a_1980_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
v___x_2014_ = lean_unbox(v_a_1972_);
lean_dec(v_a_1972_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*1, v___x_2014_);
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*1 + 1, v___x_1978_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2013_);
v___x_2016_ = v___x_2009_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_a_2007_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_a_1972_);
lean_dec_ref(v_s_1969_);
v_a_2020_ = lean_ctor_get(v___x_1979_, 0);
v_a_2021_ = lean_ctor_get(v___x_1979_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_1979_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_inc(v_a_2020_);
lean_dec(v___x_1979_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2020_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
lean_dec(v_a_1972_);
v___x_2029_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0));
v___x_2030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2030_, 0, v_s_1969_);
lean_ctor_set(v___x_2030_, 1, v_a_1970_);
lean_ctor_set(v___x_2030_, 2, v___x_1977_);
v___x_2031_ = l_String_Slice_toString(v___x_2030_);
lean_dec_ref_known(v___x_2030_, 3);
v___x_2032_ = lean_string_append(v___x_2029_, v___x_2031_);
lean_dec_ref(v___x_2031_);
v___x_2033_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1));
v___x_2034_ = lean_string_append(v___x_2032_, v___x_2033_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set_tag(v___x_1975_, 1);
lean_ctor_set(v___x_1975_, 0, v___x_2034_);
v___x_2036_ = v___x_1975_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_a_1973_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_a_1970_);
lean_dec_ref(v_s_1969_);
v_a_2039_ = lean_ctor_get(v___x_1971_, 0);
v_a_2040_ = lean_ctor_get(v___x_1971_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_1971_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_inc(v_a_2039_);
lean_dec(v___x_1971_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2039_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_parse(lean_object* v_s_2048_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = lean_unsigned_to_nat(0u);
v___x_2050_ = lean_string_utf8_byte_size(v_s_2048_);
lean_inc_ref(v_s_2048_);
v___x_2051_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_2048_, v___x_2049_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v_a_2053_; uint8_t v___x_2054_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
v_a_2053_ = lean_ctor_get(v___x_2051_, 1);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2051_, 2);
v___x_2054_ = lean_nat_dec_eq(v_a_2053_, v___x_2050_);
if (v___x_2054_ == 0)
{
lean_object* v_tail_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec(v_a_2052_);
v_tail_2055_ = lean_string_utf8_extract(v_s_2048_, v_a_2053_, v___x_2050_);
lean_dec(v_a_2053_);
lean_dec_ref(v_s_2048_);
v___x_2056_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_2057_ = lean_string_append(v___x_2056_, v_tail_2055_);
lean_dec_ref(v_tail_2055_);
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
else
{
lean_object* v___x_2059_; 
lean_dec(v_a_2053_);
lean_dec_ref(v_s_2048_);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_a_2052_);
return v___x_2059_;
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2061_; 
lean_dec_ref(v_s_2048_);
v_a_2060_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2051_, 2);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v_a_2060_);
return v___x_2061_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_VerComparator_test(lean_object* v_self_2062_, lean_object* v_ver_2063_){
_start:
{
uint8_t v___y_2065_; lean_object* v___y_2066_; uint8_t v___y_2067_; uint8_t v___y_2068_; uint8_t v___y_2069_; lean_object* v___y_2070_; uint8_t v___y_2071_; lean_object* v___y_2076_; uint8_t v___y_2077_; uint8_t v___y_2078_; uint8_t v___y_2079_; lean_object* v___y_2080_; uint8_t v___y_2081_; lean_object* v___y_2086_; uint8_t v___y_2087_; uint8_t v___y_2088_; lean_object* v___y_2089_; uint8_t v___y_2090_; lean_object* v___y_2095_; uint8_t v___y_2096_; lean_object* v___y_2097_; uint8_t v___y_2098_; lean_object* v_ver_2102_; uint8_t v_op_2103_; uint8_t v_includeSuffixes_2104_; lean_object* v_ver_2106_; 
v_ver_2102_ = lean_ctor_get(v_self_2062_, 0);
v_op_2103_ = lean_ctor_get_uint8(v_self_2062_, sizeof(void*)*1);
v_includeSuffixes_2104_ = lean_ctor_get_uint8(v_self_2062_, sizeof(void*)*1 + 1);
if (v_includeSuffixes_2104_ == 0)
{
lean_object* v_toSemVerCore_2110_; lean_object* v_specialDescr_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_toSemVerCore_2110_ = lean_ctor_get(v_ver_2063_, 0);
v_specialDescr_2111_ = lean_ctor_get(v_ver_2063_, 1);
v___x_2112_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_2113_ = lean_string_dec_eq(v_specialDescr_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v_toSemVerCore_2114_; lean_object* v_specialDescr_2115_; uint8_t v___x_2116_; 
v_toSemVerCore_2114_ = lean_ctor_get(v_ver_2102_, 0);
v_specialDescr_2115_ = lean_ctor_get(v_ver_2102_, 1);
v___x_2116_ = lean_string_dec_eq(v_specialDescr_2115_, v___x_2112_);
if (v___x_2116_ == 0)
{
uint8_t v___x_2117_; 
v___x_2117_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_2114_, v_toSemVerCore_2110_);
if (v___x_2117_ == 0)
{
return v_includeSuffixes_2104_;
}
else
{
switch(v_op_2103_)
{
case 0:
{
uint8_t v___x_2118_; 
v___x_2118_ = lean_string_dec_lt(v_specialDescr_2111_, v_specialDescr_2115_);
return v___x_2118_;
}
case 1:
{
uint8_t v___x_2119_; 
v___x_2119_ = l_String_decLE(v_specialDescr_2111_, v_specialDescr_2115_);
return v___x_2119_;
}
case 2:
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_string_dec_lt(v_specialDescr_2115_, v_specialDescr_2111_);
return v___x_2120_;
}
case 3:
{
uint8_t v___x_2121_; 
v___x_2121_ = l_String_decLE(v_specialDescr_2115_, v_specialDescr_2111_);
return v___x_2121_;
}
case 4:
{
uint8_t v___x_2122_; 
v___x_2122_ = lean_string_dec_eq(v_specialDescr_2111_, v_specialDescr_2115_);
return v___x_2122_;
}
default: 
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_string_dec_eq(v_specialDescr_2111_, v_specialDescr_2115_);
if (v___x_2123_ == 0)
{
return v___x_2117_;
}
else
{
return v___x_2116_;
}
}
}
}
}
else
{
return v_includeSuffixes_2104_;
}
}
else
{
v_ver_2106_ = v_ver_2063_;
goto v___jp_2105_;
}
}
else
{
v_ver_2106_ = v_ver_2063_;
goto v___jp_2105_;
}
v___jp_2064_:
{
uint8_t v___x_2072_; 
v___x_2072_ = l_Lake_instDecidableEqStdVer_decEq(v___y_2066_, v___y_2070_);
switch(v___y_2069_)
{
case 0:
{
return v___y_2068_;
}
case 1:
{
return v___y_2067_;
}
case 2:
{
return v___y_2065_;
}
case 3:
{
return v___y_2071_;
}
case 4:
{
return v___x_2072_;
}
default: 
{
if (v___x_2072_ == 0)
{
uint8_t v___x_2073_; 
v___x_2073_ = 1;
return v___x_2073_;
}
else
{
uint8_t v___x_2074_; 
v___x_2074_ = 0;
return v___x_2074_;
}
}
}
}
v___jp_2075_:
{
uint8_t v___x_2082_; 
v___x_2082_ = l_Lake_StdVer_compare(v___y_2080_, v___y_2076_);
if (v___x_2082_ == 2)
{
uint8_t v___x_2083_; 
v___x_2083_ = 0;
v___y_2065_ = v___y_2081_;
v___y_2066_ = v___y_2076_;
v___y_2067_ = v___y_2077_;
v___y_2068_ = v___y_2078_;
v___y_2069_ = v___y_2079_;
v___y_2070_ = v___y_2080_;
v___y_2071_ = v___x_2083_;
goto v___jp_2064_;
}
else
{
uint8_t v___x_2084_; 
v___x_2084_ = 1;
v___y_2065_ = v___y_2081_;
v___y_2066_ = v___y_2076_;
v___y_2067_ = v___y_2077_;
v___y_2068_ = v___y_2078_;
v___y_2069_ = v___y_2079_;
v___y_2070_ = v___y_2080_;
v___y_2071_ = v___x_2084_;
goto v___jp_2064_;
}
}
v___jp_2085_:
{
uint8_t v___x_2091_; 
v___x_2091_ = l_Lake_StdVer_compare(v___y_2089_, v___y_2086_);
if (v___x_2091_ == 0)
{
uint8_t v___x_2092_; 
v___x_2092_ = 1;
v___y_2076_ = v___y_2086_;
v___y_2077_ = v___y_2090_;
v___y_2078_ = v___y_2087_;
v___y_2079_ = v___y_2088_;
v___y_2080_ = v___y_2089_;
v___y_2081_ = v___x_2092_;
goto v___jp_2075_;
}
else
{
uint8_t v___x_2093_; 
v___x_2093_ = 0;
v___y_2076_ = v___y_2086_;
v___y_2077_ = v___y_2090_;
v___y_2078_ = v___y_2087_;
v___y_2079_ = v___y_2088_;
v___y_2080_ = v___y_2089_;
v___y_2081_ = v___x_2093_;
goto v___jp_2075_;
}
}
v___jp_2094_:
{
uint8_t v___x_2099_; 
v___x_2099_ = l_Lake_StdVer_compare(v___y_2095_, v___y_2097_);
if (v___x_2099_ == 2)
{
uint8_t v___x_2100_; 
v___x_2100_ = 0;
v___y_2086_ = v___y_2095_;
v___y_2087_ = v___y_2098_;
v___y_2088_ = v___y_2096_;
v___y_2089_ = v___y_2097_;
v___y_2090_ = v___x_2100_;
goto v___jp_2085_;
}
else
{
uint8_t v___x_2101_; 
v___x_2101_ = 1;
v___y_2086_ = v___y_2095_;
v___y_2087_ = v___y_2098_;
v___y_2088_ = v___y_2096_;
v___y_2089_ = v___y_2097_;
v___y_2090_ = v___x_2101_;
goto v___jp_2085_;
}
}
v___jp_2105_:
{
uint8_t v___x_2107_; 
v___x_2107_ = l_Lake_StdVer_compare(v_ver_2106_, v_ver_2102_);
if (v___x_2107_ == 0)
{
uint8_t v___x_2108_; 
v___x_2108_ = 1;
v___y_2095_ = v_ver_2106_;
v___y_2096_ = v_op_2103_;
v___y_2097_ = v_ver_2102_;
v___y_2098_ = v___x_2108_;
goto v___jp_2094_;
}
else
{
uint8_t v___x_2109_; 
v___x_2109_ = 0;
v___y_2095_ = v_ver_2106_;
v___y_2096_ = v_op_2103_;
v___y_2097_ = v_ver_2102_;
v___y_2098_ = v___x_2109_;
goto v___jp_2094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_test___boxed(lean_object* v_self_2124_, lean_object* v_ver_2125_){
_start:
{
uint8_t v_res_2126_; lean_object* v_r_2127_; 
v_res_2126_ = l_Lake_VerComparator_test(v_self_2124_, v_ver_2125_);
lean_dec_ref(v_ver_2125_);
lean_dec_ref(v_self_2124_);
v_r_2127_ = lean_box(v_res_2126_);
return v_r_2127_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_toString(lean_object* v_self_2128_){
_start:
{
lean_object* v_ver_2129_; uint8_t v_op_2130_; uint8_t v_includeSuffixes_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_ver_2129_ = lean_ctor_get(v_self_2128_, 0);
lean_inc_ref(v_ver_2129_);
v_op_2130_ = lean_ctor_get_uint8(v_self_2128_, sizeof(void*)*1);
v_includeSuffixes_2131_ = lean_ctor_get_uint8(v_self_2128_, sizeof(void*)*1 + 1);
lean_dec_ref(v_self_2128_);
v___x_2132_ = l_Lake_ComparatorOp_toString(v_op_2130_);
v___x_2133_ = l_Lake_StdVer_toString(v_ver_2129_);
v___x_2134_ = lean_string_append(v___x_2132_, v___x_2133_);
lean_dec_ref(v___x_2133_);
if (v_includeSuffixes_2131_ == 0)
{
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_2136_ = lean_string_append(v___x_2134_, v___x_2135_);
return v___x_2136_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_2139_, lean_object* v_x_2140_, lean_object* v_x_2141_){
_start:
{
if (lean_obj_tag(v_x_2141_) == 0)
{
lean_dec(v_x_2139_);
return v_x_2140_;
}
else
{
lean_object* v_head_2142_; lean_object* v_tail_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2153_; 
v_head_2142_ = lean_ctor_get(v_x_2141_, 0);
v_tail_2143_ = lean_ctor_get(v_x_2141_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2145_ = v_x_2141_;
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_tail_2143_);
lean_inc(v_head_2142_);
lean_dec(v_x_2141_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
lean_inc(v_x_2139_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set_tag(v___x_2145_, 5);
lean_ctor_set(v___x_2145_, 1, v_x_2139_);
lean_ctor_set(v___x_2145_, 0, v_x_2140_);
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_x_2140_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_x_2139_);
v___x_2148_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2142_);
v___x_2150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v_x_2140_ = v___x_2150_;
v_x_2141_ = v_tail_2143_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
if (lean_obj_tag(v_x_2156_) == 0)
{
lean_dec(v_x_2154_);
return v_x_2155_;
}
else
{
lean_object* v_head_2157_; lean_object* v_tail_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2168_; 
v_head_2157_ = lean_ctor_get(v_x_2156_, 0);
v_tail_2158_ = lean_ctor_get(v_x_2156_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_x_2156_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2160_ = v_x_2156_;
v_isShared_2161_ = v_isSharedCheck_2168_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_tail_2158_);
lean_inc(v_head_2157_);
lean_dec(v_x_2156_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2168_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
lean_inc(v_x_2154_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set_tag(v___x_2160_, 5);
lean_ctor_set(v___x_2160_, 1, v_x_2154_);
lean_ctor_set(v___x_2160_, 0, v_x_2155_);
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_x_2155_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_x_2154_);
v___x_2163_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2157_);
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_2154_, v___x_2165_, v_tail_2158_);
return v___x_2166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
lean_object* v___x_2171_; 
lean_dec(v_x_2170_);
v___x_2171_ = lean_box(0);
return v___x_2171_;
}
else
{
lean_object* v_tail_2172_; 
v_tail_2172_ = lean_ctor_get(v_x_2169_, 1);
if (lean_obj_tag(v_tail_2172_) == 0)
{
lean_object* v_head_2173_; lean_object* v___x_2174_; 
lean_dec(v_x_2170_);
v_head_2173_ = lean_ctor_get(v_x_2169_, 0);
lean_inc(v_head_2173_);
lean_dec_ref_known(v_x_2169_, 2);
v___x_2174_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2173_);
return v___x_2174_;
}
else
{
lean_object* v_head_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_inc(v_tail_2172_);
v_head_2175_ = lean_ctor_get(v_x_2169_, 0);
lean_inc(v_head_2175_);
lean_dec_ref_known(v_x_2169_, 2);
v___x_2176_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2175_);
v___x_2177_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(v_x_2170_, v___x_2176_, v_tail_2172_);
return v___x_2177_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0));
v___x_2184_ = lean_string_length(v___x_2183_);
return v___x_2184_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3);
v___x_2186_ = lean_nat_to_int(v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(lean_object* v_xs_2194_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2195_ = lean_array_get_size(v_xs_2194_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_nat_dec_eq(v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2198_ = lean_array_to_list(v_xs_2194_);
v___x_2199_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2200_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(v___x_2198_, v___x_2199_);
v___x_2201_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2202_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v___x_2200_);
v___x_2204_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2201_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = l_Std_Format_fill(v___x_2206_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; 
lean_dec_ref(v_xs_2194_);
v___x_2208_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(lean_object* v_x_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
if (lean_obj_tag(v_x_2211_) == 0)
{
lean_dec(v_x_2209_);
return v_x_2210_;
}
else
{
lean_object* v_head_2212_; lean_object* v_tail_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2223_; 
v_head_2212_ = lean_ctor_get(v_x_2211_, 0);
v_tail_2213_ = lean_ctor_get(v_x_2211_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_x_2211_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2215_ = v_x_2211_;
v_isShared_2216_ = v_isSharedCheck_2223_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_tail_2213_);
lean_inc(v_head_2212_);
lean_dec(v_x_2211_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2223_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
lean_inc(v_x_2209_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set_tag(v___x_2215_, 5);
lean_ctor_set(v___x_2215_, 1, v_x_2209_);
lean_ctor_set(v___x_2215_, 0, v_x_2210_);
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_x_2210_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_x_2209_);
v___x_2218_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2212_);
v___x_2220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v_x_2210_ = v___x_2220_;
v_x_2211_ = v_tail_2213_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_object* v___x_2226_; 
lean_dec(v_x_2225_);
v___x_2226_ = lean_box(0);
return v___x_2226_;
}
else
{
lean_object* v_tail_2227_; 
v_tail_2227_ = lean_ctor_get(v_x_2224_, 1);
if (lean_obj_tag(v_tail_2227_) == 0)
{
lean_object* v_head_2228_; lean_object* v___x_2229_; 
lean_dec(v_x_2225_);
v_head_2228_ = lean_ctor_get(v_x_2224_, 0);
lean_inc(v_head_2228_);
lean_dec_ref_known(v_x_2224_, 2);
v___x_2229_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2228_);
return v___x_2229_;
}
else
{
lean_object* v_head_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_inc(v_tail_2227_);
v_head_2230_ = lean_ctor_get(v_x_2224_, 0);
lean_inc(v_head_2230_);
lean_dec_ref_known(v_x_2224_, 2);
v___x_2231_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2230_);
v___x_2232_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(v_x_2225_, v___x_2231_, v_tail_2227_);
return v___x_2232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(lean_object* v_xs_2233_){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v___x_2234_ = lean_array_get_size(v_xs_2233_);
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = lean_nat_dec_eq(v___x_2234_, v___x_2235_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2237_ = lean_array_to_list(v_xs_2233_);
v___x_2238_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2239_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(v___x_2237_, v___x_2238_);
v___x_2240_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2241_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v___x_2239_);
v___x_2243_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2240_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = l_Std_Format_fill(v___x_2245_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; 
lean_dec_ref(v_xs_2233_);
v___x_2247_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2247_;
}
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_unsigned_to_nat(12u);
v___x_2258_ = lean_nat_to_int(v___x_2257_);
return v___x_2258_;
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_unsigned_to_nat(11u);
v___x_2263_ = lean_nat_to_int(v___x_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object* v_x_2264_){
_start:
{
lean_object* v_toString_2265_; lean_object* v_clauses_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2300_; 
v_toString_2265_ = lean_ctor_get(v_x_2264_, 0);
v_clauses_2266_ = lean_ctor_get(v_x_2264_, 1);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_x_2264_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2268_ = v_x_2264_;
v_isShared_2269_ = v_isSharedCheck_2300_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_clauses_2266_);
lean_inc(v_toString_2265_);
lean_dec(v_x_2264_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2300_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2270_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_2271_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__3));
v___x_2272_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__4, &l_Lake_instReprVerRange_repr___redArg___closed__4_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__4);
v___x_2273_ = l_String_quote(v_toString_2265_);
v___x_2274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set_tag(v___x_2268_, 4);
lean_ctor_set(v___x_2268_, 1, v___x_2274_);
lean_ctor_set(v___x_2268_, 0, v___x_2272_);
v___x_2276_ = v___x_2268_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
uint8_t v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2277_ = 0;
v___x_2278_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*1, v___x_2277_);
v___x_2279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2271_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_2281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_box(1);
v___x_2283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2281_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__6));
v___x_2285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v___x_2270_);
v___x_2287_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__7, &l_Lake_instReprVerRange_repr___redArg___closed__7_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__7);
v___x_2288_ = l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(v_clauses_2266_);
v___x_2289_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set_uint8(v___x_2290_, sizeof(void*)*1, v___x_2277_);
v___x_2291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2286_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_2293_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_2294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v___x_2291_);
v___x_2295_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_2296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2292_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*1, v___x_2277_);
return v___x_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr(lean_object* v_x_2301_, lean_object* v_prec_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lake_instReprVerRange_repr___redArg(v_x_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___boxed(lean_object* v_x_2304_, lean_object* v_prec_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lake_instReprVerRange_repr(v_x_2304_, v_prec_2305_);
lean_dec(v_prec_2305_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0(lean_object* v_self_2316_){
_start:
{
lean_object* v_toString_2317_; 
v_toString_2317_ = lean_ctor_get(v_self_2316_, 0);
lean_inc_ref(v_toString_2317_);
return v_toString_2317_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0___boxed(lean_object* v_self_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lake_VerRange_instToString___lam__0(v_self_2318_);
lean_dec_ref(v_self_2318_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(lean_object* v_as_2323_, size_t v_i_2324_, size_t v_stop_2325_, lean_object* v_b_2326_){
_start:
{
uint8_t v___x_2327_; 
v___x_2327_ = lean_usize_dec_eq(v_i_2324_, v_stop_2325_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; size_t v___x_2333_; size_t v___x_2334_; 
v___x_2328_ = lean_array_uget_borrowed(v_as_2323_, v_i_2324_);
v___x_2329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0));
v___x_2330_ = lean_string_append(v_b_2326_, v___x_2329_);
lean_inc(v___x_2328_);
v___x_2331_ = l_Lake_VerComparator_toString(v___x_2328_);
v___x_2332_ = lean_string_append(v___x_2330_, v___x_2331_);
lean_dec_ref(v___x_2331_);
v___x_2333_ = ((size_t)1ULL);
v___x_2334_ = lean_usize_add(v_i_2324_, v___x_2333_);
v_i_2324_ = v___x_2334_;
v_b_2326_ = v___x_2332_;
goto _start;
}
else
{
return v_b_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___boxed(lean_object* v_as_2336_, lean_object* v_i_2337_, lean_object* v_stop_2338_, lean_object* v_b_2339_){
_start:
{
size_t v_i_boxed_2340_; size_t v_stop_boxed_2341_; lean_object* v_res_2342_; 
v_i_boxed_2340_ = lean_unbox_usize(v_i_2337_);
lean_dec(v_i_2337_);
v_stop_boxed_2341_ = lean_unbox_usize(v_stop_2338_);
lean_dec(v_stop_2338_);
v_res_2342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_as_2336_, v_i_boxed_2340_, v_stop_boxed_2341_, v_b_2339_);
lean_dec_ref(v_as_2336_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(lean_object* v_ands_2344_){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2345_ = lean_array_get_size(v_ands_2344_);
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_nat_dec_eq(v___x_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v___x_2348_ = lean_array_fget_borrowed(v_ands_2344_, v___x_2346_);
lean_inc(v___x_2348_);
v___x_2349_ = l_Lake_VerComparator_toString(v___x_2348_);
v___x_2350_ = lean_unsigned_to_nat(1u);
v___x_2351_ = lean_nat_dec_lt(v___x_2350_, v___x_2345_);
if (v___x_2351_ == 0)
{
return v___x_2349_;
}
else
{
uint8_t v___x_2352_; 
v___x_2352_ = lean_nat_dec_le(v___x_2345_, v___x_2345_);
if (v___x_2352_ == 0)
{
if (v___x_2351_ == 0)
{
return v___x_2349_;
}
else
{
size_t v___x_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = ((size_t)1ULL);
v___x_2354_ = lean_usize_of_nat(v___x_2345_);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2344_, v___x_2353_, v___x_2354_, v___x_2349_);
return v___x_2355_;
}
}
else
{
size_t v___x_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = ((size_t)1ULL);
v___x_2357_ = lean_usize_of_nat(v___x_2345_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2344_, v___x_2356_, v___x_2357_, v___x_2349_);
return v___x_2358_;
}
}
}
else
{
lean_object* v___x_2359_; 
v___x_2359_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0));
return v___x_2359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___boxed(lean_object* v_ands_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v_ands_2360_);
lean_dec_ref(v_ands_2360_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(lean_object* v_as_2363_, size_t v_i_2364_, size_t v_stop_2365_, lean_object* v_b_2366_){
_start:
{
uint8_t v___x_2367_; 
v___x_2367_ = lean_usize_dec_eq(v_i_2364_, v_stop_2365_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; size_t v___x_2373_; size_t v___x_2374_; 
v___x_2368_ = lean_array_uget_borrowed(v_as_2363_, v_i_2364_);
v___x_2369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0));
v___x_2370_ = lean_string_append(v_b_2366_, v___x_2369_);
v___x_2371_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2368_);
v___x_2372_ = lean_string_append(v___x_2370_, v___x_2371_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = ((size_t)1ULL);
v___x_2374_ = lean_usize_add(v_i_2364_, v___x_2373_);
v_i_2364_ = v___x_2374_;
v_b_2366_ = v___x_2372_;
goto _start;
}
else
{
return v_b_2366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___boxed(lean_object* v_as_2376_, lean_object* v_i_2377_, lean_object* v_stop_2378_, lean_object* v_b_2379_){
_start:
{
size_t v_i_boxed_2380_; size_t v_stop_boxed_2381_; lean_object* v_res_2382_; 
v_i_boxed_2380_ = lean_unbox_usize(v_i_2377_);
lean_dec(v_i_2377_);
v_stop_boxed_2381_ = lean_unbox_usize(v_stop_2378_);
lean_dec(v_stop_2378_);
v_res_2382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_as_2376_, v_i_boxed_2380_, v_stop_boxed_2381_, v_b_2379_);
lean_dec_ref(v_as_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(lean_object* v_ors_2383_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2384_ = lean_array_get_size(v_ors_2383_);
v___x_2385_ = lean_unsigned_to_nat(0u);
v___x_2386_ = lean_nat_dec_eq(v___x_2384_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2387_ = lean_array_fget_borrowed(v_ors_2383_, v___x_2385_);
v___x_2388_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2387_);
v___x_2389_ = lean_unsigned_to_nat(1u);
v___x_2390_ = lean_nat_dec_lt(v___x_2389_, v___x_2384_);
if (v___x_2390_ == 0)
{
return v___x_2388_;
}
else
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_nat_dec_le(v___x_2384_, v___x_2384_);
if (v___x_2391_ == 0)
{
if (v___x_2390_ == 0)
{
return v___x_2388_;
}
else
{
size_t v___x_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = ((size_t)1ULL);
v___x_2393_ = lean_usize_of_nat(v___x_2384_);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2383_, v___x_2392_, v___x_2393_, v___x_2388_);
return v___x_2394_;
}
}
else
{
size_t v___x_2395_; size_t v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = ((size_t)1ULL);
v___x_2396_ = lean_usize_of_nat(v___x_2384_);
v___x_2397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2383_, v___x_2395_, v___x_2396_, v___x_2388_);
return v___x_2397_;
}
}
}
else
{
lean_object* v___x_2398_; 
v___x_2398_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
return v___x_2398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs___boxed(lean_object* v_ors_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_ors_2399_);
lean_dec_ref(v_ors_2399_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_ofClauses(lean_object* v_clauses_2401_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_clauses_2401_);
v___x_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v_clauses_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_appendRange(lean_object* v_ands_2404_, lean_object* v_minVer_2405_, lean_object* v_maxVer_2406_, lean_object* v_specialDescr_2407_){
_start:
{
lean_object* v_minVer_2408_; lean_object* v___x_2409_; lean_object* v_maxVer_2410_; uint8_t v___x_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_minVer_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2408_, 0, v_minVer_2405_);
lean_ctor_set(v_minVer_2408_, 1, v_specialDescr_2407_);
v___x_2409_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2410_, 0, v_maxVer_2406_);
lean_ctor_set(v_maxVer_2410_, 1, v___x_2409_);
v___x_2411_ = 3;
v___x_2412_ = 0;
v___x_2413_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2413_, 0, v_minVer_2408_);
lean_ctor_set_uint8(v___x_2413_, sizeof(void*)*1, v___x_2411_);
lean_ctor_set_uint8(v___x_2413_, sizeof(void*)*1 + 1, v___x_2412_);
v___x_2414_ = lean_array_push(v_ands_2404_, v___x_2413_);
v___x_2415_ = 0;
v___x_2416_ = 1;
v___x_2417_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2417_, 0, v_maxVer_2410_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*1, v___x_2415_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*1 + 1, v___x_2416_);
v___x_2418_ = lean_array_push(v___x_2414_, v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(lean_object* v_s_2421_, lean_object* v_ands_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v_a_2427_; lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2599_; 
v___x_2424_ = lean_unsigned_to_nat(0u);
v___x_2425_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2423_);
lean_inc_ref(v_s_2421_);
v___x_2426_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2421_, v___x_2425_, v_a_2423_, v_a_2423_);
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_a_2428_ = lean_ctor_get(v___x_2426_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2430_ = v___x_2426_;
v_isShared_2431_ = v_isSharedCheck_2599_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2599_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; 
v___x_2432_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2421_, v_a_2428_);
lean_dec_ref(v_s_2421_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2589_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_a_2434_ = lean_ctor_get(v___x_2432_, 1);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2436_ = v___x_2432_;
v_isShared_2437_ = v_isSharedCheck_2589_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2589_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2438_ = lean_array_get_size(v_a_2427_);
v___x_2439_ = lean_unsigned_to_nat(1u);
v___x_2440_ = lean_nat_dec_eq(v___x_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; uint8_t v___x_2442_; 
v___x_2441_ = lean_unsigned_to_nat(2u);
v___x_2442_ = lean_nat_dec_eq(v___x_2438_, v___x_2441_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2443_ = lean_unsigned_to_nat(3u);
v___x_2444_ = lean_nat_dec_eq(v___x_2438_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
lean_dec(v_a_2433_);
lean_del_object(v___x_2430_);
lean_dec(v_a_2427_);
lean_dec_ref(v_ands_2422_);
v___x_2445_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0));
v___x_2446_ = l_Nat_reprFast(v___x_2438_);
v___x_2447_ = lean_string_append(v___x_2445_, v___x_2446_);
lean_dec_ref(v___x_2446_);
v___x_2448_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2449_ = lean_string_append(v___x_2447_, v___x_2448_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 1);
lean_ctor_set(v___x_2436_, 0, v___x_2449_);
v___x_2451_ = v___x_2436_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_a_2434_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_array_fget_borrowed(v_a_2427_, v___x_2424_);
v___x_2454_ = l_String_Slice_toNat_x3f(v___x_2453_);
if (lean_obj_tag(v___x_2454_) == 1)
{
lean_object* v_val_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_val_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_val_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v___x_2456_ = lean_array_fget_borrowed(v_a_2427_, v___x_2439_);
v___x_2457_ = l_String_Slice_toNat_x3f(v___x_2456_);
if (lean_obj_tag(v___x_2457_) == 1)
{
lean_object* v_val_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_val_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_val_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = lean_array_fget(v_a_2427_, v___x_2441_);
lean_dec(v_a_2427_);
v___x_2460_ = l_String_Slice_toNat_x3f(v___x_2459_);
if (lean_obj_tag(v___x_2460_) == 1)
{
lean_object* v_val_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v_minVer_2466_; 
lean_dec(v___x_2459_);
v_val_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_val_2461_);
lean_dec_ref_known(v___x_2460_, 1);
lean_inc(v_val_2458_);
lean_inc(v_val_2455_);
v___x_2462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2462_, 0, v_val_2455_);
lean_ctor_set(v___x_2462_, 1, v_val_2458_);
lean_ctor_set(v___x_2462_, 2, v_val_2461_);
v___x_2463_ = lean_nat_add(v_val_2458_, v___x_2439_);
lean_dec(v_val_2458_);
v___x_2464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2464_, 0, v_val_2455_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
lean_ctor_set(v___x_2464_, 2, v___x_2424_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 1, v_a_2433_);
lean_ctor_set(v___x_2430_, 0, v___x_2462_);
v_minVer_2466_ = v___x_2430_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_a_2433_);
v_minVer_2466_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v_maxVer_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2467_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2468_, 0, v___x_2464_);
lean_ctor_set(v_maxVer_2468_, 1, v___x_2467_);
v___x_2469_ = 3;
v___x_2470_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2470_, 0, v_minVer_2466_);
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*1, v___x_2469_);
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*1 + 1, v___x_2442_);
v___x_2471_ = lean_array_push(v_ands_2422_, v___x_2470_);
v___x_2472_ = 0;
v___x_2473_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2473_, 0, v_maxVer_2468_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*1, v___x_2472_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*1 + 1, v___x_2444_);
v___x_2474_ = lean_array_push(v___x_2471_, v___x_2473_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2474_);
v___x_2476_ = v___x_2436_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_a_2434_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
else
{
lean_object* v_str_2479_; lean_object* v_startInclusive_2480_; lean_object* v_endExclusive_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
lean_dec(v___x_2460_);
lean_dec(v_val_2458_);
lean_dec(v_val_2455_);
lean_dec(v_a_2433_);
lean_del_object(v___x_2430_);
lean_dec_ref(v_ands_2422_);
v_str_2479_ = lean_ctor_get(v___x_2459_, 0);
lean_inc_ref(v_str_2479_);
v_startInclusive_2480_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_startInclusive_2480_);
v_endExclusive_2481_ = lean_ctor_get(v___x_2459_, 2);
lean_inc(v_endExclusive_2481_);
lean_dec(v___x_2459_);
v___x_2482_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2483_ = lean_string_utf8_extract(v_str_2479_, v_startInclusive_2480_, v_endExclusive_2481_);
lean_dec(v_endExclusive_2481_);
lean_dec(v_startInclusive_2480_);
lean_dec_ref(v_str_2479_);
v___x_2484_ = lean_string_append(v___x_2482_, v___x_2483_);
lean_dec_ref(v___x_2483_);
v___x_2485_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2486_ = lean_string_append(v___x_2484_, v___x_2485_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 1);
lean_ctor_set(v___x_2436_, 0, v___x_2486_);
v___x_2488_ = v___x_2436_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_a_2434_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
else
{
lean_object* v_str_2490_; lean_object* v_startInclusive_2491_; lean_object* v_endExclusive_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
lean_inc(v___x_2456_);
lean_dec(v___x_2457_);
lean_dec(v_val_2455_);
lean_dec(v_a_2433_);
lean_del_object(v___x_2430_);
lean_dec(v_a_2427_);
lean_dec_ref(v_ands_2422_);
v_str_2490_ = lean_ctor_get(v___x_2456_, 0);
lean_inc_ref(v_str_2490_);
v_startInclusive_2491_ = lean_ctor_get(v___x_2456_, 1);
lean_inc(v_startInclusive_2491_);
v_endExclusive_2492_ = lean_ctor_get(v___x_2456_, 2);
lean_inc(v_endExclusive_2492_);
lean_dec(v___x_2456_);
v___x_2493_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2494_ = lean_string_utf8_extract(v_str_2490_, v_startInclusive_2491_, v_endExclusive_2492_);
lean_dec(v_endExclusive_2492_);
lean_dec(v_startInclusive_2491_);
lean_dec_ref(v_str_2490_);
v___x_2495_ = lean_string_append(v___x_2493_, v___x_2494_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2497_ = lean_string_append(v___x_2495_, v___x_2496_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 1);
lean_ctor_set(v___x_2436_, 0, v___x_2497_);
v___x_2499_ = v___x_2436_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_a_2434_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
else
{
lean_object* v_str_2501_; lean_object* v_startInclusive_2502_; lean_object* v_endExclusive_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2510_; 
lean_inc(v___x_2453_);
lean_dec(v___x_2454_);
lean_dec(v_a_2433_);
lean_del_object(v___x_2430_);
lean_dec(v_a_2427_);
lean_dec_ref(v_ands_2422_);
v_str_2501_ = lean_ctor_get(v___x_2453_, 0);
lean_inc_ref(v_str_2501_);
v_startInclusive_2502_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_startInclusive_2502_);
v_endExclusive_2503_ = lean_ctor_get(v___x_2453_, 2);
lean_inc(v_endExclusive_2503_);
lean_dec(v___x_2453_);
v___x_2504_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2505_ = lean_string_utf8_extract(v_str_2501_, v_startInclusive_2502_, v_endExclusive_2503_);
lean_dec(v_endExclusive_2503_);
lean_dec(v_startInclusive_2502_);
lean_dec_ref(v_str_2501_);
v___x_2506_ = lean_string_append(v___x_2504_, v___x_2505_);
lean_dec_ref(v___x_2505_);
v___x_2507_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2508_ = lean_string_append(v___x_2506_, v___x_2507_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 1);
lean_ctor_set(v___x_2436_, 0, v___x_2508_);
v___x_2510_ = v___x_2436_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_a_2434_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_array_fget_borrowed(v_a_2427_, v___x_2424_);
v___x_2513_ = l_String_Slice_toNat_x3f(v___x_2512_);
if (lean_obj_tag(v___x_2513_) == 1)
{
lean_object* v_val_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_val_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2515_ = lean_array_fget(v_a_2427_, v___x_2439_);
lean_dec(v_a_2427_);
v___x_2516_ = l_String_Slice_toNat_x3f(v___x_2515_);
if (lean_obj_tag(v___x_2516_) == 1)
{
lean_object* v_val_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v_minVer_2522_; 
lean_dec(v___x_2515_);
v_val_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc_n(v_val_2517_, 2);
lean_dec_ref_known(v___x_2516_, 1);
lean_inc(v_val_2514_);
v___x_2518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2518_, 0, v_val_2514_);
lean_ctor_set(v___x_2518_, 1, v_val_2517_);
lean_ctor_set(v___x_2518_, 2, v___x_2424_);
v___x_2519_ = lean_nat_add(v_val_2517_, v___x_2439_);
lean_dec(v_val_2517_);
v___x_2520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2520_, 0, v_val_2514_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
lean_ctor_set(v___x_2520_, 2, v___x_2424_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 1, v_a_2433_);
lean_ctor_set(v___x_2430_, 0, v___x_2518_);
v_minVer_2522_ = v___x_2430_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_a_2433_);
v_minVer_2522_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; lean_object* v_maxVer_2524_; uint8_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2523_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2524_, 0, v___x_2520_);
lean_ctor_set(v_maxVer_2524_, 1, v___x_2523_);
v___x_2525_ = 3;
v___x_2526_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2526_, 0, v_minVer_2522_);
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*1, v___x_2525_);
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*1 + 1, v___x_2440_);
v___x_2527_ = lean_array_push(v_ands_2422_, v___x_2526_);
v___x_2528_ = 0;
v___x_2529_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2529_, 0, v_maxVer_2524_);
lean_ctor_set_uint8(v___x_2529_, sizeof(void*)*1, v___x_2528_);
lean_ctor_set_uint8(v___x_2529_, sizeof(void*)*1 + 1, v___x_2442_);
v___x_2530_ = lean_array_push(v___x_2527_, v___x_2529_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2530_);
v___x_2532_ = v___x_2436_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_a_2434_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
else
{
lean_object* v_str_2535_; lean_object* v_startInclusive_2536_; lean_object* v_endExclusive_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
lean_dec(v___x_2516_);
lean_dec(v_val_2514_);
lean_dec(v_a_2433_);
lean_del_object(v___x_2430_);
lean_dec_ref(v_ands_2422_);
v_str_2535_ = lean_ctor_get(v___x_2515_, 0);
lean_inc_ref(v_str_2535_);
v_startInclusive_2536_ = lean_ctor_get(v___x_2515_, 1);
lean_inc(v_startInclusive_2536_);
v_endExclusive_2537_ = lean_ctor_get(v___x_2515_, 2);
lean_inc(v_endExclusive_2537_);
lean_dec(v___x_2515_);
v___x_2538_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2539_ = lean_string_utf8_extract(v_str_2535_, v_startInclusive_2536_, v_endExclusive_2537_);
lean_dec(v_endExclusive_2537_);
lean_dec(v_startInclusive_2536_);
lean_dec_ref(v_str_2535_);
v___x_2540_ = lean_string_append(v___x_2538_, v___x_2539_);
lean_dec_ref(v___x_2539_);
v___x_2541_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2542_ = lean_string_append(v___x_2540_, v___x_2541_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 1);
lean_ctor_set(v___x_2436_, 0, v___x_2542_);
v___x_2544_ = v___x_2436_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_a_2434_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
else
{
lean_object* v_str_2546_; lean_object* v_startInclusive_2547_; lean_object* v_endExclusive_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
lean_inc(v___x_2512_);
lean_dec(v___x_2513_);
lean_dec(v_a_2433_);
lean_del_object(v___x_2430_);
lean_dec(v_a_2427_);
lean_dec_ref(v_ands_2422_);
v_str_2546_ = lean_ctor_get(v___x_2512_, 0);
lean_inc_ref(v_str_2546_);
v_startInclusive_2547_ = lean_ctor_get(v___x_2512_, 1);
lean_inc(v_startInclusive_2547_);
v_endExclusive_2548_ = lean_ctor_get(v___x_2512_, 2);
lean_inc(v_endExclusive_2548_);
lean_dec(v___x_2512_);
v___x_2549_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2550_ = lean_string_utf8_extract(v_str_2546_, v_startInclusive_2547_, v_endExclusive_2548_);
lean_dec(v_endExclusive_2548_);
lean_dec(v_startInclusive_2547_);
lean_dec_ref(v_str_2546_);
v___x_2551_ = lean_string_append(v___x_2549_, v___x_2550_);
lean_dec_ref(v___x_2550_);
v___x_2552_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2553_ = lean_string_append(v___x_2551_, v___x_2552_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 1);
lean_ctor_set(v___x_2436_, 0, v___x_2553_);
v___x_2555_ = v___x_2436_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_a_2434_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_array_fget(v_a_2427_, v___x_2424_);
lean_dec(v_a_2427_);
v___x_2558_ = l_String_Slice_toNat_x3f(v___x_2557_);
if (lean_obj_tag(v___x_2558_) == 1)
{
lean_object* v_val_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_minVer_2564_; 
lean_dec(v___x_2557_);
v_val_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc_n(v_val_2559_, 2);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2560_, 0, v_val_2559_);
lean_ctor_set(v___x_2560_, 1, v___x_2424_);
lean_ctor_set(v___x_2560_, 2, v___x_2424_);
v___x_2561_ = lean_nat_add(v_val_2559_, v___x_2439_);
lean_dec(v_val_2559_);
v___x_2562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v___x_2424_);
lean_ctor_set(v___x_2562_, 2, v___x_2424_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 1, v_a_2433_);
lean_ctor_set(v___x_2430_, 0, v___x_2560_);
v_minVer_2564_ = v___x_2430_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_a_2433_);
v_minVer_2564_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2565_; lean_object* v_maxVer_2566_; uint8_t v___x_2567_; uint8_t v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2565_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2566_, 0, v___x_2562_);
lean_ctor_set(v_maxVer_2566_, 1, v___x_2565_);
v___x_2567_ = 3;
v___x_2568_ = 0;
v___x_2569_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2569_, 0, v_minVer_2564_);
lean_ctor_set_uint8(v___x_2569_, sizeof(void*)*1, v___x_2567_);
lean_ctor_set_uint8(v___x_2569_, sizeof(void*)*1 + 1, v___x_2568_);
v___x_2570_ = lean_array_push(v_ands_2422_, v___x_2569_);
v___x_2571_ = 0;
v___x_2572_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2572_, 0, v_maxVer_2566_);
lean_ctor_set_uint8(v___x_2572_, sizeof(void*)*1, v___x_2571_);
lean_ctor_set_uint8(v___x_2572_, sizeof(void*)*1 + 1, v___x_2440_);
v___x_2573_ = lean_array_push(v___x_2570_, v___x_2572_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2573_);
v___x_2575_ = v___x_2436_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_a_2434_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
else
{
lean_object* v_str_2578_; lean_object* v_startInclusive_2579_; lean_object* v_endExclusive_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_dec(v___x_2558_);
lean_dec(v_a_2433_);
lean_del_object(v___x_2430_);
lean_dec_ref(v_ands_2422_);
v_str_2578_ = lean_ctor_get(v___x_2557_, 0);
lean_inc_ref(v_str_2578_);
v_startInclusive_2579_ = lean_ctor_get(v___x_2557_, 1);
lean_inc(v_startInclusive_2579_);
v_endExclusive_2580_ = lean_ctor_get(v___x_2557_, 2);
lean_inc(v_endExclusive_2580_);
lean_dec(v___x_2557_);
v___x_2581_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2582_ = lean_string_utf8_extract(v_str_2578_, v_startInclusive_2579_, v_endExclusive_2580_);
lean_dec(v_endExclusive_2580_);
lean_dec(v_startInclusive_2579_);
lean_dec_ref(v_str_2578_);
v___x_2583_ = lean_string_append(v___x_2581_, v___x_2582_);
lean_dec_ref(v___x_2582_);
v___x_2584_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2585_ = lean_string_append(v___x_2583_, v___x_2584_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 1);
lean_ctor_set(v___x_2436_, 0, v___x_2585_);
v___x_2587_ = v___x_2436_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_a_2434_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_del_object(v___x_2430_);
lean_dec(v_a_2427_);
lean_dec_ref(v_ands_2422_);
v_a_2590_ = lean_ctor_get(v___x_2432_, 0);
v_a_2591_ = lean_ctor_get(v___x_2432_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2432_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_inc(v_a_2590_);
lean_dec(v___x_2432_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2590_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(lean_object* v_s_2602_, lean_object* v_ands_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v_a_2608_; lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2831_; 
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2604_);
lean_inc_ref(v_s_2602_);
v___x_2607_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2602_, v___x_2606_, v_a_2604_, v_a_2604_);
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_a_2609_ = lean_ctor_get(v___x_2607_, 1);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2611_ = v___x_2607_;
v_isShared_2612_ = v_isSharedCheck_2831_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2831_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; 
v___x_2613_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2602_, v_a_2609_);
lean_dec_ref(v_s_2602_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2821_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_a_2615_ = lean_ctor_get(v___x_2613_, 1);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2617_ = v___x_2613_;
v_isShared_2618_ = v_isSharedCheck_2821_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2821_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2619_ = lean_array_get_size(v_a_2608_);
v___x_2620_ = lean_unsigned_to_nat(1u);
v___x_2621_ = lean_nat_dec_eq(v___x_2619_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = lean_unsigned_to_nat(2u);
v___x_2623_ = lean_nat_dec_eq(v___x_2619_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = lean_unsigned_to_nat(3u);
v___x_2625_ = lean_nat_dec_eq(v___x_2619_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
lean_dec(v_a_2614_);
lean_del_object(v___x_2611_);
lean_dec(v_a_2608_);
lean_dec_ref(v_ands_2603_);
v___x_2626_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0));
v___x_2627_ = l_Nat_reprFast(v___x_2619_);
v___x_2628_ = lean_string_append(v___x_2626_, v___x_2627_);
lean_dec_ref(v___x_2627_);
v___x_2629_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2630_ = lean_string_append(v___x_2628_, v___x_2629_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 1);
lean_ctor_set(v___x_2617_, 0, v___x_2630_);
v___x_2632_ = v___x_2617_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_a_2615_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_array_fget_borrowed(v_a_2608_, v___x_2605_);
v___x_2635_ = l_String_Slice_toNat_x3f(v___x_2634_);
if (lean_obj_tag(v___x_2635_) == 1)
{
lean_object* v_val_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_val_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_val_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = lean_array_fget_borrowed(v_a_2608_, v___x_2620_);
v___x_2638_ = l_String_Slice_toNat_x3f(v___x_2637_);
if (lean_obj_tag(v___x_2638_) == 1)
{
lean_object* v_val_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_val_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_val_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v___x_2640_ = lean_array_fget(v_a_2608_, v___x_2622_);
lean_dec(v_a_2608_);
v___x_2641_ = l_String_Slice_toNat_x3f(v___x_2640_);
if (lean_obj_tag(v___x_2641_) == 1)
{
lean_object* v_val_2642_; uint8_t v___y_2644_; uint8_t v___x_2664_; 
lean_dec(v___x_2640_);
v_val_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_val_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v___x_2664_ = lean_nat_dec_eq(v_val_2636_, v___x_2605_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v_minVer_2668_; lean_object* v___x_2669_; lean_object* v_maxVer_2670_; uint8_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
lean_del_object(v___x_2617_);
lean_inc(v_val_2636_);
v___x_2665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2665_, 0, v_val_2636_);
lean_ctor_set(v___x_2665_, 1, v_val_2639_);
lean_ctor_set(v___x_2665_, 2, v_val_2642_);
v___x_2666_ = lean_nat_add(v_val_2636_, v___x_2620_);
lean_dec(v_val_2636_);
v___x_2667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
lean_ctor_set(v___x_2667_, 1, v___x_2605_);
lean_ctor_set(v___x_2667_, 2, v___x_2605_);
v_minVer_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2668_, 0, v___x_2665_);
lean_ctor_set(v_minVer_2668_, 1, v_a_2614_);
v___x_2669_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2670_, 0, v___x_2667_);
lean_ctor_set(v_maxVer_2670_, 1, v___x_2669_);
v___x_2671_ = 3;
v___x_2672_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2672_, 0, v_minVer_2668_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*1, v___x_2671_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*1 + 1, v___x_2664_);
v___x_2673_ = lean_array_push(v_ands_2603_, v___x_2672_);
v___x_2674_ = 0;
v___x_2675_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2675_, 0, v_maxVer_2670_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*1, v___x_2674_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*1 + 1, v___x_2625_);
v___x_2676_ = lean_array_push(v___x_2673_, v___x_2675_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 1, v_a_2615_);
lean_ctor_set(v___x_2611_, 0, v___x_2676_);
v___x_2678_ = v___x_2611_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_a_2615_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
else
{
uint8_t v___x_2680_; 
v___x_2680_ = lean_nat_dec_eq(v_val_2639_, v___x_2605_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v_minVer_2684_; lean_object* v___x_2685_; lean_object* v_maxVer_2686_; uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
lean_del_object(v___x_2617_);
lean_inc(v_val_2639_);
lean_inc(v_val_2636_);
v___x_2681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2681_, 0, v_val_2636_);
lean_ctor_set(v___x_2681_, 1, v_val_2639_);
lean_ctor_set(v___x_2681_, 2, v_val_2642_);
v___x_2682_ = lean_nat_add(v_val_2639_, v___x_2620_);
lean_dec(v_val_2639_);
v___x_2683_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2683_, 0, v_val_2636_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
lean_ctor_set(v___x_2683_, 2, v___x_2605_);
v_minVer_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2684_, 0, v___x_2681_);
lean_ctor_set(v_minVer_2684_, 1, v_a_2614_);
v___x_2685_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2686_, 0, v___x_2683_);
lean_ctor_set(v_maxVer_2686_, 1, v___x_2685_);
v___x_2687_ = 3;
v___x_2688_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2688_, 0, v_minVer_2684_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*1, v___x_2687_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*1 + 1, v___x_2680_);
v___x_2689_ = lean_array_push(v_ands_2603_, v___x_2688_);
v___x_2690_ = 0;
v___x_2691_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2691_, 0, v_maxVer_2686_);
lean_ctor_set_uint8(v___x_2691_, sizeof(void*)*1, v___x_2690_);
lean_ctor_set_uint8(v___x_2691_, sizeof(void*)*1 + 1, v___x_2664_);
v___x_2692_ = lean_array_push(v___x_2689_, v___x_2691_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 1, v_a_2615_);
lean_ctor_set(v___x_2611_, 0, v___x_2692_);
v___x_2694_ = v___x_2611_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_a_2615_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
else
{
uint8_t v___x_2696_; 
lean_del_object(v___x_2611_);
v___x_2696_ = lean_nat_dec_eq(v_val_2642_, v___x_2605_);
if (v___x_2696_ == 0)
{
v___y_2644_ = v___x_2696_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2697_ = lean_string_utf8_byte_size(v_a_2614_);
v___x_2698_ = lean_nat_dec_eq(v___x_2697_, v___x_2605_);
v___y_2644_ = v___x_2698_;
goto v___jp_2643_;
}
}
}
v___jp_2643_:
{
if (v___y_2644_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v_minVer_2648_; lean_object* v___x_2649_; lean_object* v_maxVer_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_inc(v_val_2642_);
lean_inc(v_val_2639_);
lean_inc(v_val_2636_);
v___x_2645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2645_, 0, v_val_2636_);
lean_ctor_set(v___x_2645_, 1, v_val_2639_);
lean_ctor_set(v___x_2645_, 2, v_val_2642_);
v___x_2646_ = lean_nat_add(v_val_2642_, v___x_2620_);
lean_dec(v_val_2642_);
v___x_2647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2647_, 0, v_val_2636_);
lean_ctor_set(v___x_2647_, 1, v_val_2639_);
lean_ctor_set(v___x_2647_, 2, v___x_2646_);
v_minVer_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2648_, 0, v___x_2645_);
lean_ctor_set(v_minVer_2648_, 1, v_a_2614_);
v___x_2649_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2650_, 0, v___x_2647_);
lean_ctor_set(v_maxVer_2650_, 1, v___x_2649_);
v___x_2651_ = 3;
v___x_2652_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2652_, 0, v_minVer_2648_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*1, v___x_2651_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*1 + 1, v___y_2644_);
v___x_2653_ = lean_array_push(v_ands_2603_, v___x_2652_);
v___x_2654_ = 0;
v___x_2655_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2655_, 0, v_maxVer_2650_);
lean_ctor_set_uint8(v___x_2655_, sizeof(void*)*1, v___x_2654_);
lean_ctor_set_uint8(v___x_2655_, sizeof(void*)*1 + 1, v___x_2625_);
v___x_2656_ = lean_array_push(v___x_2653_, v___x_2655_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2656_);
v___x_2658_ = v___x_2617_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_a_2615_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
lean_dec(v_val_2642_);
lean_dec(v_val_2639_);
lean_dec(v_val_2636_);
lean_dec(v_a_2614_);
lean_dec_ref(v_ands_2603_);
v___x_2660_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1));
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 1);
lean_ctor_set(v___x_2617_, 0, v___x_2660_);
v___x_2662_ = v___x_2617_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_a_2615_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
else
{
lean_object* v_str_2699_; lean_object* v_startInclusive_2700_; lean_object* v_endExclusive_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
lean_dec(v___x_2641_);
lean_dec(v_val_2639_);
lean_dec(v_val_2636_);
lean_dec(v_a_2614_);
lean_del_object(v___x_2611_);
lean_dec_ref(v_ands_2603_);
v_str_2699_ = lean_ctor_get(v___x_2640_, 0);
lean_inc_ref(v_str_2699_);
v_startInclusive_2700_ = lean_ctor_get(v___x_2640_, 1);
lean_inc(v_startInclusive_2700_);
v_endExclusive_2701_ = lean_ctor_get(v___x_2640_, 2);
lean_inc(v_endExclusive_2701_);
lean_dec(v___x_2640_);
v___x_2702_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2703_ = lean_string_utf8_extract(v_str_2699_, v_startInclusive_2700_, v_endExclusive_2701_);
lean_dec(v_endExclusive_2701_);
lean_dec(v_startInclusive_2700_);
lean_dec_ref(v_str_2699_);
v___x_2704_ = lean_string_append(v___x_2702_, v___x_2703_);
lean_dec_ref(v___x_2703_);
v___x_2705_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2706_ = lean_string_append(v___x_2704_, v___x_2705_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 1);
lean_ctor_set(v___x_2617_, 0, v___x_2706_);
v___x_2708_ = v___x_2617_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_a_2615_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
else
{
lean_object* v_str_2710_; lean_object* v_startInclusive_2711_; lean_object* v_endExclusive_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
lean_inc(v___x_2637_);
lean_dec(v___x_2638_);
lean_dec(v_val_2636_);
lean_dec(v_a_2614_);
lean_del_object(v___x_2611_);
lean_dec(v_a_2608_);
lean_dec_ref(v_ands_2603_);
v_str_2710_ = lean_ctor_get(v___x_2637_, 0);
lean_inc_ref(v_str_2710_);
v_startInclusive_2711_ = lean_ctor_get(v___x_2637_, 1);
lean_inc(v_startInclusive_2711_);
v_endExclusive_2712_ = lean_ctor_get(v___x_2637_, 2);
lean_inc(v_endExclusive_2712_);
lean_dec(v___x_2637_);
v___x_2713_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2714_ = lean_string_utf8_extract(v_str_2710_, v_startInclusive_2711_, v_endExclusive_2712_);
lean_dec(v_endExclusive_2712_);
lean_dec(v_startInclusive_2711_);
lean_dec_ref(v_str_2710_);
v___x_2715_ = lean_string_append(v___x_2713_, v___x_2714_);
lean_dec_ref(v___x_2714_);
v___x_2716_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2717_ = lean_string_append(v___x_2715_, v___x_2716_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 1);
lean_ctor_set(v___x_2617_, 0, v___x_2717_);
v___x_2719_ = v___x_2617_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2717_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_a_2615_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
else
{
lean_object* v_str_2721_; lean_object* v_startInclusive_2722_; lean_object* v_endExclusive_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
lean_inc(v___x_2634_);
lean_dec(v___x_2635_);
lean_dec(v_a_2614_);
lean_del_object(v___x_2611_);
lean_dec(v_a_2608_);
lean_dec_ref(v_ands_2603_);
v_str_2721_ = lean_ctor_get(v___x_2634_, 0);
lean_inc_ref(v_str_2721_);
v_startInclusive_2722_ = lean_ctor_get(v___x_2634_, 1);
lean_inc(v_startInclusive_2722_);
v_endExclusive_2723_ = lean_ctor_get(v___x_2634_, 2);
lean_inc(v_endExclusive_2723_);
lean_dec(v___x_2634_);
v___x_2724_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2725_ = lean_string_utf8_extract(v_str_2721_, v_startInclusive_2722_, v_endExclusive_2723_);
lean_dec(v_endExclusive_2723_);
lean_dec(v_startInclusive_2722_);
lean_dec_ref(v_str_2721_);
v___x_2726_ = lean_string_append(v___x_2724_, v___x_2725_);
lean_dec_ref(v___x_2725_);
v___x_2727_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2728_ = lean_string_append(v___x_2726_, v___x_2727_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 1);
lean_ctor_set(v___x_2617_, 0, v___x_2728_);
v___x_2730_ = v___x_2617_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_a_2615_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_del_object(v___x_2611_);
v___x_2732_ = lean_array_fget_borrowed(v_a_2608_, v___x_2605_);
v___x_2733_ = l_String_Slice_toNat_x3f(v___x_2732_);
if (lean_obj_tag(v___x_2733_) == 1)
{
lean_object* v_val_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_val_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_val_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2735_ = lean_array_fget(v_a_2608_, v___x_2620_);
lean_dec(v_a_2608_);
v___x_2736_ = l_String_Slice_toNat_x3f(v___x_2735_);
if (lean_obj_tag(v___x_2736_) == 1)
{
lean_object* v_val_2737_; uint8_t v___x_2738_; 
lean_dec(v___x_2735_);
v_val_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_val_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = lean_nat_dec_eq(v_val_2734_, v___x_2605_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v_minVer_2742_; lean_object* v___x_2743_; lean_object* v_maxVer_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
lean_inc(v_val_2734_);
v___x_2739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2739_, 0, v_val_2734_);
lean_ctor_set(v___x_2739_, 1, v_val_2737_);
lean_ctor_set(v___x_2739_, 2, v___x_2605_);
v___x_2740_ = lean_nat_add(v_val_2734_, v___x_2620_);
lean_dec(v_val_2734_);
v___x_2741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v___x_2605_);
lean_ctor_set(v___x_2741_, 2, v___x_2605_);
v_minVer_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2742_, 0, v___x_2739_);
lean_ctor_set(v_minVer_2742_, 1, v_a_2614_);
v___x_2743_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2744_, 0, v___x_2741_);
lean_ctor_set(v_maxVer_2744_, 1, v___x_2743_);
v___x_2745_ = 3;
v___x_2746_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2746_, 0, v_minVer_2742_);
lean_ctor_set_uint8(v___x_2746_, sizeof(void*)*1, v___x_2745_);
lean_ctor_set_uint8(v___x_2746_, sizeof(void*)*1 + 1, v___x_2738_);
v___x_2747_ = lean_array_push(v_ands_2603_, v___x_2746_);
v___x_2748_ = 0;
v___x_2749_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2749_, 0, v_maxVer_2744_);
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*1, v___x_2748_);
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*1 + 1, v___x_2623_);
v___x_2750_ = lean_array_push(v___x_2747_, v___x_2749_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2750_);
v___x_2752_ = v___x_2617_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_a_2615_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
else
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v_minVer_2757_; lean_object* v___x_2758_; lean_object* v_maxVer_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
lean_inc(v_val_2737_);
lean_inc(v_val_2734_);
v___x_2754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2754_, 0, v_val_2734_);
lean_ctor_set(v___x_2754_, 1, v_val_2737_);
lean_ctor_set(v___x_2754_, 2, v___x_2605_);
v___x_2755_ = lean_nat_add(v_val_2737_, v___x_2620_);
lean_dec(v_val_2737_);
v___x_2756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2756_, 0, v_val_2734_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
lean_ctor_set(v___x_2756_, 2, v___x_2605_);
v_minVer_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2757_, 0, v___x_2754_);
lean_ctor_set(v_minVer_2757_, 1, v_a_2614_);
v___x_2758_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2759_, 0, v___x_2756_);
lean_ctor_set(v_maxVer_2759_, 1, v___x_2758_);
v___x_2760_ = 3;
v___x_2761_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2761_, 0, v_minVer_2757_);
lean_ctor_set_uint8(v___x_2761_, sizeof(void*)*1, v___x_2760_);
lean_ctor_set_uint8(v___x_2761_, sizeof(void*)*1 + 1, v___x_2621_);
v___x_2762_ = lean_array_push(v_ands_2603_, v___x_2761_);
v___x_2763_ = 0;
v___x_2764_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2764_, 0, v_maxVer_2759_);
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*1, v___x_2763_);
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*1 + 1, v___x_2738_);
v___x_2765_ = lean_array_push(v___x_2762_, v___x_2764_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2765_);
v___x_2767_ = v___x_2617_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_a_2615_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
else
{
lean_object* v_str_2769_; lean_object* v_startInclusive_2770_; lean_object* v_endExclusive_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
lean_dec(v___x_2736_);
lean_dec(v_val_2734_);
lean_dec(v_a_2614_);
lean_dec_ref(v_ands_2603_);
v_str_2769_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_ref(v_str_2769_);
v_startInclusive_2770_ = lean_ctor_get(v___x_2735_, 1);
lean_inc(v_startInclusive_2770_);
v_endExclusive_2771_ = lean_ctor_get(v___x_2735_, 2);
lean_inc(v_endExclusive_2771_);
lean_dec(v___x_2735_);
v___x_2772_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2773_ = lean_string_utf8_extract(v_str_2769_, v_startInclusive_2770_, v_endExclusive_2771_);
lean_dec(v_endExclusive_2771_);
lean_dec(v_startInclusive_2770_);
lean_dec_ref(v_str_2769_);
v___x_2774_ = lean_string_append(v___x_2772_, v___x_2773_);
lean_dec_ref(v___x_2773_);
v___x_2775_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2776_ = lean_string_append(v___x_2774_, v___x_2775_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 1);
lean_ctor_set(v___x_2617_, 0, v___x_2776_);
v___x_2778_ = v___x_2617_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_a_2615_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
else
{
lean_object* v_str_2780_; lean_object* v_startInclusive_2781_; lean_object* v_endExclusive_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
lean_inc(v___x_2732_);
lean_dec(v___x_2733_);
lean_dec(v_a_2614_);
lean_dec(v_a_2608_);
lean_dec_ref(v_ands_2603_);
v_str_2780_ = lean_ctor_get(v___x_2732_, 0);
lean_inc_ref(v_str_2780_);
v_startInclusive_2781_ = lean_ctor_get(v___x_2732_, 1);
lean_inc(v_startInclusive_2781_);
v_endExclusive_2782_ = lean_ctor_get(v___x_2732_, 2);
lean_inc(v_endExclusive_2782_);
lean_dec(v___x_2732_);
v___x_2783_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2784_ = lean_string_utf8_extract(v_str_2780_, v_startInclusive_2781_, v_endExclusive_2782_);
lean_dec(v_endExclusive_2782_);
lean_dec(v_startInclusive_2781_);
lean_dec_ref(v_str_2780_);
v___x_2785_ = lean_string_append(v___x_2783_, v___x_2784_);
lean_dec_ref(v___x_2784_);
v___x_2786_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2787_ = lean_string_append(v___x_2785_, v___x_2786_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 1);
lean_ctor_set(v___x_2617_, 0, v___x_2787_);
v___x_2789_ = v___x_2617_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_a_2615_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_del_object(v___x_2611_);
v___x_2791_ = lean_array_fget(v_a_2608_, v___x_2605_);
lean_dec(v_a_2608_);
v___x_2792_ = l_String_Slice_toNat_x3f(v___x_2791_);
if (lean_obj_tag(v___x_2792_) == 1)
{
lean_object* v_val_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v_minVer_2797_; lean_object* v___x_2798_; lean_object* v_maxVer_2799_; uint8_t v___x_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
lean_dec(v___x_2791_);
v_val_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc_n(v_val_2793_, 2);
lean_dec_ref_known(v___x_2792_, 1);
v___x_2794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2794_, 0, v_val_2793_);
lean_ctor_set(v___x_2794_, 1, v___x_2605_);
lean_ctor_set(v___x_2794_, 2, v___x_2605_);
v___x_2795_ = lean_nat_add(v_val_2793_, v___x_2620_);
lean_dec(v_val_2793_);
v___x_2796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___x_2605_);
lean_ctor_set(v___x_2796_, 2, v___x_2605_);
v_minVer_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2797_, 0, v___x_2794_);
lean_ctor_set(v_minVer_2797_, 1, v_a_2614_);
v___x_2798_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2799_, 0, v___x_2796_);
lean_ctor_set(v_maxVer_2799_, 1, v___x_2798_);
v___x_2800_ = 3;
v___x_2801_ = 0;
v___x_2802_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2802_, 0, v_minVer_2797_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*1, v___x_2800_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*1 + 1, v___x_2801_);
v___x_2803_ = lean_array_push(v_ands_2603_, v___x_2802_);
v___x_2804_ = 0;
v___x_2805_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2805_, 0, v_maxVer_2799_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1, v___x_2804_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1 + 1, v___x_2621_);
v___x_2806_ = lean_array_push(v___x_2803_, v___x_2805_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2806_);
v___x_2808_ = v___x_2617_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_a_2615_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
else
{
lean_object* v_str_2810_; lean_object* v_startInclusive_2811_; lean_object* v_endExclusive_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
lean_dec(v___x_2792_);
lean_dec(v_a_2614_);
lean_dec_ref(v_ands_2603_);
v_str_2810_ = lean_ctor_get(v___x_2791_, 0);
lean_inc_ref(v_str_2810_);
v_startInclusive_2811_ = lean_ctor_get(v___x_2791_, 1);
lean_inc(v_startInclusive_2811_);
v_endExclusive_2812_ = lean_ctor_get(v___x_2791_, 2);
lean_inc(v_endExclusive_2812_);
lean_dec(v___x_2791_);
v___x_2813_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2814_ = lean_string_utf8_extract(v_str_2810_, v_startInclusive_2811_, v_endExclusive_2812_);
lean_dec(v_endExclusive_2812_);
lean_dec(v_startInclusive_2811_);
lean_dec_ref(v_str_2810_);
v___x_2815_ = lean_string_append(v___x_2813_, v___x_2814_);
lean_dec_ref(v___x_2814_);
v___x_2816_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2817_ = lean_string_append(v___x_2815_, v___x_2816_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 1);
lean_ctor_set(v___x_2617_, 0, v___x_2817_);
v___x_2819_ = v___x_2617_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v_a_2615_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_del_object(v___x_2611_);
lean_dec(v_a_2608_);
lean_dec_ref(v_ands_2603_);
v_a_2822_ = lean_ctor_get(v___x_2613_, 0);
v_a_2823_ = lean_ctor_get(v___x_2613_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2613_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_inc(v_a_2822_);
lean_dec(v___x_2613_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2822_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(lean_object* v_s_2837_, lean_object* v_ands_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v___y_2841_; lean_object* v___y_2845_; lean_object* v___y_2850_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v_a_2856_; lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_3005_; 
v___x_2853_ = lean_unsigned_to_nat(0u);
v___x_2854_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2839_);
lean_inc_ref(v_s_2837_);
v___x_2855_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2837_, v___x_2854_, v_a_2839_, v_a_2839_);
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
v_a_2857_ = lean_ctor_get(v___x_2855_, 1);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2859_ = v___x_2855_;
v_isShared_2860_ = v_isSharedCheck_3005_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_inc(v_a_2856_);
lean_dec(v___x_2855_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_3005_;
goto v_resetjp_2858_;
}
v___jp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0));
v___x_2843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
lean_ctor_set(v___x_2843_, 1, v___y_2841_);
return v___x_2843_;
}
v___jp_2844_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2846_ = ((lean_object*)(l_Lake_VerComparator_wild));
v___x_2847_ = lean_array_push(v_ands_2838_, v___x_2846_);
v___x_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
lean_ctor_set(v___x_2848_, 1, v___y_2845_);
return v___x_2848_;
}
v___jp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1));
v___x_2852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v___y_2850_);
return v___x_2852_;
}
v_resetjp_2858_:
{
lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; uint8_t v___y_2867_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___x_2978_; lean_object* v___y_2980_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_2978_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__1));
v___x_3000_ = lean_array_get_size(v_a_2856_);
v___x_3001_ = lean_nat_dec_lt(v___x_2853_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_box(0);
v___y_2980_ = v___x_3002_;
goto v___jp_2979_;
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_array_fget_borrowed(v_a_2856_, v___x_2853_);
lean_inc(v___x_3003_);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
v___y_2980_ = v___x_3004_;
goto v___jp_2979_;
}
v___jp_2861_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2868_ = lean_unsigned_to_nat(3u);
v___x_2869_ = lean_array_get_size(v_a_2856_);
lean_dec(v_a_2856_);
v___x_2870_ = lean_nat_dec_lt(v___x_2868_, v___x_2869_);
if (v___x_2870_ == 0)
{
switch(lean_obj_tag(v___y_2863_))
{
case 2:
{
switch(lean_obj_tag(v___y_2866_))
{
case 2:
{
if (lean_obj_tag(v___y_2862_) == 1)
{
lean_object* v_n_2871_; lean_object* v_n_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v_minVer_2877_; lean_object* v_maxVer_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; uint8_t v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v_n_2871_ = lean_ctor_get(v___y_2863_, 0);
lean_inc_n(v_n_2871_, 2);
lean_dec_ref_known(v___y_2863_, 1);
v_n_2872_ = lean_ctor_get(v___y_2866_, 0);
lean_inc_n(v_n_2872_, 2);
lean_dec_ref_known(v___y_2866_, 1);
v___x_2873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2873_, 0, v_n_2871_);
lean_ctor_set(v___x_2873_, 1, v_n_2872_);
lean_ctor_set(v___x_2873_, 2, v___x_2853_);
v___x_2874_ = lean_nat_add(v_n_2872_, v___y_2865_);
lean_dec(v_n_2872_);
v___x_2875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2875_, 0, v_n_2871_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
lean_ctor_set(v___x_2875_, 2, v___x_2853_);
v___x_2876_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2877_, 0, v___x_2873_);
lean_ctor_set(v_minVer_2877_, 1, v___x_2876_);
v_maxVer_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2878_, 0, v___x_2875_);
lean_ctor_set(v_maxVer_2878_, 1, v___x_2876_);
v___x_2879_ = 3;
v___x_2880_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2880_, 0, v_minVer_2877_);
lean_ctor_set_uint8(v___x_2880_, sizeof(void*)*1, v___x_2879_);
lean_ctor_set_uint8(v___x_2880_, sizeof(void*)*1 + 1, v___y_2867_);
v___x_2881_ = lean_array_push(v_ands_2838_, v___x_2880_);
v___x_2882_ = 0;
v___x_2883_ = 1;
v___x_2884_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2884_, 0, v_maxVer_2878_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*1, v___x_2882_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*1 + 1, v___x_2883_);
v___x_2885_ = lean_array_push(v___x_2881_, v___x_2884_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v___y_2864_);
lean_ctor_set(v___x_2859_, 0, v___x_2885_);
v___x_2887_ = v___x_2859_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v___y_2864_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
else
{
lean_dec_ref_known(v___y_2866_, 1);
lean_dec_ref_known(v___y_2863_, 1);
lean_dec(v___y_2862_);
lean_del_object(v___x_2859_);
lean_dec_ref(v_ands_2838_);
v___y_2850_ = v___y_2864_;
goto v___jp_2849_;
}
}
case 1:
{
if (lean_obj_tag(v___y_2862_) == 2)
{
lean_dec_ref_known(v___y_2862_, 1);
lean_dec_ref_known(v___y_2863_, 1);
lean_del_object(v___x_2859_);
lean_dec_ref(v_ands_2838_);
v___y_2841_ = v___y_2864_;
goto v___jp_2840_;
}
else
{
lean_object* v_n_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v_minVer_2894_; lean_object* v_maxVer_2895_; uint8_t v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
lean_dec(v___y_2862_);
v_n_2889_ = lean_ctor_get(v___y_2863_, 0);
lean_inc_n(v_n_2889_, 2);
lean_dec_ref_known(v___y_2863_, 1);
v___x_2890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2890_, 0, v_n_2889_);
lean_ctor_set(v___x_2890_, 1, v___x_2853_);
lean_ctor_set(v___x_2890_, 2, v___x_2853_);
v___x_2891_ = lean_nat_add(v_n_2889_, v___y_2865_);
lean_dec(v_n_2889_);
v___x_2892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
lean_ctor_set(v___x_2892_, 1, v___x_2853_);
lean_ctor_set(v___x_2892_, 2, v___x_2853_);
v___x_2893_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2894_, 0, v___x_2890_);
lean_ctor_set(v_minVer_2894_, 1, v___x_2893_);
v_maxVer_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2895_, 0, v___x_2892_);
lean_ctor_set(v_maxVer_2895_, 1, v___x_2893_);
v___x_2896_ = 3;
v___x_2897_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2897_, 0, v_minVer_2894_);
lean_ctor_set_uint8(v___x_2897_, sizeof(void*)*1, v___x_2896_);
lean_ctor_set_uint8(v___x_2897_, sizeof(void*)*1 + 1, v___y_2867_);
v___x_2898_ = lean_array_push(v_ands_2838_, v___x_2897_);
v___x_2899_ = 0;
v___x_2900_ = 1;
v___x_2901_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2901_, 0, v_maxVer_2895_);
lean_ctor_set_uint8(v___x_2901_, sizeof(void*)*1, v___x_2899_);
lean_ctor_set_uint8(v___x_2901_, sizeof(void*)*1 + 1, v___x_2900_);
v___x_2902_ = lean_array_push(v___x_2898_, v___x_2901_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v___y_2864_);
lean_ctor_set(v___x_2859_, 0, v___x_2902_);
v___x_2904_ = v___x_2859_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v___y_2864_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
default: 
{
lean_dec_ref_known(v___y_2863_, 1);
lean_dec(v___y_2866_);
lean_dec(v___y_2862_);
lean_del_object(v___x_2859_);
lean_dec_ref(v_ands_2838_);
v___y_2850_ = v___y_2864_;
goto v___jp_2849_;
}
}
}
case 1:
{
if (lean_obj_tag(v___y_2862_) == 2)
{
lean_dec_ref_known(v___y_2862_, 1);
lean_dec(v___y_2866_);
lean_del_object(v___x_2859_);
lean_dec_ref(v_ands_2838_);
v___y_2841_ = v___y_2864_;
goto v___jp_2840_;
}
else
{
lean_dec(v___y_2862_);
if (lean_obj_tag(v___y_2866_) == 2)
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
lean_dec_ref_known(v___y_2866_, 1);
lean_dec_ref(v_ands_2838_);
v___x_2906_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2));
if (v_isShared_2860_ == 0)
{
lean_ctor_set_tag(v___x_2859_, 1);
lean_ctor_set(v___x_2859_, 1, v___y_2864_);
lean_ctor_set(v___x_2859_, 0, v___x_2906_);
v___x_2908_ = v___x_2859_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v___y_2864_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
else
{
lean_dec(v___y_2866_);
lean_del_object(v___x_2859_);
v___y_2845_ = v___y_2864_;
goto v___jp_2844_;
}
}
}
default: 
{
lean_dec(v___y_2863_);
lean_del_object(v___x_2859_);
if (lean_obj_tag(v___y_2866_) == 1)
{
if (lean_obj_tag(v___y_2862_) == 2)
{
lean_dec_ref_known(v___y_2862_, 1);
lean_dec_ref(v_ands_2838_);
v___y_2841_ = v___y_2864_;
goto v___jp_2840_;
}
else
{
lean_dec(v___y_2862_);
v___y_2845_ = v___y_2864_;
goto v___jp_2844_;
}
}
else
{
lean_dec(v___y_2866_);
lean_dec(v___y_2862_);
v___y_2845_ = v___y_2864_;
goto v___jp_2844_;
}
}
}
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
lean_dec(v___y_2866_);
lean_dec(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v_ands_2838_);
v___x_2910_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3));
v___x_2911_ = l_Nat_reprFast(v___x_2869_);
v___x_2912_ = lean_string_append(v___x_2910_, v___x_2911_);
lean_dec_ref(v___x_2911_);
v___x_2913_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2914_ = lean_string_append(v___x_2912_, v___x_2913_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set_tag(v___x_2859_, 1);
lean_ctor_set(v___x_2859_, 1, v___y_2864_);
lean_ctor_set(v___x_2859_, 0, v___x_2914_);
v___x_2916_ = v___x_2859_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v___y_2864_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
v___jp_2918_:
{
lean_object* v___x_2925_; 
v___x_2925_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2921_, v___y_2924_, v___y_2920_);
lean_dec(v___y_2924_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2943_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
v_a_2927_ = lean_ctor_get(v___x_2925_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2929_ = v___x_2925_;
v_isShared_2930_ = v_isSharedCheck_2943_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_inc(v_a_2926_);
lean_dec(v___x_2925_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2943_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = lean_string_utf8_byte_size(v_s_2837_);
v___x_2932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2932_, 0, v_s_2837_);
lean_ctor_set(v___x_2932_, 1, v___x_2853_);
lean_ctor_set(v___x_2932_, 2, v___x_2931_);
v___x_2933_ = l_String_Slice_Pos_get_x3f(v___x_2932_, v_a_2927_);
lean_dec_ref_known(v___x_2932_, 3);
if (lean_obj_tag(v___x_2933_) == 0)
{
uint8_t v___x_2934_; 
lean_del_object(v___x_2929_);
v___x_2934_ = 0;
v___y_2862_ = v_a_2926_;
v___y_2863_ = v___y_2919_;
v___y_2864_ = v_a_2927_;
v___y_2865_ = v___y_2922_;
v___y_2866_ = v___y_2923_;
v___y_2867_ = v___x_2934_;
goto v___jp_2861_;
}
else
{
lean_object* v_val_2935_; uint32_t v___x_2936_; uint32_t v___x_2937_; uint8_t v___x_2938_; 
v_val_2935_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_val_2935_);
lean_dec_ref_known(v___x_2933_, 1);
v___x_2936_ = 45;
v___x_2937_ = lean_unbox_uint32(v_val_2935_);
lean_dec(v_val_2935_);
v___x_2938_ = lean_uint32_dec_eq(v___x_2937_, v___x_2936_);
if (v___x_2938_ == 0)
{
lean_del_object(v___x_2929_);
v___y_2862_ = v_a_2926_;
v___y_2863_ = v___y_2919_;
v___y_2864_ = v_a_2927_;
v___y_2865_ = v___y_2922_;
v___y_2866_ = v___y_2923_;
v___y_2867_ = v___x_2938_;
goto v___jp_2861_;
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
lean_dec(v_a_2926_);
lean_dec(v___y_2923_);
lean_dec(v___y_2919_);
lean_del_object(v___x_2859_);
lean_dec(v_a_2856_);
lean_dec_ref(v_ands_2838_);
v___x_2939_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4));
if (v_isShared_2930_ == 0)
{
lean_ctor_set_tag(v___x_2929_, 1);
lean_ctor_set(v___x_2929_, 0, v___x_2939_);
v___x_2941_ = v___x_2929_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_a_2927_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
else
{
lean_object* v_a_2944_; lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v___y_2923_);
lean_dec(v___y_2919_);
lean_del_object(v___x_2859_);
lean_dec(v_a_2856_);
lean_dec_ref(v_ands_2838_);
lean_dec_ref(v_s_2837_);
v_a_2944_ = lean_ctor_get(v___x_2925_, 0);
v_a_2945_ = lean_ctor_get(v___x_2925_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2925_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_inc(v_a_2944_);
lean_dec(v___x_2925_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2944_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
v___jp_2953_:
{
lean_object* v___x_2959_; 
v___x_2959_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2956_, v___y_2958_, v___y_2955_);
lean_dec(v___y_2958_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; uint8_t v___x_2965_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
v_a_2961_ = lean_ctor_get(v___x_2959_, 1);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2959_, 2);
v___x_2962_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__12));
v___x_2963_ = lean_unsigned_to_nat(2u);
v___x_2964_ = lean_array_get_size(v_a_2856_);
v___x_2965_ = lean_nat_dec_lt(v___x_2963_, v___x_2964_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_box(0);
v___y_2919_ = v___y_2954_;
v___y_2920_ = v_a_2961_;
v___y_2921_ = v___x_2962_;
v___y_2922_ = v___y_2957_;
v___y_2923_ = v_a_2960_;
v___y_2924_ = v___x_2966_;
goto v___jp_2918_;
}
else
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = lean_array_fget_borrowed(v_a_2856_, v___x_2963_);
lean_inc(v___x_2967_);
v___x_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
v___y_2919_ = v___y_2954_;
v___y_2920_ = v_a_2961_;
v___y_2921_ = v___x_2962_;
v___y_2922_ = v___y_2957_;
v___y_2923_ = v_a_2960_;
v___y_2924_ = v___x_2968_;
goto v___jp_2918_;
}
}
else
{
lean_object* v_a_2969_; lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec(v___y_2954_);
lean_del_object(v___x_2859_);
lean_dec(v_a_2856_);
lean_dec_ref(v_ands_2838_);
lean_dec_ref(v_s_2837_);
v_a_2969_ = lean_ctor_get(v___x_2959_, 0);
v_a_2970_ = lean_ctor_get(v___x_2959_, 1);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2959_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_inc(v_a_2969_);
lean_dec(v___x_2959_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2969_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
v___jp_2979_:
{
lean_object* v___x_2981_; 
v___x_2981_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___x_2978_, v___y_2980_, v_a_2857_);
lean_dec(v___y_2980_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
v_a_2983_ = lean_ctor_get(v___x_2981_, 1);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2981_, 2);
v___x_2984_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__10));
v___x_2985_ = lean_unsigned_to_nat(1u);
v___x_2986_ = lean_array_get_size(v_a_2856_);
v___x_2987_ = lean_nat_dec_lt(v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_box(0);
v___y_2954_ = v_a_2982_;
v___y_2955_ = v_a_2983_;
v___y_2956_ = v___x_2984_;
v___y_2957_ = v___x_2985_;
v___y_2958_ = v___x_2988_;
goto v___jp_2953_;
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_array_fget_borrowed(v_a_2856_, v___x_2985_);
lean_inc(v___x_2989_);
v___x_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
v___y_2954_ = v_a_2982_;
v___y_2955_ = v_a_2983_;
v___y_2956_ = v___x_2984_;
v___y_2957_ = v___x_2985_;
v___y_2958_ = v___x_2990_;
goto v___jp_2953_;
}
}
else
{
lean_object* v_a_2991_; lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_del_object(v___x_2859_);
lean_dec(v_a_2856_);
lean_dec_ref(v_ands_2838_);
lean_dec_ref(v_s_2837_);
v_a_2991_ = lean_ctor_get(v___x_2981_, 0);
v_a_2992_ = lean_ctor_get(v___x_2981_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2981_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_inc(v_a_2991_);
lean_dec(v___x_2981_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2991_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(lean_object* v_s_3012_, uint8_t v_needsRange_3013_, lean_object* v_ors_3014_, lean_object* v_ands_3015_, lean_object* v_p_3016_){
_start:
{
lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3023_ = lean_string_utf8_byte_size(v_s_3012_);
v___x_3024_ = lean_nat_dec_eq(v_p_3016_, v___x_3023_);
if (v___x_3024_ == 0)
{
uint32_t v_c_3039_; uint8_t v___y_3041_; uint8_t v___y_3042_; uint8_t v___y_3083_; uint8_t v___y_3084_; uint8_t v___y_3090_; uint8_t v___y_3137_; uint32_t v___x_3147_; uint8_t v___x_3148_; 
v_c_3039_ = lean_string_utf8_get_fast(v_s_3012_, v_p_3016_);
v___x_3147_ = 65;
v___x_3148_ = lean_uint32_dec_le(v___x_3147_, v_c_3039_);
if (v___x_3148_ == 0)
{
goto v___jp_3142_;
}
else
{
uint32_t v___x_3149_; uint8_t v___x_3150_; 
v___x_3149_ = 90;
v___x_3150_ = lean_uint32_dec_le(v_c_3039_, v___x_3149_);
if (v___x_3150_ == 0)
{
goto v___jp_3142_;
}
else
{
goto v___jp_3025_;
}
}
v___jp_3040_:
{
if (v___y_3042_ == 0)
{
uint32_t v___x_3043_; uint8_t v___x_3044_; 
v___x_3043_ = 44;
v___x_3044_ = lean_uint32_dec_eq(v_c_3039_, v___x_3043_);
if (v___x_3044_ == 0)
{
uint32_t v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = 124;
v___x_3046_ = lean_uint32_dec_eq(v_c_3039_, v___x_3045_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; 
lean_inc_ref(v_s_3012_);
v___x_3047_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_3012_, v_p_3016_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
v_a_3049_ = lean_ctor_get(v___x_3047_, 1);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3047_, 2);
v___x_3050_ = lean_array_push(v_ands_3015_, v_a_3048_);
v_needsRange_3013_ = v___x_3046_;
v_ands_3015_ = v___x_3050_;
v_p_3016_ = v_a_3049_;
goto _start;
}
else
{
lean_object* v_a_3052_; lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v_ands_3015_);
lean_dec_ref(v_ors_3014_);
lean_dec_ref(v_s_3012_);
v_a_3052_ = lean_ctor_get(v___x_3047_, 0);
v_a_3053_ = lean_ctor_get(v___x_3047_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3047_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_inc(v_a_3052_);
lean_dec(v___x_3047_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3052_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v_p_3061_; uint8_t v___x_3062_; 
v_p_3061_ = lean_string_utf8_next_fast(v_s_3012_, v_p_3016_);
lean_dec(v_p_3016_);
v___x_3062_ = lean_nat_dec_eq(v_p_3061_, v___x_3023_);
if (v___x_3062_ == 0)
{
uint32_t v___x_3063_; uint8_t v___x_3064_; 
v___x_3063_ = lean_string_utf8_get_fast(v_s_3012_, v_p_3061_);
v___x_3064_ = lean_uint32_dec_eq(v___x_3063_, v___x_3045_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_dec_ref(v_ands_3015_);
lean_dec_ref(v_ors_3014_);
lean_dec_ref(v_s_3012_);
v___x_3065_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
lean_ctor_set(v___x_3066_, 1, v_p_3061_);
return v___x_3066_;
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3067_ = lean_array_get_size(v_ands_3015_);
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = lean_nat_dec_eq(v___x_3067_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = lean_array_push(v_ors_3014_, v_ands_3015_);
v___x_3071_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2));
v___x_3072_ = lean_string_utf8_next_fast(v_s_3012_, v_p_3061_);
v_needsRange_3013_ = v___y_3041_;
v_ors_3014_ = v___x_3070_;
v_ands_3015_ = v___x_3071_;
v_p_3016_ = v___x_3072_;
goto _start;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec_ref(v_ands_3015_);
lean_dec_ref(v_ors_3014_);
lean_dec_ref(v_s_3012_);
v___x_3074_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v_p_3061_);
return v___x_3075_;
}
}
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_dec_ref(v_ands_3015_);
lean_dec_ref(v_ors_3014_);
lean_dec_ref(v_s_3012_);
v___x_3076_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3076_);
lean_ctor_set(v___x_3077_, 1, v_p_3061_);
return v___x_3077_;
}
}
}
else
{
if (v_needsRange_3013_ == 0)
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_string_utf8_next_fast(v_s_3012_, v_p_3016_);
lean_dec(v_p_3016_);
v_needsRange_3013_ = v___y_3041_;
v_p_3016_ = v___x_3078_;
goto _start;
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec_ref(v_ands_3015_);
lean_dec_ref(v_ors_3014_);
lean_dec_ref(v_s_3012_);
v___x_3080_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
lean_ctor_set(v___x_3081_, 1, v_p_3016_);
return v___x_3081_;
}
}
}
else
{
goto v___jp_3020_;
}
}
v___jp_3082_:
{
if (v___y_3084_ == 0)
{
uint32_t v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = 13;
v___x_3086_ = lean_uint32_dec_eq(v_c_3039_, v___x_3085_);
if (v___x_3086_ == 0)
{
uint32_t v___x_3087_; uint8_t v___x_3088_; 
v___x_3087_ = 10;
v___x_3088_ = lean_uint32_dec_eq(v_c_3039_, v___x_3087_);
v___y_3041_ = v___y_3083_;
v___y_3042_ = v___x_3088_;
goto v___jp_3040_;
}
else
{
v___y_3041_ = v___y_3083_;
v___y_3042_ = v___x_3086_;
goto v___jp_3040_;
}
}
else
{
goto v___jp_3020_;
}
}
v___jp_3089_:
{
if (v___y_3090_ == 0)
{
uint32_t v___x_3091_; uint8_t v___x_3092_; 
v___x_3091_ = 42;
v___x_3092_ = lean_uint32_dec_eq(v_c_3039_, v___x_3091_);
if (v___x_3092_ == 0)
{
uint32_t v___x_3093_; uint8_t v___x_3094_; 
v___x_3093_ = 94;
v___x_3094_ = lean_uint32_dec_eq(v_c_3039_, v___x_3093_);
if (v___x_3094_ == 0)
{
uint32_t v___x_3095_; uint8_t v___x_3096_; 
v___x_3095_ = 126;
v___x_3096_ = lean_uint32_dec_eq(v_c_3039_, v___x_3095_);
if (v___x_3096_ == 0)
{
uint8_t v___x_3097_; uint32_t v___x_3098_; uint8_t v___x_3099_; 
v___x_3097_ = 1;
v___x_3098_ = 32;
v___x_3099_ = lean_uint32_dec_eq(v_c_3039_, v___x_3098_);
if (v___x_3099_ == 0)
{
uint32_t v___x_3100_; uint8_t v___x_3101_; 
v___x_3100_ = 9;
v___x_3101_ = lean_uint32_dec_eq(v_c_3039_, v___x_3100_);
v___y_3083_ = v___x_3097_;
v___y_3084_ = v___x_3101_;
goto v___jp_3082_;
}
else
{
v___y_3083_ = v___x_3097_;
v___y_3084_ = v___x_3099_;
goto v___jp_3082_;
}
}
else
{
lean_object* v_p_3102_; uint8_t v___x_3103_; 
v_p_3102_ = lean_string_utf8_next_fast(v_s_3012_, v_p_3016_);
lean_dec(v_p_3016_);
v___x_3103_ = lean_nat_dec_eq(v_p_3102_, v___x_3023_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; 
lean_inc_ref(v_s_3012_);
v___x_3104_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(v_s_3012_, v_ands_3015_, v_p_3102_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v_a_3106_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
v_a_3106_ = lean_ctor_get(v___x_3104_, 1);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3104_, 2);
v_needsRange_3013_ = v___x_3094_;
v_ands_3015_ = v_a_3105_;
v_p_3016_ = v_a_3106_;
goto _start;
}
else
{
lean_object* v_a_3108_; lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec_ref(v_ors_3014_);
lean_dec_ref(v_s_3012_);
v_a_3108_ = lean_ctor_get(v___x_3104_, 0);
v_a_3109_ = lean_ctor_get(v___x_3104_, 1);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3104_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_inc(v_a_3108_);
lean_dec(v___x_3104_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3108_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_dec_ref(v_ands_3015_);
lean_dec_ref(v_ors_3014_);
lean_dec_ref(v_s_3012_);
v___x_3117_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3));
v___x_3118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
lean_ctor_set(v___x_3118_, 1, v_p_3102_);
return v___x_3118_;
}
}
}
else
{
lean_object* v_p_3119_; uint8_t v___x_3120_; 
v_p_3119_ = lean_string_utf8_next_fast(v_s_3012_, v_p_3016_);
lean_dec(v_p_3016_);
v___x_3120_ = lean_nat_dec_eq(v_p_3119_, v___x_3023_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
lean_inc_ref(v_s_3012_);
v___x_3121_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(v_s_3012_, v_ands_3015_, v_p_3119_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v_a_3123_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
v_a_3123_ = lean_ctor_get(v___x_3121_, 1);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3121_, 2);
v_needsRange_3013_ = v___x_3092_;
v_ands_3015_ = v_a_3122_;
v_p_3016_ = v_a_3123_;
goto _start;
}
else
{
lean_object* v_a_3125_; lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v_ors_3014_);
lean_dec_ref(v_s_3012_);
v_a_3125_ = lean_ctor_get(v___x_3121_, 0);
v_a_3126_ = lean_ctor_get(v___x_3121_, 1);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3121_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_inc(v_a_3125_);
lean_dec(v___x_3121_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3125_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec_ref(v_ands_3015_);
lean_dec_ref(v_ors_3014_);
lean_dec_ref(v_s_3012_);
v___x_3134_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4));
v___x_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
lean_ctor_set(v___x_3135_, 1, v_p_3119_);
return v___x_3135_;
}
}
}
else
{
goto v___jp_3025_;
}
}
else
{
goto v___jp_3025_;
}
}
v___jp_3136_:
{
if (v___y_3137_ == 0)
{
uint32_t v___x_3138_; uint8_t v___x_3139_; 
v___x_3138_ = 48;
v___x_3139_ = lean_uint32_dec_le(v___x_3138_, v_c_3039_);
if (v___x_3139_ == 0)
{
v___y_3090_ = v___x_3139_;
goto v___jp_3089_;
}
else
{
uint32_t v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = 57;
v___x_3141_ = lean_uint32_dec_le(v_c_3039_, v___x_3140_);
v___y_3090_ = v___x_3141_;
goto v___jp_3089_;
}
}
else
{
goto v___jp_3025_;
}
}
v___jp_3142_:
{
uint32_t v___x_3143_; uint8_t v___x_3144_; 
v___x_3143_ = 97;
v___x_3144_ = lean_uint32_dec_le(v___x_3143_, v_c_3039_);
if (v___x_3144_ == 0)
{
v___y_3137_ = v___x_3144_;
goto v___jp_3136_;
}
else
{
uint32_t v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = 122;
v___x_3146_ = lean_uint32_dec_le(v_c_3039_, v___x_3145_);
v___y_3137_ = v___x_3146_;
goto v___jp_3136_;
}
}
}
else
{
lean_dec_ref(v_s_3012_);
if (v_needsRange_3013_ == 0)
{
lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3151_ = lean_array_get_size(v_ands_3015_);
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = lean_nat_dec_eq(v___x_3151_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_array_push(v_ors_3014_, v_ands_3015_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
lean_ctor_set(v___x_3155_, 1, v_p_3016_);
return v___x_3155_;
}
else
{
lean_dec_ref(v_ands_3015_);
lean_dec_ref(v_ors_3014_);
goto v___jp_3017_;
}
}
else
{
lean_dec_ref(v_ands_3015_);
lean_dec_ref(v_ors_3014_);
goto v___jp_3017_;
}
}
v___jp_3017_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v_p_3016_);
return v___x_3019_;
}
v___jp_3020_:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_string_utf8_next_fast(v_s_3012_, v_p_3016_);
lean_dec(v_p_3016_);
v_p_3016_ = v___x_3021_;
goto _start;
}
v___jp_3025_:
{
lean_object* v___x_3026_; 
lean_inc_ref(v_s_3012_);
v___x_3026_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(v_s_3012_, v_ands_3015_, v_p_3016_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v_a_3028_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
v_a_3028_ = lean_ctor_get(v___x_3026_, 1);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3026_, 2);
v_needsRange_3013_ = v___x_3024_;
v_ands_3015_ = v_a_3027_;
v_p_3016_ = v_a_3028_;
goto _start;
}
else
{
lean_object* v_a_3030_; lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v_ors_3014_);
lean_dec_ref(v_s_3012_);
v_a_3030_ = lean_ctor_get(v___x_3026_, 0);
v_a_3031_ = lean_ctor_get(v___x_3026_, 1);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3026_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_inc(v_a_3030_);
lean_dec(v___x_3026_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3030_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(lean_object* v_s_3156_, lean_object* v_needsRange_3157_, lean_object* v_ors_3158_, lean_object* v_ands_3159_, lean_object* v_p_3160_){
_start:
{
uint8_t v_needsRange_boxed_3161_; lean_object* v_res_3162_; 
v_needsRange_boxed_3161_ = lean_unbox(v_needsRange_3157_);
v_res_3162_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3156_, v_needsRange_boxed_3161_, v_ors_3158_, v_ands_3159_, v_p_3160_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object* v_s_3165_, lean_object* v_a_3166_){
_start:
{
uint8_t v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = 1;
v___x_3168_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3165_);
v___x_3169_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3165_, v___x_3167_, v___x_3168_, v___x_3168_, v_a_3166_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3179_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_a_3171_ = lean_ctor_get(v___x_3169_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3173_ = v___x_3169_;
v_isShared_3174_ = v_isSharedCheck_3179_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3179_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v___x_3177_; 
v___x_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3175_, 0, v_s_3165_);
lean_ctor_set(v___x_3175_, 1, v_a_3170_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v___x_3175_);
v___x_3177_ = v___x_3173_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_a_3171_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec_ref(v_s_3165_);
v_a_3180_ = lean_ctor_get(v___x_3169_, 0);
v_a_3181_ = lean_ctor_get(v___x_3169_, 1);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3169_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_inc(v_a_3180_);
lean_dec(v___x_3169_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3180_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_parse(lean_object* v_s_3189_){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3190_ = lean_unsigned_to_nat(0u);
v___x_3191_ = lean_string_utf8_byte_size(v_s_3189_);
v___x_3192_ = 1;
v___x_3193_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3189_);
v___x_3194_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3189_, v___x_3192_, v___x_3193_, v___x_3193_, v___x_3190_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3209_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_a_3196_ = lean_ctor_get(v___x_3194_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3198_ = v___x_3194_;
v_isShared_3199_ = v_isSharedCheck_3209_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3209_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
uint8_t v___x_3200_; 
v___x_3200_ = lean_nat_dec_eq(v_a_3196_, v___x_3191_);
if (v___x_3200_ == 0)
{
lean_object* v_tail_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_del_object(v___x_3198_);
lean_dec(v_a_3195_);
v_tail_3201_ = lean_string_utf8_extract(v_s_3189_, v_a_3196_, v___x_3191_);
lean_dec(v_a_3196_);
lean_dec_ref(v_s_3189_);
v___x_3202_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_3203_ = lean_string_append(v___x_3202_, v_tail_3201_);
lean_dec_ref(v_tail_3201_);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
return v___x_3204_;
}
else
{
lean_object* v___x_3206_; 
lean_dec(v_a_3196_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 1, v_a_3195_);
lean_ctor_set(v___x_3198_, 0, v_s_3189_);
v___x_3206_ = v___x_3198_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_s_3189_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_a_3195_);
v___x_3206_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3211_; 
lean_dec_ref(v_s_3189_);
v_a_3210_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3194_, 2);
v___x_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3211_, 0, v_a_3210_);
return v___x_3211_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(lean_object* v_ver_3214_, lean_object* v_as_3215_, size_t v_i_3216_, size_t v_stop_3217_){
_start:
{
uint8_t v___x_3218_; 
v___x_3218_ = lean_usize_dec_eq(v_i_3216_, v_stop_3217_);
if (v___x_3218_ == 0)
{
uint8_t v___x_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v___x_3219_ = 1;
v___x_3220_ = lean_array_uget_borrowed(v_as_3215_, v_i_3216_);
v___x_3221_ = l_Lake_VerComparator_test(v___x_3220_, v_ver_3214_);
if (v___x_3221_ == 0)
{
return v___x_3219_;
}
else
{
if (v___x_3218_ == 0)
{
size_t v___x_3222_; size_t v___x_3223_; 
v___x_3222_ = ((size_t)1ULL);
v___x_3223_ = lean_usize_add(v_i_3216_, v___x_3222_);
v_i_3216_ = v___x_3223_;
goto _start;
}
else
{
return v___x_3219_;
}
}
}
else
{
uint8_t v___x_3225_; 
v___x_3225_ = 0;
return v___x_3225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0___boxed(lean_object* v_ver_3226_, lean_object* v_as_3227_, lean_object* v_i_3228_, lean_object* v_stop_3229_){
_start:
{
size_t v_i_boxed_3230_; size_t v_stop_boxed_3231_; uint8_t v_res_3232_; lean_object* v_r_3233_; 
v_i_boxed_3230_ = lean_unbox_usize(v_i_3228_);
lean_dec(v_i_3228_);
v_stop_boxed_3231_ = lean_unbox_usize(v_stop_3229_);
lean_dec(v_stop_3229_);
v_res_3232_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3226_, v_as_3227_, v_i_boxed_3230_, v_stop_boxed_3231_);
lean_dec_ref(v_as_3227_);
lean_dec_ref(v_ver_3226_);
v_r_3233_ = lean_box(v_res_3232_);
return v_r_3233_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(lean_object* v_ver_3234_, lean_object* v_as_3235_, size_t v_i_3236_, size_t v_stop_3237_){
_start:
{
uint8_t v___x_3238_; 
v___x_3238_ = lean_usize_dec_eq(v_i_3236_, v_stop_3237_);
if (v___x_3238_ == 0)
{
uint8_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3239_ = 1;
v___x_3240_ = lean_array_uget_borrowed(v_as_3235_, v_i_3236_);
v___x_3241_ = lean_unsigned_to_nat(0u);
v___x_3242_ = lean_array_get_size(v___x_3240_);
v___x_3243_ = lean_nat_dec_lt(v___x_3241_, v___x_3242_);
if (v___x_3243_ == 0)
{
return v___x_3239_;
}
else
{
if (v___x_3243_ == 0)
{
return v___x_3239_;
}
else
{
size_t v___x_3244_; size_t v___x_3245_; uint8_t v___x_3246_; 
v___x_3244_ = ((size_t)0ULL);
v___x_3245_ = lean_usize_of_nat(v___x_3242_);
v___x_3246_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3234_, v___x_3240_, v___x_3244_, v___x_3245_);
if (v___x_3246_ == 0)
{
return v___x_3239_;
}
else
{
if (v___x_3238_ == 0)
{
size_t v___x_3247_; size_t v___x_3248_; 
v___x_3247_ = ((size_t)1ULL);
v___x_3248_ = lean_usize_add(v_i_3236_, v___x_3247_);
v_i_3236_ = v___x_3248_;
goto _start;
}
else
{
return v___x_3239_;
}
}
}
}
}
else
{
uint8_t v___x_3250_; 
v___x_3250_ = 0;
return v___x_3250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1___boxed(lean_object* v_ver_3251_, lean_object* v_as_3252_, lean_object* v_i_3253_, lean_object* v_stop_3254_){
_start:
{
size_t v_i_boxed_3255_; size_t v_stop_boxed_3256_; uint8_t v_res_3257_; lean_object* v_r_3258_; 
v_i_boxed_3255_ = lean_unbox_usize(v_i_3253_);
lean_dec(v_i_3253_);
v_stop_boxed_3256_ = lean_unbox_usize(v_stop_3254_);
lean_dec(v_stop_3254_);
v_res_3257_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3251_, v_as_3252_, v_i_boxed_3255_, v_stop_boxed_3256_);
lean_dec_ref(v_as_3252_);
lean_dec_ref(v_ver_3251_);
v_r_3258_ = lean_box(v_res_3257_);
return v_r_3258_;
}
}
LEAN_EXPORT uint8_t l_Lake_VerRange_test(lean_object* v_self_3259_, lean_object* v_ver_3260_){
_start:
{
lean_object* v_clauses_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v_clauses_3261_ = lean_ctor_get(v_self_3259_, 1);
v___x_3262_ = lean_unsigned_to_nat(0u);
v___x_3263_ = lean_array_get_size(v_clauses_3261_);
v___x_3264_ = lean_nat_dec_lt(v___x_3262_, v___x_3263_);
if (v___x_3264_ == 0)
{
return v___x_3264_;
}
else
{
if (v___x_3264_ == 0)
{
return v___x_3264_;
}
else
{
size_t v___x_3265_; size_t v___x_3266_; uint8_t v___x_3267_; 
v___x_3265_ = ((size_t)0ULL);
v___x_3266_ = lean_usize_of_nat(v___x_3263_);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3260_, v_clauses_3261_, v___x_3265_, v___x_3266_);
return v___x_3267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_test___boxed(lean_object* v_self_3268_, lean_object* v_ver_3269_){
_start:
{
uint8_t v_res_3270_; lean_object* v_r_3271_; 
v_res_3270_ = l_Lake_VerRange_test(v_self_3268_, v_ver_3269_);
lean_dec_ref(v_ver_3269_);
lean_dec_ref(v_self_3268_);
v_r_3271_ = lean_box(v_res_3270_);
return v_r_3271_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
