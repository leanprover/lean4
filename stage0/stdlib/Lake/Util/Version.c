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
static const lean_closure_object l_Lake_SemVerCore_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_parse___closed__0 = (const lean_object*)&l_Lake_SemVerCore_parse___closed__0_value;
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
static const lean_closure_object l_Lake_StdVer_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_parse___closed__0 = (const lean_object*)&l_Lake_StdVer_parse___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(lean_object*, lean_object*);
static const lean_closure_object l_Lake_VerComparator_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Util_Version_0__Lake_VerComparator_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_VerComparator_parse___closed__0 = (const lean_object*)&l_Lake_VerComparator_parse___closed__0_value;
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
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 183, .m_capacity = 183, .m_length = 180, .m_data = "invalid version range: bare versions are not supported; if you want to pin a specific version, use '=' before the full version; otherwise, use '≥' to support it and future versions"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "invalid patch version: components after a wildcard must be wildcards"};
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object*, lean_object*);
static const lean_closure_object l_Lake_VerRange_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Util_Version_0__Lake_VerRange_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_VerRange_parse___closed__0 = (const lean_object*)&l_Lake_VerRange_parse___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_VerRange_parse(lean_object*);
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
v___x_321_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_317_, v_x_318_, v_startPos_319_, v_endPos_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___boxed(lean_object* v_00_u03b1_322_, lean_object* v_s_323_, lean_object* v_x_324_, lean_object* v_startPos_325_, lean_object* v_endPos_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Lake_Util_Version_0__Lake_runVerParse(v_00_u03b1_322_, v_s_323_, v_x_324_, v_startPos_325_, v_endPos_326_);
lean_dec(v_endPos_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprSemVerCore_repr_spec__0(lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_nat_to_int(v_a_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(9u);
v___x_348_ = lean_nat_to_int(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__0));
v___x_360_ = lean_string_length(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__15, &l_Lake_instReprSemVerCore_repr___redArg___closed__15_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15);
v___x_362_ = lean_nat_to_int(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___redArg(lean_object* v_x_367_){
_start:
{
lean_object* v_major_368_; lean_object* v_minor_369_; lean_object* v_patch_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_major_368_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_major_368_);
v_minor_369_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_minor_369_);
v_patch_370_ = lean_ctor_get(v_x_367_, 2);
lean_inc(v_patch_370_);
lean_dec_ref(v_x_367_);
v___x_371_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_372_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__6));
v___x_373_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__7, &l_Lake_instReprSemVerCore_repr___redArg___closed__7_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7);
v___x_374_ = l_Nat_reprFast(v_major_368_);
v___x_375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
v___x_376_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_373_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = 0;
v___x_378_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*1, v___x_377_);
v___x_379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_372_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_box(1);
v___x_383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__11));
v___x_385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_371_);
v___x_387_ = l_Nat_reprFast(v_minor_369_);
v___x_388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
v___x_389_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_373_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*1, v___x_377_);
v___x_391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_386_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_380_);
v___x_393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_382_);
v___x_394_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__13));
v___x_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_371_);
v___x_397_ = l_Nat_reprFast(v_patch_370_);
v___x_398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_373_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*1, v___x_377_);
v___x_401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_396_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_403_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_401_);
v___x_405_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_402_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*1, v___x_377_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr(lean_object* v_x_409_, lean_object* v_prec_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lake_instReprSemVerCore_repr___redArg(v_x_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___boxed(lean_object* v_x_412_, lean_object* v_prec_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lake_instReprSemVerCore_repr(v_x_412_, v_prec_413_);
lean_dec(v_prec_413_);
return v_res_414_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore_decEq(lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_major_419_; lean_object* v_minor_420_; lean_object* v_patch_421_; lean_object* v_major_422_; lean_object* v_minor_423_; lean_object* v_patch_424_; uint8_t v___x_425_; 
v_major_419_ = lean_ctor_get(v_x_417_, 0);
v_minor_420_ = lean_ctor_get(v_x_417_, 1);
v_patch_421_ = lean_ctor_get(v_x_417_, 2);
v_major_422_ = lean_ctor_get(v_x_418_, 0);
v_minor_423_ = lean_ctor_get(v_x_418_, 1);
v_patch_424_ = lean_ctor_get(v_x_418_, 2);
v___x_425_ = lean_nat_dec_eq(v_major_419_, v_major_422_);
if (v___x_425_ == 0)
{
return v___x_425_;
}
else
{
uint8_t v___x_426_; 
v___x_426_ = lean_nat_dec_eq(v_minor_420_, v_minor_423_);
if (v___x_426_ == 0)
{
return v___x_426_;
}
else
{
uint8_t v___x_427_; 
v___x_427_ = lean_nat_dec_eq(v_patch_421_, v_patch_424_);
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore_decEq___boxed(lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_428_, v_x_429_);
lean_dec_ref(v_x_429_);
lean_dec_ref(v_x_428_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_432_, v_x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore___boxed(lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Lake_instDecidableEqSemVerCore(v_x_435_, v_x_436_);
lean_dec_ref(v_x_436_);
lean_dec_ref(v_x_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdSemVerCore_ord(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_major_441_; lean_object* v_minor_442_; lean_object* v_patch_443_; lean_object* v_major_444_; lean_object* v_minor_445_; lean_object* v_patch_446_; uint8_t v___x_447_; 
v_major_441_ = lean_ctor_get(v_x_439_, 0);
v_minor_442_ = lean_ctor_get(v_x_439_, 1);
v_patch_443_ = lean_ctor_get(v_x_439_, 2);
v_major_444_ = lean_ctor_get(v_x_440_, 0);
v_minor_445_ = lean_ctor_get(v_x_440_, 1);
v_patch_446_ = lean_ctor_get(v_x_440_, 2);
v___x_447_ = lean_nat_dec_lt(v_major_441_, v_major_444_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; 
v___x_448_ = lean_nat_dec_eq(v_major_441_, v_major_444_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; 
v___x_449_ = 2;
return v___x_449_;
}
else
{
uint8_t v___x_450_; 
v___x_450_ = lean_nat_dec_lt(v_minor_442_, v_minor_445_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = lean_nat_dec_eq(v_minor_442_, v_minor_445_);
if (v___x_451_ == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 2;
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = lean_nat_dec_lt(v_patch_443_, v_patch_446_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
v___x_454_ = lean_nat_dec_eq(v_patch_443_, v_patch_446_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
v___x_455_ = 2;
return v___x_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 1;
return v___x_456_;
}
}
else
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
}
}
else
{
uint8_t v___x_458_; 
v___x_458_ = 0;
return v___x_458_;
}
}
}
else
{
uint8_t v___x_459_; 
v___x_459_ = 0;
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdSemVerCore_ord___boxed(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Lake_instOrdSemVerCore_ord(v_x_460_, v_x_461_);
lean_dec_ref(v_x_461_);
lean_dec_ref(v_x_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
static lean_object* _init_l_Lake_SemVerCore_instLT(void){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_box(0);
return v___x_466_;
}
}
static lean_object* _init_l_Lake_SemVerCore_instLE(void){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = lean_box(0);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0(lean_object* v_x_468_, lean_object* v_y_469_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = l_Lake_instOrdSemVerCore_ord(v_x_468_, v_y_469_);
if (v___x_470_ == 2)
{
lean_inc_ref(v_y_469_);
return v_y_469_;
}
else
{
lean_inc_ref(v_x_468_);
return v_x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0___boxed(lean_object* v_x_471_, lean_object* v_y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lake_SemVerCore_instMin___lam__0(v_x_471_, v_y_472_);
lean_dec_ref(v_y_472_);
lean_dec_ref(v_x_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0(lean_object* v_x_476_, lean_object* v_y_477_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = l_Lake_instOrdSemVerCore_ord(v_x_476_, v_y_477_);
if (v___x_478_ == 2)
{
lean_inc_ref(v_x_476_);
return v_x_476_;
}
else
{
lean_inc_ref(v_y_477_);
return v_y_477_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0___boxed(lean_object* v_x_479_, lean_object* v_y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lake_SemVerCore_instMax___lam__0(v_x_479_, v_y_480_);
lean_dec_ref(v_y_480_);
lean_dec_ref(v_x_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(lean_object* v_s_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_a_493_; lean_object* v_a_494_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v_a_501_; lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_553_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_491_);
v___x_500_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_490_, v___x_499_, v_a_491_, v_a_491_);
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_a_502_ = lean_ctor_get(v___x_500_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_553_ == 0)
{
v___x_504_ = v___x_500_;
v_isShared_505_ = v_isSharedCheck_553_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_553_;
goto v_resetjp_503_;
}
v___jp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0));
v___x_496_ = lean_string_append(v___x_495_, v_a_493_);
lean_dec_ref(v_a_493_);
v___x_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_a_494_);
return v___x_497_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = lean_array_get_size(v_a_501_);
v___x_507_ = lean_unsigned_to_nat(3u);
v___x_508_ = lean_nat_dec_eq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_del_object(v___x_504_);
lean_dec(v_a_501_);
v___x_509_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1));
v___x_510_ = l_Nat_reprFast(v___x_506_);
v___x_511_ = lean_string_append(v___x_509_, v___x_510_);
lean_dec_ref(v___x_510_);
v___x_512_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2));
v___x_513_ = lean_string_append(v___x_511_, v___x_512_);
v_a_493_ = v___x_513_;
v_a_494_ = v_a_502_;
goto v___jp_492_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_array_fget_borrowed(v_a_501_, v___x_498_);
v___x_515_ = l_String_Slice_toNat_x3f(v___x_514_);
if (lean_obj_tag(v___x_515_) == 1)
{
lean_object* v_val_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_val_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_val_516_);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_array_fget_borrowed(v_a_501_, v___x_517_);
v___x_519_ = l_String_Slice_toNat_x3f(v___x_518_);
if (lean_obj_tag(v___x_519_) == 1)
{
lean_object* v_val_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_val_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_val_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = lean_unsigned_to_nat(2u);
v___x_522_ = lean_array_fget(v_a_501_, v___x_521_);
lean_dec(v_a_501_);
v___x_523_ = l_String_Slice_toNat_x3f(v___x_522_);
if (lean_obj_tag(v___x_523_) == 1)
{
lean_object* v_val_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec(v___x_522_);
v_val_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_525_, 0, v_val_516_);
lean_ctor_set(v___x_525_, 1, v_val_520_);
lean_ctor_set(v___x_525_, 2, v_val_524_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_525_);
v___x_527_ = v___x_504_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_a_502_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v_str_529_; lean_object* v_startInclusive_530_; lean_object* v_endExclusive_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v___x_523_);
lean_dec(v_val_520_);
lean_dec(v_val_516_);
lean_del_object(v___x_504_);
v_str_529_ = lean_ctor_get(v___x_522_, 0);
lean_inc_ref(v_str_529_);
v_startInclusive_530_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_startInclusive_530_);
v_endExclusive_531_ = lean_ctor_get(v___x_522_, 2);
lean_inc(v_endExclusive_531_);
lean_dec(v___x_522_);
v___x_532_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_533_ = lean_string_utf8_extract(v_str_529_, v_startInclusive_530_, v_endExclusive_531_);
lean_dec(v_endExclusive_531_);
lean_dec(v_startInclusive_530_);
lean_dec_ref(v_str_529_);
v___x_534_ = lean_string_append(v___x_532_, v___x_533_);
lean_dec_ref(v___x_533_);
v___x_535_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_536_ = lean_string_append(v___x_534_, v___x_535_);
v_a_493_ = v___x_536_;
v_a_494_ = v_a_502_;
goto v___jp_492_;
}
}
else
{
lean_object* v_str_537_; lean_object* v_startInclusive_538_; lean_object* v_endExclusive_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
lean_inc(v___x_518_);
lean_dec(v___x_519_);
lean_dec(v_val_516_);
lean_del_object(v___x_504_);
lean_dec(v_a_501_);
v_str_537_ = lean_ctor_get(v___x_518_, 0);
lean_inc_ref(v_str_537_);
v_startInclusive_538_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_startInclusive_538_);
v_endExclusive_539_ = lean_ctor_get(v___x_518_, 2);
lean_inc(v_endExclusive_539_);
lean_dec(v___x_518_);
v___x_540_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_541_ = lean_string_utf8_extract(v_str_537_, v_startInclusive_538_, v_endExclusive_539_);
lean_dec(v_endExclusive_539_);
lean_dec(v_startInclusive_538_);
lean_dec_ref(v_str_537_);
v___x_542_ = lean_string_append(v___x_540_, v___x_541_);
lean_dec_ref(v___x_541_);
v___x_543_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
v_a_493_ = v___x_544_;
v_a_494_ = v_a_502_;
goto v___jp_492_;
}
}
else
{
lean_object* v_str_545_; lean_object* v_startInclusive_546_; lean_object* v_endExclusive_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_inc(v___x_514_);
lean_dec(v___x_515_);
lean_del_object(v___x_504_);
lean_dec(v_a_501_);
v_str_545_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_str_545_);
v_startInclusive_546_ = lean_ctor_get(v___x_514_, 1);
lean_inc(v_startInclusive_546_);
v_endExclusive_547_ = lean_ctor_get(v___x_514_, 2);
lean_inc(v_endExclusive_547_);
lean_dec(v___x_514_);
v___x_548_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_549_ = lean_string_utf8_extract(v_str_545_, v_startInclusive_546_, v_endExclusive_547_);
lean_dec(v_endExclusive_547_);
lean_dec(v_startInclusive_546_);
lean_dec_ref(v_str_545_);
v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_552_ = lean_string_append(v___x_550_, v___x_551_);
v_a_493_ = v___x_552_;
v_a_494_ = v_a_502_;
goto v___jp_492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_parse(lean_object* v_s_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_556_ = ((lean_object*)(l_Lake_SemVerCore_parse___closed__0));
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_string_utf8_byte_size(v_s_555_);
v___x_559_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_555_, v___x_556_, v___x_557_, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_toString(lean_object* v_ver_561_){
_start:
{
lean_object* v_major_562_; lean_object* v_minor_563_; lean_object* v_patch_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_major_562_ = lean_ctor_get(v_ver_561_, 0);
lean_inc(v_major_562_);
v_minor_563_ = lean_ctor_get(v_ver_561_, 1);
lean_inc(v_minor_563_);
v_patch_564_ = lean_ctor_get(v_ver_561_, 2);
lean_inc(v_patch_564_);
lean_dec_ref(v_ver_561_);
v___x_565_ = l_Nat_reprFast(v_major_562_);
v___x_566_ = ((lean_object*)(l_Lake_SemVerCore_toString___closed__0));
v___x_567_ = lean_string_append(v___x_565_, v___x_566_);
v___x_568_ = l_Nat_reprFast(v_minor_563_);
v___x_569_ = lean_string_append(v___x_567_, v___x_568_);
lean_dec_ref(v___x_568_);
v___x_570_ = lean_string_append(v___x_569_, v___x_566_);
v___x_571_ = l_Nat_reprFast(v_patch_564_);
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
lean_dec_ref(v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instToJson___lam__0(lean_object* v_x_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = l_Lake_SemVerCore_toString(v_x_575_);
v___x_577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instFromJson___lam__0(lean_object* v_x_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Json_getStr_x3f(v_x_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_a_590_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_581_, 1);
v___x_591_ = ((lean_object*)(l_Lake_SemVerCore_parse___closed__0));
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_string_utf8_byte_size(v_a_590_);
v___x_594_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_a_590_, v___x_591_, v___x_592_, v___x_593_);
return v___x_594_;
}
}
}
static lean_object* _init_l_Lake_instReprStdVer_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(16u);
v___x_612_ = lean_nat_to_int(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___redArg(lean_object* v_x_616_){
_start:
{
lean_object* v_toSemVerCore_617_; lean_object* v_specialDescr_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_651_; 
v_toSemVerCore_617_ = lean_ctor_get(v_x_616_, 0);
v_specialDescr_618_ = lean_ctor_get(v_x_616_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_651_ == 0)
{
v___x_620_ = v_x_616_;
v_isShared_621_ = v_isSharedCheck_651_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_specialDescr_618_);
lean_inc(v_toSemVerCore_617_);
lean_dec(v_x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_651_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_622_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_623_ = ((lean_object*)(l_Lake_instReprStdVer_repr___redArg___closed__3));
v___x_624_ = lean_obj_once(&l_Lake_instReprStdVer_repr___redArg___closed__4, &l_Lake_instReprStdVer_repr___redArg___closed__4_once, _init_l_Lake_instReprStdVer_repr___redArg___closed__4);
v___x_625_ = l_Lake_instReprSemVerCore_repr___redArg(v_toSemVerCore_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 4);
lean_ctor_set(v___x_620_, 1, v___x_625_);
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_650_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_628_ = 0;
v___x_629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v___x_628_);
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_623_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_box(1);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = ((lean_object*)(l_Lake_instReprStdVer_repr___redArg___closed__6));
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_622_);
v___x_638_ = l_String_quote(v_specialDescr_618_);
v___x_639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
v___x_640_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_624_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1, v___x_628_);
v___x_642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_637_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_644_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_642_);
v___x_646_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_643_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*1, v___x_628_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr(lean_object* v_x_652_, lean_object* v_prec_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lake_instReprStdVer_repr___redArg(v_x_652_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___boxed(lean_object* v_x_655_, lean_object* v_prec_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lake_instReprStdVer_repr(v_x_655_, v_prec_656_);
lean_dec(v_prec_656_);
return v_res_657_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer_decEq(lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v_toSemVerCore_662_; lean_object* v_specialDescr_663_; lean_object* v_toSemVerCore_664_; lean_object* v_specialDescr_665_; uint8_t v___x_666_; 
v_toSemVerCore_662_ = lean_ctor_get(v_x_660_, 0);
v_specialDescr_663_ = lean_ctor_get(v_x_660_, 1);
v_toSemVerCore_664_ = lean_ctor_get(v_x_661_, 0);
v_specialDescr_665_ = lean_ctor_get(v_x_661_, 1);
v___x_666_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_662_, v_toSemVerCore_664_);
if (v___x_666_ == 0)
{
return v___x_666_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = lean_string_dec_eq(v_specialDescr_663_, v_specialDescr_665_);
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer_decEq___boxed(lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Lake_instDecidableEqStdVer_decEq(v_x_668_, v_x_669_);
lean_dec_ref(v_x_669_);
lean_dec_ref(v_x_668_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer(lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
uint8_t v___x_674_; 
v___x_674_ = l_Lake_instDecidableEqStdVer_decEq(v_x_672_, v_x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer___boxed(lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l_Lake_instDecidableEqStdVer(v_x_675_, v_x_676_);
lean_dec_ref(v_x_676_);
lean_dec_ref(v_x_675_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0(lean_object* v_self_679_){
_start:
{
lean_object* v_toSemVerCore_680_; 
v_toSemVerCore_680_ = lean_ctor_get(v_self_679_, 0);
lean_inc_ref(v_toSemVerCore_680_);
return v_toSemVerCore_680_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed(lean_object* v_self_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lake_StdVer_instCoeSemVerCore___lam__0(v_self_681_);
lean_dec_ref(v_self_681_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_ofSemVerCore(lean_object* v_ver_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_ver_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT uint8_t l_Lake_StdVer_compare(lean_object* v_a_690_, lean_object* v_b_691_){
_start:
{
lean_object* v_toSemVerCore_692_; lean_object* v_specialDescr_693_; lean_object* v_toSemVerCore_694_; lean_object* v_specialDescr_695_; uint8_t v___x_696_; 
v_toSemVerCore_692_ = lean_ctor_get(v_a_690_, 0);
v_specialDescr_693_ = lean_ctor_get(v_a_690_, 1);
v_toSemVerCore_694_ = lean_ctor_get(v_b_691_, 0);
v_specialDescr_695_ = lean_ctor_get(v_b_691_, 1);
v___x_696_ = l_Lake_instOrdSemVerCore_ord(v_toSemVerCore_692_, v_toSemVerCore_694_);
if (v___x_696_ == 1)
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_698_ = lean_string_dec_eq(v_specialDescr_693_, v___x_697_);
if (v___x_698_ == 0)
{
uint8_t v___x_699_; 
v___x_699_ = lean_string_dec_eq(v_specialDescr_695_, v___x_697_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; 
v___x_700_ = lean_string_compare(v_specialDescr_693_, v_specialDescr_695_);
return v___x_700_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
}
else
{
uint8_t v___x_702_; 
v___x_702_ = lean_string_dec_eq(v_specialDescr_695_, v___x_697_);
if (v___x_702_ == 0)
{
uint8_t v___x_703_; 
v___x_703_ = 2;
return v___x_703_;
}
else
{
return v___x_696_;
}
}
}
else
{
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_compare___boxed(lean_object* v_a_704_, lean_object* v_b_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Lake_StdVer_compare(v_a_704_, v_b_705_);
lean_dec_ref(v_b_705_);
lean_dec_ref(v_a_704_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
static lean_object* _init_l_Lake_StdVer_instLT(void){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_box(0);
return v___x_710_;
}
}
static lean_object* _init_l_Lake_StdVer_instLE(void){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = lean_box(0);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0(lean_object* v_x_712_, lean_object* v_y_713_){
_start:
{
uint8_t v___x_714_; 
v___x_714_ = l_Lake_StdVer_compare(v_x_712_, v_y_713_);
if (v___x_714_ == 2)
{
lean_inc_ref(v_y_713_);
return v_y_713_;
}
else
{
lean_inc_ref(v_x_712_);
return v_x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0___boxed(lean_object* v_x_715_, lean_object* v_y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lake_StdVer_instMin___lam__0(v_x_715_, v_y_716_);
lean_dec_ref(v_y_716_);
lean_dec_ref(v_x_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0(lean_object* v_x_720_, lean_object* v_y_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = l_Lake_StdVer_compare(v_x_720_, v_y_721_);
if (v___x_722_ == 2)
{
lean_inc_ref(v_x_720_);
return v_x_720_;
}
else
{
lean_inc_ref(v_y_721_);
return v_y_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0___boxed(lean_object* v_x_723_, lean_object* v_y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lake_StdVer_instMax___lam__0(v_x_723_, v_y_724_);
lean_dec_ref(v_y_724_);
lean_dec_ref(v_x_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parseM(lean_object* v_s_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_730_; 
lean_inc_ref(v_s_728_);
v___x_730_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_728_, v_a_729_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
v_a_732_ = lean_ctor_get(v___x_730_, 1);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_730_, 2);
v___x_733_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_728_, v_a_732_);
lean_dec_ref(v_s_728_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_a_735_ = lean_ctor_get(v___x_733_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_743_ == 0)
{
v___x_737_ = v___x_733_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v_a_731_);
lean_ctor_set(v___x_739_, 1, v_a_734_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_a_735_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
else
{
lean_object* v_a_744_; lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_a_731_);
v_a_744_ = lean_ctor_get(v___x_733_, 0);
v_a_745_ = lean_ctor_get(v___x_733_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_733_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_inc(v_a_744_);
lean_dec(v___x_733_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_744_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v_s_728_);
v_a_753_ = lean_ctor_get(v___x_730_, 0);
v_a_754_ = lean_ctor_get(v___x_730_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_730_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_inc(v_a_753_);
lean_dec(v___x_730_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_753_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parse(lean_object* v_s_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_764_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_string_utf8_byte_size(v_s_763_);
v___x_767_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_763_, v___x_764_, v___x_765_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_toString(lean_object* v_ver_769_){
_start:
{
lean_object* v_toSemVerCore_770_; lean_object* v_specialDescr_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_toSemVerCore_770_ = lean_ctor_get(v_ver_769_, 0);
lean_inc_ref(v_toSemVerCore_770_);
v_specialDescr_771_ = lean_ctor_get(v_ver_769_, 1);
lean_inc_ref(v_specialDescr_771_);
lean_dec_ref(v_ver_769_);
v___x_772_ = lean_string_utf8_byte_size(v_specialDescr_771_);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_nat_dec_eq(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = l_Lake_SemVerCore_toString(v_toSemVerCore_770_);
v___x_776_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
v___x_778_ = lean_string_append(v___x_777_, v_specialDescr_771_);
lean_dec_ref(v_specialDescr_771_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; 
lean_dec_ref(v_specialDescr_771_);
v___x_779_ = l_Lake_SemVerCore_toString(v_toSemVerCore_770_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instToJson___lam__0(lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = l_Lake_StdVer_toString(v_x_782_);
v___x_784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instFromJson___lam__0(lean_object* v_x_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Json_getStr_x3f(v_x_787_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_a_797_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_788_, 1);
v___x_798_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_string_utf8_byte_size(v_a_797_);
v___x_801_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_a_797_, v___x_798_, v___x_799_, v___x_800_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx(lean_object* v_x_810_){
_start:
{
switch(lean_obj_tag(v_x_810_))
{
case 0:
{
lean_object* v___x_811_; 
v___x_811_ = lean_unsigned_to_nat(0u);
return v___x_811_;
}
case 1:
{
lean_object* v___x_812_; 
v___x_812_ = lean_unsigned_to_nat(1u);
return v___x_812_;
}
case 2:
{
lean_object* v___x_813_; 
v___x_813_ = lean_unsigned_to_nat(2u);
return v___x_813_;
}
default: 
{
lean_object* v___x_814_; 
v___x_814_ = lean_unsigned_to_nat(3u);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___boxed(lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lake_ToolchainVer_ctorIdx(v_x_815_);
lean_dec_ref(v_x_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___redArg(lean_object* v_t_817_, lean_object* v_k_818_){
_start:
{
switch(lean_obj_tag(v_t_817_))
{
case 1:
{
lean_object* v_date_819_; lean_object* v_rev_820_; lean_object* v___x_821_; 
v_date_819_ = lean_ctor_get(v_t_817_, 0);
lean_inc_ref(v_date_819_);
v_rev_820_ = lean_ctor_get(v_t_817_, 1);
lean_inc(v_rev_820_);
lean_dec_ref_known(v_t_817_, 2);
v___x_821_ = lean_apply_2(v_k_818_, v_date_819_, v_rev_820_);
return v___x_821_;
}
case 2:
{
lean_object* v_n_822_; lean_object* v___x_823_; 
v_n_822_ = lean_ctor_get(v_t_817_, 0);
lean_inc(v_n_822_);
lean_dec_ref_known(v_t_817_, 1);
v___x_823_ = lean_apply_1(v_k_818_, v_n_822_);
return v___x_823_;
}
default: 
{
lean_object* v_ver_824_; lean_object* v___x_825_; 
v_ver_824_ = lean_ctor_get(v_t_817_, 0);
lean_inc_ref(v_ver_824_);
lean_dec_ref(v_t_817_);
v___x_825_ = lean_apply_1(v_k_818_, v_ver_824_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim(lean_object* v_motive_826_, lean_object* v_ctorIdx_827_, lean_object* v_t_828_, lean_object* v_h_829_, lean_object* v_k_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_828_, v_k_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___boxed(lean_object* v_motive_832_, lean_object* v_ctorIdx_833_, lean_object* v_t_834_, lean_object* v_h_835_, lean_object* v_k_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lake_ToolchainVer_ctorElim(v_motive_832_, v_ctorIdx_833_, v_t_834_, v_h_835_, v_k_836_);
lean_dec(v_ctorIdx_833_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim___redArg(lean_object* v_t_838_, lean_object* v_release_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_838_, v_release_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim(lean_object* v_motive_841_, lean_object* v_t_842_, lean_object* v_h_843_, lean_object* v_release_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_842_, v_release_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim___redArg(lean_object* v_t_846_, lean_object* v_nightly_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_846_, v_nightly_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim(lean_object* v_motive_849_, lean_object* v_t_850_, lean_object* v_h_851_, lean_object* v_nightly_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_850_, v_nightly_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim___redArg(lean_object* v_t_854_, lean_object* v_pr_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_854_, v_pr_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim(lean_object* v_motive_857_, lean_object* v_t_858_, lean_object* v_h_859_, lean_object* v_pr_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_858_, v_pr_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim___redArg(lean_object* v_t_862_, lean_object* v_other_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_862_, v_other_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim(lean_object* v_motive_865_, lean_object* v_t_866_, lean_object* v_h_867_, lean_object* v_other_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_866_, v_other_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override___redArg(lean_object* v_t_870_, lean_object* v_release_871_, lean_object* v_nightly_872_, lean_object* v_pr_873_, lean_object* v_other_874_){
_start:
{
switch(lean_obj_tag(v_t_870_))
{
case 0:
{
lean_object* v_ver_875_; lean_object* v___x_876_; 
lean_dec(v_other_874_);
lean_dec(v_pr_873_);
lean_dec(v_nightly_872_);
v_ver_875_ = lean_ctor_get(v_t_870_, 1);
lean_inc_ref(v_ver_875_);
lean_dec_ref_known(v_t_870_, 2);
v___x_876_ = lean_apply_1(v_release_871_, v_ver_875_);
return v___x_876_;
}
case 1:
{
lean_object* v_date_877_; lean_object* v_rev_878_; lean_object* v___x_879_; 
lean_dec(v_other_874_);
lean_dec(v_pr_873_);
lean_dec(v_release_871_);
v_date_877_ = lean_ctor_get(v_t_870_, 1);
lean_inc_ref(v_date_877_);
v_rev_878_ = lean_ctor_get(v_t_870_, 2);
lean_inc(v_rev_878_);
lean_dec_ref_known(v_t_870_, 3);
v___x_879_ = lean_apply_2(v_nightly_872_, v_date_877_, v_rev_878_);
return v___x_879_;
}
case 2:
{
lean_object* v_n_880_; lean_object* v___x_881_; 
lean_dec(v_other_874_);
lean_dec(v_nightly_872_);
lean_dec(v_release_871_);
v_n_880_ = lean_ctor_get(v_t_870_, 1);
lean_inc(v_n_880_);
lean_dec_ref_known(v_t_870_, 2);
v___x_881_ = lean_apply_1(v_pr_873_, v_n_880_);
return v___x_881_;
}
default: 
{
lean_object* v_v_882_; lean_object* v___x_883_; 
lean_dec(v_pr_873_);
lean_dec(v_nightly_872_);
lean_dec(v_release_871_);
v_v_882_ = lean_ctor_get(v_t_870_, 1);
lean_inc_ref(v_v_882_);
lean_dec_ref_known(v_t_870_, 2);
v___x_883_ = lean_apply_1(v_other_874_, v_v_882_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override(lean_object* v_motive_884_, lean_object* v_t_885_, lean_object* v_release_886_, lean_object* v_nightly_887_, lean_object* v_pr_888_, lean_object* v_other_889_){
_start:
{
switch(lean_obj_tag(v_t_885_))
{
case 0:
{
lean_object* v_ver_890_; lean_object* v___x_891_; 
lean_dec(v_other_889_);
lean_dec(v_pr_888_);
lean_dec(v_nightly_887_);
v_ver_890_ = lean_ctor_get(v_t_885_, 1);
lean_inc_ref(v_ver_890_);
lean_dec_ref_known(v_t_885_, 2);
v___x_891_ = lean_apply_1(v_release_886_, v_ver_890_);
return v___x_891_;
}
case 1:
{
lean_object* v_date_892_; lean_object* v_rev_893_; lean_object* v___x_894_; 
lean_dec(v_other_889_);
lean_dec(v_pr_888_);
lean_dec(v_release_886_);
v_date_892_ = lean_ctor_get(v_t_885_, 1);
lean_inc_ref(v_date_892_);
v_rev_893_ = lean_ctor_get(v_t_885_, 2);
lean_inc(v_rev_893_);
lean_dec_ref_known(v_t_885_, 3);
v___x_894_ = lean_apply_2(v_nightly_887_, v_date_892_, v_rev_893_);
return v___x_894_;
}
case 2:
{
lean_object* v_n_895_; lean_object* v___x_896_; 
lean_dec(v_other_889_);
lean_dec(v_nightly_887_);
lean_dec(v_release_886_);
v_n_895_ = lean_ctor_get(v_t_885_, 1);
lean_inc(v_n_895_);
lean_dec_ref_known(v_t_885_, 2);
v___x_896_ = lean_apply_1(v_pr_888_, v_n_895_);
return v___x_896_;
}
default: 
{
lean_object* v_v_897_; lean_object* v___x_898_; 
lean_dec(v_pr_888_);
lean_dec(v_nightly_887_);
lean_dec(v_release_886_);
v_v_897_ = lean_ctor_get(v_t_885_, 1);
lean_inc_ref(v_v_897_);
lean_dec_ref_known(v_t_885_, 2);
v___x_898_ = lean_apply_1(v_other_889_, v_v_897_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release___override(lean_object* v_ver_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_901_ = ((lean_object*)(l_Lake_ToolchainVer_release___override___closed__0));
lean_inc_ref(v_ver_900_);
v___x_902_ = l_Lake_StdVer_toString(v_ver_900_);
v___x_903_ = lean_string_append(v___x_901_, v___x_902_);
lean_dec_ref(v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v_ver_900_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly___override(lean_object* v_date_907_, lean_object* v_rev_908_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___y_913_; 
v___x_909_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__0));
lean_inc_ref(v_date_907_);
v___x_910_ = l_Lake_Date_toString(v_date_907_);
v___x_911_ = lean_string_append(v___x_909_, v___x_910_);
lean_dec_ref(v___x_910_);
if (lean_obj_tag(v_rev_908_) == 0)
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___y_913_ = v___x_916_;
goto v___jp_912_;
}
else
{
lean_object* v_val_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_val_917_ = lean_ctor_get(v_rev_908_, 0);
v___x_918_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
lean_inc(v_val_917_);
v___x_919_ = l_Nat_reprFast(v_val_917_);
v___x_920_ = lean_string_append(v___x_918_, v___x_919_);
lean_dec_ref(v___x_919_);
v___y_913_ = v___x_920_;
goto v___jp_912_;
}
v___jp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_string_append(v___x_911_, v___y_913_);
lean_dec_ref(v___y_913_);
v___x_915_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v_date_907_);
lean_ctor_set(v___x_915_, 2, v_rev_908_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr___override(lean_object* v_n_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_923_ = ((lean_object*)(l_Lake_ToolchainVer_pr___override___closed__0));
lean_inc(v_n_922_);
v___x_924_ = l_Nat_reprFast(v_n_922_);
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
lean_dec_ref(v___x_924_);
v___x_926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v_n_922_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other___override(lean_object* v_v_927_){
_start:
{
lean_object* v___x_928_; 
lean_inc_ref(v_v_927_);
v___x_928_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_928_, 0, v_v_927_);
lean_ctor_set(v___x_928_, 1, v_v_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override(lean_object* v_x_929_){
_start:
{
lean_object* v_toString_930_; 
v_toString_930_ = lean_ctor_get(v_x_929_, 0);
lean_inc_ref(v_toString_930_);
return v_toString_930_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override___boxed(lean_object* v_x_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lake_ToolchainVer_toString___override(v_x_931_);
lean_dec_ref(v_x_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1));
return v___x_941_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_953_; 
v_val_942_ = lean_ctor_get(v_x_939_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v_x_939_);
if (v_isSharedCheck_953_ == 0)
{
v___x_944_ = v_x_939_;
v_isShared_945_ = v_isSharedCheck_953_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v_x_939_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_953_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_946_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3));
v___x_947_ = l_Nat_reprFast(v_val_942_);
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 3);
lean_ctor_set(v___x_944_, 0, v___x_947_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_952_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_946_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Repr_addAppParen(v___x_950_, v_x_940_);
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___boxed(lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_x_954_, v_x_955_);
lean_dec(v_x_955_);
return v_res_956_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__3(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(2u);
v___x_964_ = lean_nat_to_int(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__4(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_to_int(v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr(lean_object* v_x_985_, lean_object* v_prec_986_){
_start:
{
switch(lean_obj_tag(v_x_985_))
{
case 0:
{
lean_object* v_ver_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1006_; 
v_ver_987_ = lean_ctor_get(v_x_985_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_x_985_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v_x_985_, 0);
lean_dec(v_unused_1007_);
v___x_989_ = v_x_985_;
v_isShared_990_ = v_isSharedCheck_1006_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_ver_987_);
lean_dec(v_x_985_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1006_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___y_992_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(1024u);
v___x_1003_ = lean_nat_dec_le(v___x_1002_, v_prec_986_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_992_ = v___x_1004_;
goto v___jp_991_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_992_ = v___x_1005_;
goto v___jp_991_;
}
v___jp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_993_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__2));
v___x_994_ = l_Lake_instReprStdVer_repr___redArg(v_ver_987_);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 5);
lean_ctor_set(v___x_989_, 1, v___x_994_);
lean_ctor_set(v___x_989_, 0, v___x_993_);
v___x_996_ = v___x_989_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_1001_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_inc(v___y_992_);
v___x_997_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_997_, 0, v___y_992_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = 0;
v___x_999_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*1, v___x_998_);
v___x_1000_ = l_Repr_addAppParen(v___x_999_, v_prec_986_);
return v___x_1000_;
}
}
}
}
case 1:
{
lean_object* v_date_1008_; lean_object* v_rev_1009_; lean_object* v___y_1011_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_date_1008_ = lean_ctor_get(v_x_985_, 1);
lean_inc_ref(v_date_1008_);
v_rev_1009_ = lean_ctor_get(v_x_985_, 2);
lean_inc(v_rev_1009_);
lean_dec_ref_known(v_x_985_, 3);
v___x_1024_ = lean_unsigned_to_nat(1024u);
v___x_1025_ = lean_nat_dec_le(v___x_1024_, v_prec_986_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1011_ = v___x_1026_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1011_ = v___x_1027_;
goto v___jp_1010_;
}
v___jp_1010_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1012_ = lean_box(1);
v___x_1013_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__7));
v___x_1014_ = lean_unsigned_to_nat(1024u);
v___x_1015_ = l_Lake_instReprDate_repr___redArg(v_date_1008_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1013_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_1012_);
v___x_1018_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_rev_1009_, v___x_1014_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
lean_inc(v___y_1011_);
v___x_1020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___y_1011_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = 0;
v___x_1022_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set_uint8(v___x_1022_, sizeof(void*)*1, v___x_1021_);
v___x_1023_ = l_Repr_addAppParen(v___x_1022_, v_prec_986_);
return v___x_1023_;
}
}
case 2:
{
lean_object* v_n_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1048_; 
v_n_1028_ = lean_ctor_get(v_x_985_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_x_985_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_x_985_, 0);
lean_dec(v_unused_1049_);
v___x_1030_ = v_x_985_;
v_isShared_1031_ = v_isSharedCheck_1048_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_n_1028_);
lean_dec(v_x_985_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1048_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___y_1033_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_unsigned_to_nat(1024u);
v___x_1045_ = lean_nat_dec_le(v___x_1044_, v_prec_986_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1033_ = v___x_1046_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1033_ = v___x_1047_;
goto v___jp_1032_;
}
v___jp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1034_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__10));
v___x_1035_ = l_Nat_reprFast(v_n_1028_);
v___x_1036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 5);
lean_ctor_set(v___x_1030_, 1, v___x_1036_);
lean_ctor_set(v___x_1030_, 0, v___x_1034_);
v___x_1038_ = v___x_1030_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_inc(v___y_1033_);
v___x_1039_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___y_1033_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = 0;
v___x_1041_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*1, v___x_1040_);
v___x_1042_ = l_Repr_addAppParen(v___x_1041_, v_prec_986_);
return v___x_1042_;
}
}
}
}
default: 
{
lean_object* v_v_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1070_; 
v_v_1050_ = lean_ctor_get(v_x_985_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_x_985_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v_x_985_, 0);
lean_dec(v_unused_1071_);
v___x_1052_ = v_x_985_;
v_isShared_1053_ = v_isSharedCheck_1070_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_v_1050_);
lean_dec(v_x_985_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1070_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___y_1055_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(1024u);
v___x_1067_ = lean_nat_dec_le(v___x_1066_, v_prec_986_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1055_ = v___x_1068_;
goto v___jp_1054_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1055_ = v___x_1069_;
goto v___jp_1054_;
}
v___jp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1056_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__13));
v___x_1057_ = l_String_quote(v_v_1050_);
v___x_1058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 5);
lean_ctor_set(v___x_1052_, 1, v___x_1058_);
lean_ctor_set(v___x_1052_, 0, v___x_1056_);
v___x_1060_ = v___x_1052_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_inc(v___y_1055_);
v___x_1061_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___y_1055_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = 0;
v___x_1063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*1, v___x_1062_);
v___x_1064_ = l_Repr_addAppParen(v___x_1063_, v_prec_986_);
return v___x_1064_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr___boxed(lean_object* v_x_1072_, lean_object* v_prec_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lake_instReprToolchainVer_repr(v_x_1072_, v_prec_1073_);
lean_dec(v_prec_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer_decEq(lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
switch(lean_obj_tag(v_x_1077_))
{
case 0:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
lean_object* v_ver_1079_; lean_object* v_ver_1080_; uint8_t v___x_1081_; 
v_ver_1079_ = lean_ctor_get(v_x_1077_, 1);
lean_inc_ref(v_ver_1079_);
lean_dec_ref_known(v_x_1077_, 2);
v_ver_1080_ = lean_ctor_get(v_x_1078_, 1);
lean_inc_ref(v_ver_1080_);
lean_dec_ref_known(v_x_1078_, 2);
v___x_1081_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_1079_, v_ver_1080_);
lean_dec_ref(v_ver_1080_);
lean_dec_ref(v_ver_1079_);
return v___x_1081_;
}
else
{
uint8_t v___x_1082_; 
lean_dec_ref_known(v_x_1077_, 2);
lean_dec_ref(v_x_1078_);
v___x_1082_ = 0;
return v___x_1082_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1078_) == 1)
{
lean_object* v_date_1083_; lean_object* v_rev_1084_; lean_object* v_date_1085_; lean_object* v_rev_1086_; uint8_t v___x_1087_; 
v_date_1083_ = lean_ctor_get(v_x_1077_, 1);
lean_inc_ref(v_date_1083_);
v_rev_1084_ = lean_ctor_get(v_x_1077_, 2);
lean_inc(v_rev_1084_);
lean_dec_ref_known(v_x_1077_, 3);
v_date_1085_ = lean_ctor_get(v_x_1078_, 1);
lean_inc_ref(v_date_1085_);
v_rev_1086_ = lean_ctor_get(v_x_1078_, 2);
lean_inc(v_rev_1086_);
lean_dec_ref_known(v_x_1078_, 3);
v___x_1087_ = l_Lake_instDecidableEqDate_decEq(v_date_1083_, v_date_1085_);
lean_dec_ref(v_date_1085_);
lean_dec_ref(v_date_1083_);
if (v___x_1087_ == 0)
{
lean_dec(v_rev_1086_);
lean_dec(v_rev_1084_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_1089_ = l_Option_instDecidableEq___redArg(v___x_1088_, v_rev_1084_, v_rev_1086_);
return v___x_1089_;
}
}
else
{
uint8_t v___x_1090_; 
lean_dec_ref_known(v_x_1077_, 3);
lean_dec_ref(v_x_1078_);
v___x_1090_ = 0;
return v___x_1090_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1078_) == 2)
{
lean_object* v_n_1091_; lean_object* v_n_1092_; uint8_t v___x_1093_; 
v_n_1091_ = lean_ctor_get(v_x_1077_, 1);
lean_inc(v_n_1091_);
lean_dec_ref_known(v_x_1077_, 2);
v_n_1092_ = lean_ctor_get(v_x_1078_, 1);
lean_inc(v_n_1092_);
lean_dec_ref_known(v_x_1078_, 2);
v___x_1093_ = lean_nat_dec_eq(v_n_1091_, v_n_1092_);
lean_dec(v_n_1092_);
lean_dec(v_n_1091_);
return v___x_1093_;
}
else
{
uint8_t v___x_1094_; 
lean_dec_ref_known(v_x_1077_, 2);
lean_dec_ref(v_x_1078_);
v___x_1094_ = 0;
return v___x_1094_;
}
}
default: 
{
if (lean_obj_tag(v_x_1078_) == 3)
{
lean_object* v_v_1095_; lean_object* v_v_1096_; uint8_t v___x_1097_; 
v_v_1095_ = lean_ctor_get(v_x_1077_, 1);
lean_inc_ref(v_v_1095_);
lean_dec_ref_known(v_x_1077_, 2);
v_v_1096_ = lean_ctor_get(v_x_1078_, 1);
lean_inc_ref(v_v_1096_);
lean_dec_ref_known(v_x_1078_, 2);
v___x_1097_ = lean_string_dec_eq(v_v_1095_, v_v_1096_);
lean_dec_ref(v_v_1096_);
lean_dec_ref(v_v_1095_);
return v___x_1097_;
}
else
{
uint8_t v___x_1098_; 
lean_dec_ref_known(v_x_1077_, 2);
lean_dec_ref(v_x_1078_);
v___x_1098_ = 0;
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer_decEq___boxed(lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
uint8_t v_res_1101_; lean_object* v_r_1102_; 
v_res_1101_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1099_, v_x_1100_);
v_r_1102_ = lean_box(v_res_1101_);
return v_r_1102_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer(lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1103_, v_x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer___boxed(lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
uint8_t v_res_1108_; lean_object* v_r_1109_; 
v_res_1108_ = l_Lake_instDecidableEqToolchainVer(v_x_1106_, v_x_1107_);
v_r_1109_ = lean_box(v_res_1108_);
return v_r_1109_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1114_ = lean_string_utf8_byte_size(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(lean_object* v_s_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1116_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1117_ = lean_string_utf8_byte_size(v_s_1115_);
v___x_1118_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1);
v___x_1119_ = lean_nat_dec_le(v___x_1118_, v___x_1117_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v_s_1115_);
v___x_1120_ = lean_box(0);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_string_memcmp(v_s_1115_, v___x_1116_, v___x_1121_, v___x_1121_, v___x_1118_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v_s_1115_);
v___x_1123_ = lean_box(0);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_inc_ref(v_s_1115_);
v___x_1124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1124_, 0, v_s_1115_);
lean_ctor_set(v___x_1124_, 1, v___x_1121_);
lean_ctor_set(v___x_1124_, 2, v___x_1117_);
v___x_1125_ = l_String_Slice_pos_x21(v___x_1124_, v___x_1118_);
lean_dec_ref_known(v___x_1124_, 3);
v___x_1126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1126_, 0, v_s_1115_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
lean_ctor_set(v___x_1126_, 2, v___x_1117_);
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(lean_object* v_s_1128_, lean_object* v_pat_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v_s_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(lean_object* v_s_1131_, lean_object* v_pat_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(v_s_1131_, v_pat_1132_);
lean_dec_ref(v_pat_1132_);
return v_res_1133_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1135_ = lean_string_utf8_byte_size(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(lean_object* v_s_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1137_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1138_ = lean_string_utf8_byte_size(v_s_1136_);
v___x_1139_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0);
v___x_1140_ = lean_nat_dec_le(v___x_1139_, v___x_1138_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref(v_s_1136_);
v___x_1141_ = lean_box(0);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = lean_string_memcmp(v_s_1136_, v___x_1137_, v___x_1142_, v___x_1142_, v___x_1139_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref(v_s_1136_);
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_inc_ref(v_s_1136_);
v___x_1145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1145_, 0, v_s_1136_);
lean_ctor_set(v___x_1145_, 1, v___x_1142_);
lean_ctor_set(v___x_1145_, 2, v___x_1138_);
v___x_1146_ = l_String_Slice_pos_x21(v___x_1145_, v___x_1139_);
lean_dec_ref_known(v___x_1145_, 3);
v___x_1147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1147_, 0, v_s_1136_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
lean_ctor_set(v___x_1147_, 2, v___x_1138_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(lean_object* v_s_1149_, lean_object* v_pat_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v_s_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(lean_object* v_s_1152_, lean_object* v_pat_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(v_s_1152_, v_pat_1153_);
lean_dec_ref(v_pat_1153_);
return v_res_1154_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0));
v___x_1157_ = lean_string_utf8_byte_size(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object* v_s_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1159_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0));
v___x_1160_ = lean_string_utf8_byte_size(v_s_1158_);
v___x_1161_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1);
v___x_1162_ = lean_nat_dec_le(v___x_1161_, v___x_1160_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
lean_dec_ref(v_s_1158_);
v___x_1163_ = lean_box(0);
return v___x_1163_;
}
else
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(0u);
v___x_1165_ = lean_string_memcmp(v_s_1158_, v___x_1159_, v___x_1164_, v___x_1164_, v___x_1161_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec_ref(v_s_1158_);
v___x_1166_ = lean_box(0);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_inc_ref(v_s_1158_);
v___x_1167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1167_, 0, v_s_1158_);
lean_ctor_set(v___x_1167_, 1, v___x_1164_);
lean_ctor_set(v___x_1167_, 2, v___x_1160_);
v___x_1168_ = l_String_Slice_pos_x21(v___x_1167_, v___x_1161_);
lean_dec_ref_known(v___x_1167_, 3);
v___x_1169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1169_, 0, v_s_1158_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
lean_ctor_set(v___x_1169_, 2, v___x_1160_);
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(lean_object* v_s_1171_, lean_object* v_pat_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v_s_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object* v_s_1174_, lean_object* v_pat_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(v_s_1174_, v_pat_1175_);
lean_dec_ref(v_pat_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(lean_object* v___x_1177_, lean_object* v_ver_1178_, lean_object* v_a_1179_, lean_object* v_b_1180_){
_start:
{
lean_object* v_startInclusive_1181_; lean_object* v_endExclusive_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_startInclusive_1181_ = lean_ctor_get(v___x_1177_, 1);
v_endExclusive_1182_ = lean_ctor_get(v___x_1177_, 2);
v___x_1183_ = lean_nat_sub(v_endExclusive_1182_, v_startInclusive_1181_);
v___x_1184_ = lean_nat_dec_eq(v_a_1179_, v___x_1183_);
lean_dec(v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint32_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1185_ = lean_string_utf8_get_fast(v_ver_1178_, v_a_1179_);
v___x_1186_ = 58;
v___x_1187_ = lean_uint32_dec_eq(v___x_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_string_utf8_next_fast(v_ver_1178_, v_a_1179_);
lean_dec(v_a_1179_);
v_a_1179_ = v___x_1189_;
v_b_1180_ = v___x_1188_;
goto _start;
}
else
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_a_1179_);
return v___x_1191_;
}
}
else
{
lean_dec(v_a_1179_);
lean_inc(v_b_1180_);
return v_b_1180_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg___boxed(lean_object* v___x_1192_, lean_object* v_ver_1193_, lean_object* v_a_1194_, lean_object* v_b_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1192_, v_ver_1193_, v_a_1194_, v_b_1195_);
lean_dec(v_b_1195_);
lean_dec_ref(v_ver_1193_);
lean_dec_ref(v___x_1192_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object* v___x_1197_, lean_object* v_rest_1198_, lean_object* v_a_1199_, lean_object* v_b_1200_){
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
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_string_utf8_next_fast(v_rest_1198_, v_a_1199_);
lean_dec(v_a_1199_);
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_add(v_b_1200_, v___x_1206_);
lean_dec(v_b_1200_);
v_a_1199_ = v___x_1205_;
v_b_1200_ = v___x_1207_;
goto _start;
}
else
{
lean_dec(v_a_1199_);
return v_b_1200_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg___boxed(lean_object* v___x_1209_, lean_object* v_rest_1210_, lean_object* v_a_1211_, lean_object* v_b_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___x_1209_, v_rest_1210_, v_a_1211_, v_b_1212_);
lean_dec_ref(v_rest_1210_);
lean_dec_ref(v___x_1209_);
return v_res_1213_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1216_ = lean_string_utf8_byte_size(v___x_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__2(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1218_ = lean_string_utf8_byte_size(v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__4(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__3));
v___x_1221_ = lean_string_utf8_byte_size(v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofString(lean_object* v_ver_1222_){
_start:
{
uint8_t v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; uint8_t v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; uint8_t v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v_fst_1319_; lean_object* v_snd_1320_; lean_object* v___y_1345_; lean_object* v_searcher_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v_searcher_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_string_utf8_byte_size(v_ver_1222_);
lean_inc_ref(v_ver_1222_);
v___x_1355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1355_, 0, v_ver_1222_);
lean_ctor_set(v___x_1355_, 1, v_searcher_1353_);
lean_ctor_set(v___x_1355_, 2, v___x_1354_);
v___x_1356_ = lean_box(0);
v___x_1357_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1355_, v_ver_1222_, v_searcher_1353_, v___x_1356_);
lean_dec_ref_known(v___x_1355_, 3);
if (lean_obj_tag(v___x_1357_) == 0)
{
v___y_1345_ = v___x_1354_;
goto v___jp_1344_;
}
else
{
lean_object* v_val_1358_; 
v_val_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_val_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___y_1345_ = v_val_1358_;
goto v___jp_1344_;
}
v___jp_1223_:
{
if (v___y_1224_ == 0)
{
lean_object* v___x_1229_; 
v___x_1229_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v___y_1228_);
if (lean_obj_tag(v___x_1229_) == 1)
{
lean_object* v_val_1230_; lean_object* v_startInclusive_1231_; lean_object* v_endExclusive_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_val_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v_startInclusive_1231_ = lean_ctor_get(v_val_1230_, 1);
v_endExclusive_1232_ = lean_ctor_get(v_val_1230_, 2);
v___x_1233_ = lean_nat_sub(v_endExclusive_1232_, v_startInclusive_1231_);
v___x_1234_ = lean_nat_dec_eq(v___x_1233_, v___y_1226_);
lean_dec(v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1235_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1236_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__1, &l_Lake_ToolchainVer_ofString___closed__1_once, _init_l_Lake_ToolchainVer_ofString___closed__1);
v___x_1237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___y_1226_);
lean_ctor_set(v___x_1237_, 2, v___x_1236_);
v___x_1238_ = l_String_Slice_beq(v_val_1230_, v___x_1237_);
lean_dec_ref_known(v___x_1237_, 3);
lean_dec(v_val_1230_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1225_);
lean_inc_ref(v_ver_1222_);
v___x_1239_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_ver_1222_);
lean_ctor_set(v___x_1239_, 1, v_ver_1222_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; 
lean_dec_ref(v_ver_1222_);
v___x_1240_ = l_Lake_ToolchainVer_nightly___override(v___y_1227_, v___y_1225_);
return v___x_1240_;
}
}
else
{
lean_object* v___x_1241_; 
lean_dec(v_val_1230_);
lean_dec(v___y_1226_);
lean_dec_ref(v_ver_1222_);
v___x_1241_ = l_Lake_ToolchainVer_nightly___override(v___y_1227_, v___y_1225_);
return v___x_1241_;
}
}
else
{
lean_object* v___x_1242_; 
lean_dec(v___x_1229_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_inc_ref(v_ver_1222_);
v___x_1242_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1242_, 0, v_ver_1222_);
lean_ctor_set(v___x_1242_, 1, v_ver_1222_);
return v___x_1242_;
}
}
else
{
lean_object* v___x_1243_; 
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1226_);
lean_dec_ref(v_ver_1222_);
v___x_1243_ = l_Lake_ToolchainVer_nightly___override(v___y_1227_, v___y_1225_);
return v___x_1243_;
}
}
v___jp_1244_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1253_ = l_String_Slice_positions(v___y_1247_);
lean_inc(v___y_1248_);
v___x_1254_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___y_1247_, v___y_1246_, v___x_1253_, v___y_1248_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___y_1247_);
v___x_1255_ = lean_nat_dec_le(v___x_1254_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec(v___x_1254_);
if (v___x_1255_ == 0)
{
if (lean_obj_tag(v___y_1252_) == 0)
{
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_dec_ref(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1248_);
lean_inc_ref(v_ver_1222_);
v___x_1256_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1256_, 0, v_ver_1222_);
lean_ctor_set(v___x_1256_, 1, v_ver_1222_);
return v___x_1256_;
}
else
{
v___y_1224_ = v___y_1245_;
v___y_1225_ = v___y_1252_;
v___y_1226_ = v___y_1248_;
v___y_1227_ = v___y_1250_;
v___y_1228_ = v___y_1251_;
goto v___jp_1223_;
}
}
else
{
v___y_1224_ = v___y_1245_;
v___y_1225_ = v___y_1252_;
v___y_1226_ = v___y_1248_;
v___y_1227_ = v___y_1250_;
v___y_1228_ = v___y_1251_;
goto v___jp_1223_;
}
}
else
{
v___y_1224_ = v___y_1245_;
v___y_1225_ = v___y_1252_;
v___y_1226_ = v___y_1248_;
v___y_1227_ = v___y_1250_;
v___y_1228_ = v___y_1251_;
goto v___jp_1223_;
}
}
v___jp_1257_:
{
lean_object* v___x_1265_; 
v___x_1265_ = lean_box(0);
v___y_1245_ = v___y_1258_;
v___y_1246_ = v___y_1259_;
v___y_1247_ = v___y_1260_;
v___y_1248_ = v___y_1261_;
v___y_1249_ = v___y_1262_;
v___y_1250_ = v___y_1263_;
v___y_1251_ = v___y_1264_;
v___y_1252_ = v___x_1265_;
goto v___jp_1244_;
}
v___jp_1266_:
{
lean_object* v___x_1271_; 
lean_inc_ref(v___y_1269_);
v___x_1271_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v___y_1269_);
if (lean_obj_tag(v___x_1271_) == 1)
{
lean_object* v_val_1272_; lean_object* v_rest_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref(v___y_1269_);
v_val_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_val_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v_rest_1273_ = l_String_Slice_toString(v_val_1272_);
lean_dec(v_val_1272_);
v___x_1274_ = lean_unsigned_to_nat(10u);
v___x_1275_ = lean_string_utf8_byte_size(v_rest_1273_);
lean_inc_n(v___y_1268_, 3);
lean_inc_ref_n(v_rest_1273_, 2);
v___x_1276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1276_, 0, v_rest_1273_);
lean_ctor_set(v___x_1276_, 1, v___y_1268_);
lean_ctor_set(v___x_1276_, 2, v___x_1275_);
v___x_1277_ = l_String_Slice_Pos_nextn(v___x_1276_, v___y_1268_, v___x_1274_);
lean_inc(v___x_1277_);
v___x_1278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1278_, 0, v_rest_1273_);
lean_ctor_set(v___x_1278_, 1, v___y_1268_);
lean_ctor_set(v___x_1278_, 2, v___x_1277_);
v___x_1279_ = l_String_Slice_toString(v___x_1278_);
lean_dec_ref_known(v___x_1278_, 3);
v___x_1280_ = l_Lake_Date_ofString_x3f(v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 1)
{
lean_object* v_val_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1283_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__2, &l_Lake_ToolchainVer_ofString___closed__2_once, _init_l_Lake_ToolchainVer_ofString___closed__2);
v___x_1284_ = lean_nat_sub(v___x_1275_, v___x_1277_);
v___x_1285_ = lean_nat_dec_le(v___x_1283_, v___x_1284_);
lean_dec(v___x_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v___x_1277_);
v___y_1258_ = v___y_1267_;
v___y_1259_ = v_rest_1273_;
v___y_1260_ = v___x_1276_;
v___y_1261_ = v___y_1268_;
v___y_1262_ = v___x_1274_;
v___y_1263_ = v_val_1281_;
v___y_1264_ = v___y_1270_;
goto v___jp_1257_;
}
else
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_string_memcmp(v_rest_1273_, v___x_1282_, v___x_1277_, v___y_1268_, v___x_1283_);
if (v___x_1286_ == 0)
{
lean_dec(v___x_1277_);
v___y_1258_ = v___y_1267_;
v___y_1259_ = v_rest_1273_;
v___y_1260_ = v___x_1276_;
v___y_1261_ = v___y_1268_;
v___y_1262_ = v___x_1274_;
v___y_1263_ = v_val_1281_;
v___y_1264_ = v___y_1270_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_inc(v___x_1277_);
lean_inc_ref_n(v_rest_1273_, 2);
v___x_1287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1287_, 0, v_rest_1273_);
lean_ctor_set(v___x_1287_, 1, v___x_1277_);
lean_ctor_set(v___x_1287_, 2, v___x_1275_);
v___x_1288_ = l_String_Slice_pos_x21(v___x_1287_, v___x_1283_);
lean_dec_ref_known(v___x_1287_, 3);
v___x_1289_ = lean_nat_add(v___x_1277_, v___x_1288_);
lean_dec(v___x_1288_);
lean_dec(v___x_1277_);
v___x_1290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1290_, 0, v_rest_1273_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
lean_ctor_set(v___x_1290_, 2, v___x_1275_);
v___x_1291_ = l_String_Slice_toString(v___x_1290_);
lean_dec_ref_known(v___x_1290_, 3);
v___x_1292_ = lean_string_utf8_byte_size(v___x_1291_);
lean_inc(v___y_1268_);
v___x_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___y_1268_);
lean_ctor_set(v___x_1293_, 2, v___x_1292_);
v___x_1294_ = l_String_Slice_toNat_x3f(v___x_1293_);
lean_dec_ref_known(v___x_1293_, 3);
v___y_1245_ = v___y_1267_;
v___y_1246_ = v_rest_1273_;
v___y_1247_ = v___x_1276_;
v___y_1248_ = v___y_1268_;
v___y_1249_ = v___x_1274_;
v___y_1250_ = v_val_1281_;
v___y_1251_ = v___y_1270_;
v___y_1252_ = v___x_1294_;
goto v___jp_1244_;
}
}
}
else
{
lean_object* v___x_1295_; 
lean_dec(v___x_1280_);
lean_dec(v___x_1277_);
lean_dec_ref_known(v___x_1276_, 3);
lean_dec_ref(v_rest_1273_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1268_);
lean_inc_ref(v_ver_1222_);
v___x_1295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_ver_1222_);
lean_ctor_set(v___x_1295_, 1, v_ver_1222_);
return v___x_1295_;
}
}
else
{
lean_object* v___x_1296_; 
lean_dec(v___x_1271_);
v___x_1296_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___y_1269_);
if (lean_obj_tag(v___x_1296_) == 1)
{
lean_object* v_val_1297_; lean_object* v___x_1298_; 
lean_dec(v___y_1268_);
v_val_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1298_ = l_String_Slice_toNat_x3f(v_val_1297_);
lean_dec(v_val_1297_);
if (lean_obj_tag(v___x_1298_) == 1)
{
if (v___y_1267_ == 0)
{
lean_object* v_val_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_val_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1300_ = ((lean_object*)(l_Lake_ToolchainVer_prOrigin___closed__0));
v___x_1301_ = lean_string_dec_eq(v___y_1270_, v___x_1300_);
lean_dec_ref(v___y_1270_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec(v_val_1299_);
lean_inc_ref(v_ver_1222_);
v___x_1302_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_ver_1222_);
lean_ctor_set(v___x_1302_, 1, v_ver_1222_);
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; 
lean_dec_ref(v_ver_1222_);
v___x_1303_ = l_Lake_ToolchainVer_pr___override(v_val_1299_);
return v___x_1303_;
}
}
else
{
lean_object* v_val_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v___y_1270_);
lean_dec_ref(v_ver_1222_);
v_val_1304_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1305_ = l_Lake_ToolchainVer_pr___override(v_val_1304_);
return v___x_1305_;
}
}
else
{
lean_object* v___x_1306_; 
lean_dec(v___x_1298_);
lean_dec_ref(v___y_1270_);
lean_inc_ref(v_ver_1222_);
v___x_1306_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_ver_1222_);
lean_ctor_set(v___x_1306_, 1, v_ver_1222_);
return v___x_1306_;
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec(v___x_1296_);
v___x_1307_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_1308_ = lean_string_utf8_byte_size(v_ver_1222_);
lean_inc_ref(v_ver_1222_);
v___x_1309_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_ver_1222_, v___x_1307_, v___y_1268_, v___x_1308_);
if (lean_obj_tag(v___x_1309_) == 1)
{
if (v___y_1267_ == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1312_ = lean_string_dec_eq(v___y_1270_, v___x_1311_);
lean_dec_ref(v___y_1270_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec(v_a_1310_);
lean_inc_ref(v_ver_1222_);
v___x_1313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_ver_1222_);
lean_ctor_set(v___x_1313_, 1, v_ver_1222_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; 
lean_dec_ref(v_ver_1222_);
v___x_1314_ = l_Lake_ToolchainVer_release___override(v_a_1310_);
return v___x_1314_;
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1316_; 
lean_dec_ref(v___y_1270_);
lean_dec_ref(v_ver_1222_);
v_a_1315_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1316_ = l_Lake_ToolchainVer_release___override(v_a_1315_);
return v___x_1316_;
}
}
else
{
lean_object* v___x_1317_; 
lean_dec_ref(v___x_1309_);
lean_dec_ref(v___y_1270_);
lean_inc_ref(v_ver_1222_);
v___x_1317_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1317_, 0, v_ver_1222_);
lean_ctor_set(v___x_1317_, 1, v_ver_1222_);
return v___x_1317_;
}
}
}
}
v___jp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v_noOrigin_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1321_ = lean_string_utf8_byte_size(v_fst_1319_);
v___x_1322_ = lean_unsigned_to_nat(0u);
v_noOrigin_1323_ = lean_nat_dec_eq(v___x_1321_, v___x_1322_);
v___x_1324_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__3));
v___x_1325_ = lean_string_utf8_byte_size(v_snd_1320_);
v___x_1326_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__4, &l_Lake_ToolchainVer_ofString___closed__4_once, _init_l_Lake_ToolchainVer_ofString___closed__4);
v___x_1327_ = lean_nat_dec_le(v___x_1326_, v___x_1325_);
if (v___x_1327_ == 0)
{
v___y_1267_ = v_noOrigin_1323_;
v___y_1268_ = v___x_1322_;
v___y_1269_ = v_snd_1320_;
v___y_1270_ = v_fst_1319_;
goto v___jp_1266_;
}
else
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_string_memcmp(v_snd_1320_, v___x_1324_, v___x_1322_, v___x_1322_, v___x_1326_);
if (v___x_1328_ == 0)
{
v___y_1267_ = v_noOrigin_1323_;
v___y_1268_ = v___x_1322_;
v___y_1269_ = v_snd_1320_;
v___y_1270_ = v_fst_1319_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1329_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_snd_1320_);
v___x_1330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1330_, 0, v_snd_1320_);
lean_ctor_set(v___x_1330_, 1, v___x_1322_);
lean_ctor_set(v___x_1330_, 2, v___x_1325_);
v___x_1331_ = l_String_Slice_Pos_nextn(v___x_1330_, v___x_1322_, v___x_1329_);
lean_dec_ref_known(v___x_1330_, 3);
v___x_1332_ = lean_string_utf8_extract(v_snd_1320_, v___x_1331_, v___x_1325_);
lean_dec(v___x_1331_);
lean_dec_ref(v_snd_1320_);
v___x_1333_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_1334_ = lean_string_utf8_byte_size(v___x_1332_);
v___x_1335_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v___x_1332_, v___x_1333_, v___x_1322_, v___x_1334_);
if (lean_obj_tag(v___x_1335_) == 1)
{
if (v_noOrigin_1323_ == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1338_ = lean_string_dec_eq(v_fst_1319_, v___x_1337_);
lean_dec_ref(v_fst_1319_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec(v_a_1336_);
lean_inc_ref(v_ver_1222_);
v___x_1339_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_ver_1222_);
lean_ctor_set(v___x_1339_, 1, v_ver_1222_);
return v___x_1339_;
}
else
{
lean_object* v___x_1340_; 
lean_dec_ref(v_ver_1222_);
v___x_1340_ = l_Lake_ToolchainVer_release___override(v_a_1336_);
return v___x_1340_;
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v_fst_1319_);
lean_dec_ref(v_ver_1222_);
v_a_1341_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1342_ = l_Lake_ToolchainVer_release___override(v_a_1341_);
return v___x_1342_;
}
}
else
{
lean_object* v___x_1343_; 
lean_dec_ref(v___x_1335_);
lean_dec_ref(v_fst_1319_);
lean_inc_ref(v_ver_1222_);
v___x_1343_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1343_, 0, v_ver_1222_);
lean_ctor_set(v___x_1343_, 1, v_ver_1222_);
return v___x_1343_;
}
}
}
}
v___jp_1344_:
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = lean_string_utf8_byte_size(v_ver_1222_);
v___x_1347_ = lean_nat_dec_eq(v___y_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v_pos_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_pos_1348_ = lean_string_utf8_next_fast(v_ver_1222_, v___y_1345_);
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_string_utf8_extract(v_ver_1222_, v___x_1349_, v___y_1345_);
lean_dec(v___y_1345_);
v___x_1351_ = lean_string_utf8_extract(v_ver_1222_, v_pos_1348_, v___x_1346_);
v_fst_1319_ = v___x_1350_;
v_snd_1320_ = v___x_1351_;
goto v___jp_1318_;
}
else
{
lean_object* v___x_1352_; 
lean_dec(v___y_1345_);
v___x_1352_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
lean_inc_ref(v_ver_1222_);
v_fst_1319_ = v___x_1352_;
v_snd_1320_ = v_ver_1222_;
goto v___jp_1318_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(lean_object* v___x_1359_, lean_object* v_rest_1360_, lean_object* v_inst_1361_, lean_object* v_R_1362_, lean_object* v_a_1363_, lean_object* v_b_1364_, lean_object* v_c_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___x_1359_, v_rest_1360_, v_a_1363_, v_b_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object* v___x_1367_, lean_object* v_rest_1368_, lean_object* v_inst_1369_, lean_object* v_R_1370_, lean_object* v_a_1371_, lean_object* v_b_1372_, lean_object* v_c_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(v___x_1367_, v_rest_1368_, v_inst_1369_, v_R_1370_, v_a_1371_, v_b_1372_, v_c_1373_);
lean_dec_ref(v_rest_1368_);
lean_dec_ref(v___x_1367_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(lean_object* v___x_1375_, lean_object* v_ver_1376_, lean_object* v_inst_1377_, lean_object* v_R_1378_, lean_object* v_a_1379_, lean_object* v_b_1380_, lean_object* v_c_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1375_, v_ver_1376_, v_a_1379_, v_b_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___boxed(lean_object* v___x_1383_, lean_object* v_ver_1384_, lean_object* v_inst_1385_, lean_object* v_R_1386_, lean_object* v_a_1387_, lean_object* v_b_1388_, lean_object* v_c_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(v___x_1383_, v_ver_1384_, v_inst_1385_, v_R_1386_, v_a_1387_, v_b_1388_, v_c_1389_);
lean_dec(v_b_1388_);
lean_dec_ref(v_ver_1384_);
lean_dec_ref(v___x_1383_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object* v_toolchainFile_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_IO_FS_readFile(v_toolchainFile_1391_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1411_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1411_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1411_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v_str_1402_; lean_object* v_startInclusive_1403_; lean_object* v_endExclusive_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = lean_string_utf8_byte_size(v_a_1394_);
v___x_1400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1400_, 0, v_a_1394_);
lean_ctor_set(v___x_1400_, 1, v___x_1398_);
lean_ctor_set(v___x_1400_, 2, v___x_1399_);
v___x_1401_ = l_String_Slice_trimAscii(v___x_1400_);
v_str_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc_ref(v_str_1402_);
v_startInclusive_1403_ = lean_ctor_get(v___x_1401_, 1);
lean_inc(v_startInclusive_1403_);
v_endExclusive_1404_ = lean_ctor_get(v___x_1401_, 2);
lean_inc(v_endExclusive_1404_);
lean_dec_ref(v___x_1401_);
v___x_1405_ = lean_string_utf8_extract(v_str_1402_, v_startInclusive_1403_, v_endExclusive_1404_);
lean_dec(v_endExclusive_1404_);
lean_dec(v_startInclusive_1403_);
lean_dec_ref(v_str_1402_);
v___x_1406_ = l_Lake_ToolchainVer_ofString(v___x_1405_);
v___x_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1407_);
v___x_1409_ = v___x_1396_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1423_; 
v_a_1412_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1414_ = v___x_1393_;
v_isShared_1415_ = v_isSharedCheck_1423_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1393_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1423_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
if (lean_obj_tag(v_a_1412_) == 11)
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_dec_ref_known(v_a_1412_, 2);
v___x_1416_ = lean_box(0);
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1416_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
else
{
lean_object* v___x_1421_; 
if (v_isShared_1415_ == 0)
{
v___x_1421_ = v___x_1414_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1412_);
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
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f___boxed(lean_object* v_toolchainFile_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lake_ToolchainVer_ofFile_x3f(v_toolchainFile_1424_);
lean_dec_ref(v_toolchainFile_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f(lean_object* v_dir_1427_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = ((lean_object*)(l_Lake_toolchainFileName___closed__0));
v___x_1430_ = l_System_FilePath_join(v_dir_1427_, v___x_1429_);
v___x_1431_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1430_);
lean_dec_ref(v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f___boxed(lean_object* v_dir_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lake_ToolchainVer_ofDir_x3f(v_dir_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0(lean_object* v_x_1437_){
_start:
{
lean_object* v_toString_1438_; lean_object* v___x_1439_; 
v_toString_1438_ = lean_ctor_get(v_x_1437_, 0);
lean_inc_ref(v_toString_1438_);
v___x_1439_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1439_, 0, v_toString_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0___boxed(lean_object* v_x_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lake_ToolchainVer_instToJson___lam__0(v_x_1440_);
lean_dec_ref(v_x_1440_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instFromJson___lam__0(lean_object* v_x_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Json_getStr_x3f(v_x_1444_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1462_; 
v_a_1454_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1456_ = v___x_1445_;
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1445_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = l_Lake_ToolchainVer_ofString(v_a_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1460_ = v___x_1456_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_blt(lean_object* v_a_1465_, lean_object* v_b_1466_){
_start:
{
switch(lean_obj_tag(v_a_1465_))
{
case 0:
{
if (lean_obj_tag(v_b_1466_) == 0)
{
lean_object* v_ver_1467_; lean_object* v_ver_1468_; uint8_t v___x_1469_; 
v_ver_1467_ = lean_ctor_get(v_a_1465_, 1);
v_ver_1468_ = lean_ctor_get(v_b_1466_, 1);
v___x_1469_ = l_Lake_StdVer_compare(v_ver_1467_, v_ver_1468_);
if (v___x_1469_ == 0)
{
uint8_t v___x_1470_; 
v___x_1470_ = 1;
return v___x_1470_;
}
else
{
uint8_t v___x_1471_; 
v___x_1471_ = 0;
return v___x_1471_;
}
}
else
{
uint8_t v___x_1472_; 
v___x_1472_ = 0;
return v___x_1472_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1466_) == 1)
{
lean_object* v_date_1473_; lean_object* v_rev_1474_; lean_object* v_date_1475_; lean_object* v_rev_1476_; lean_object* v___y_1478_; uint8_t v___x_1483_; 
v_date_1473_ = lean_ctor_get(v_a_1465_, 1);
v_rev_1474_ = lean_ctor_get(v_a_1465_, 2);
v_date_1475_ = lean_ctor_get(v_b_1466_, 1);
v_rev_1476_ = lean_ctor_get(v_b_1466_, 2);
v___x_1483_ = l_Lake_instOrdDate_ord(v_date_1473_, v_date_1475_);
if (v___x_1483_ == 0)
{
uint8_t v___x_1484_; 
v___x_1484_ = 1;
return v___x_1484_;
}
else
{
uint8_t v___x_1485_; 
v___x_1485_ = l_Lake_instDecidableEqDate_decEq(v_date_1473_, v_date_1475_);
if (v___x_1485_ == 0)
{
return v___x_1485_;
}
else
{
if (lean_obj_tag(v_rev_1474_) == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
v___y_1478_ = v___x_1486_;
goto v___jp_1477_;
}
else
{
lean_object* v_val_1487_; 
v_val_1487_ = lean_ctor_get(v_rev_1474_, 0);
v___y_1478_ = v_val_1487_;
goto v___jp_1477_;
}
}
}
v___jp_1477_:
{
if (lean_obj_tag(v_rev_1476_) == 0)
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = lean_unsigned_to_nat(0u);
v___x_1480_ = lean_nat_dec_lt(v___y_1478_, v___x_1479_);
return v___x_1480_;
}
else
{
lean_object* v_val_1481_; uint8_t v___x_1482_; 
v_val_1481_ = lean_ctor_get(v_rev_1476_, 0);
v___x_1482_ = lean_nat_dec_lt(v___y_1478_, v_val_1481_);
return v___x_1482_;
}
}
}
else
{
uint8_t v___x_1488_; 
v___x_1488_ = 0;
return v___x_1488_;
}
}
default: 
{
uint8_t v___x_1489_; 
v___x_1489_ = 0;
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_blt___boxed(lean_object* v_a_1490_, lean_object* v_b_1491_){
_start:
{
uint8_t v_res_1492_; lean_object* v_r_1493_; 
v_res_1492_ = l_Lake_ToolchainVer_blt(v_a_1490_, v_b_1491_);
lean_dec_ref(v_b_1491_);
lean_dec_ref(v_a_1490_);
v_r_1493_ = lean_box(v_res_1492_);
return v_r_1493_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLT(void){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_box(0);
return v___x_1494_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLt(lean_object* v_a_1495_, lean_object* v_b_1496_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = l_Lake_ToolchainVer_blt(v_a_1495_, v_b_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLt___boxed(lean_object* v_a_1498_, lean_object* v_b_1499_){
_start:
{
uint8_t v_res_1500_; lean_object* v_r_1501_; 
v_res_1500_ = l_Lake_ToolchainVer_decLt(v_a_1498_, v_b_1499_);
lean_dec_ref(v_b_1499_);
lean_dec_ref(v_a_1498_);
v_r_1501_ = lean_box(v_res_1500_);
return v_r_1501_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_ble(lean_object* v_a_1502_, lean_object* v_b_1503_){
_start:
{
switch(lean_obj_tag(v_a_1502_))
{
case 0:
{
if (lean_obj_tag(v_b_1503_) == 0)
{
lean_object* v_ver_1504_; lean_object* v_ver_1505_; uint8_t v___x_1506_; 
v_ver_1504_ = lean_ctor_get(v_a_1502_, 1);
v_ver_1505_ = lean_ctor_get(v_b_1503_, 1);
v___x_1506_ = l_Lake_StdVer_compare(v_ver_1504_, v_ver_1505_);
if (v___x_1506_ == 2)
{
uint8_t v___x_1507_; 
v___x_1507_ = 0;
return v___x_1507_;
}
else
{
uint8_t v___x_1508_; 
v___x_1508_ = 1;
return v___x_1508_;
}
}
else
{
uint8_t v___x_1509_; 
v___x_1509_ = 0;
return v___x_1509_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1503_) == 1)
{
lean_object* v_date_1510_; lean_object* v_rev_1511_; lean_object* v_date_1512_; lean_object* v_rev_1513_; lean_object* v___y_1515_; uint8_t v___x_1520_; 
v_date_1510_ = lean_ctor_get(v_a_1502_, 1);
v_rev_1511_ = lean_ctor_get(v_a_1502_, 2);
v_date_1512_ = lean_ctor_get(v_b_1503_, 1);
v_rev_1513_ = lean_ctor_get(v_b_1503_, 2);
v___x_1520_ = l_Lake_instOrdDate_ord(v_date_1510_, v_date_1512_);
if (v___x_1520_ == 0)
{
uint8_t v___x_1521_; 
v___x_1521_ = 1;
return v___x_1521_;
}
else
{
uint8_t v___x_1522_; 
v___x_1522_ = l_Lake_instDecidableEqDate_decEq(v_date_1510_, v_date_1512_);
if (v___x_1522_ == 0)
{
return v___x_1522_;
}
else
{
if (lean_obj_tag(v_rev_1511_) == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_unsigned_to_nat(0u);
v___y_1515_ = v___x_1523_;
goto v___jp_1514_;
}
else
{
lean_object* v_val_1524_; 
v_val_1524_ = lean_ctor_get(v_rev_1511_, 0);
v___y_1515_ = v_val_1524_;
goto v___jp_1514_;
}
}
}
v___jp_1514_:
{
if (lean_obj_tag(v_rev_1513_) == 0)
{
lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_nat_dec_le(v___y_1515_, v___x_1516_);
return v___x_1517_;
}
else
{
lean_object* v_val_1518_; uint8_t v___x_1519_; 
v_val_1518_ = lean_ctor_get(v_rev_1513_, 0);
v___x_1519_ = lean_nat_dec_le(v___y_1515_, v_val_1518_);
return v___x_1519_;
}
}
}
else
{
uint8_t v___x_1525_; 
v___x_1525_ = 0;
return v___x_1525_;
}
}
case 2:
{
if (lean_obj_tag(v_b_1503_) == 2)
{
lean_object* v_n_1526_; lean_object* v_n_1527_; uint8_t v___x_1528_; 
v_n_1526_ = lean_ctor_get(v_a_1502_, 1);
v_n_1527_ = lean_ctor_get(v_b_1503_, 1);
v___x_1528_ = lean_nat_dec_eq(v_n_1526_, v_n_1527_);
return v___x_1528_;
}
else
{
uint8_t v___x_1529_; 
v___x_1529_ = 0;
return v___x_1529_;
}
}
default: 
{
if (lean_obj_tag(v_b_1503_) == 3)
{
lean_object* v_v_1530_; lean_object* v_v_1531_; uint8_t v___x_1532_; 
v_v_1530_ = lean_ctor_get(v_a_1502_, 1);
v_v_1531_ = lean_ctor_get(v_b_1503_, 1);
v___x_1532_ = lean_string_dec_eq(v_v_1530_, v_v_1531_);
return v___x_1532_;
}
else
{
uint8_t v___x_1533_; 
v___x_1533_ = 0;
return v___x_1533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ble___boxed(lean_object* v_a_1534_, lean_object* v_b_1535_){
_start:
{
uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l_Lake_ToolchainVer_ble(v_a_1534_, v_b_1535_);
lean_dec_ref(v_b_1535_);
lean_dec_ref(v_a_1534_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLE(void){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_box(0);
return v___x_1538_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLe(lean_object* v_a_1539_, lean_object* v_b_1540_){
_start:
{
uint8_t v___x_1541_; 
v___x_1541_ = l_Lake_ToolchainVer_ble(v_a_1539_, v_b_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLe___boxed(lean_object* v_a_1542_, lean_object* v_b_1543_){
_start:
{
uint8_t v_res_1544_; lean_object* v_r_1545_; 
v_res_1544_ = l_Lake_ToolchainVer_decLe(v_a_1542_, v_b_1543_);
lean_dec_ref(v_b_1543_);
lean_dec_ref(v_a_1542_);
v_r_1545_ = lean_box(v_res_1544_);
return v_r_1545_;
}
}
LEAN_EXPORT lean_object* l_Lake_normalizeToolchain(lean_object* v_s_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v_toString_1548_; 
v___x_1547_ = l_Lake_ToolchainVer_ofString(v_s_1546_);
v_toString_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc_ref(v_toString_1548_);
lean_dec_ref(v___x_1547_);
return v_toString_1548_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeVersionToolchainVer___lam__0(lean_object* v_x_1553_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = l_Lake_ToolchainVer_ofString(v_x_1553_);
v___x_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx(uint8_t v_x_1558_){
_start:
{
switch(v_x_1558_)
{
case 0:
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_unsigned_to_nat(0u);
return v___x_1559_;
}
case 1:
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_unsigned_to_nat(1u);
return v___x_1560_;
}
case 2:
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_unsigned_to_nat(2u);
return v___x_1561_;
}
case 3:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_unsigned_to_nat(3u);
return v___x_1562_;
}
case 4:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_unsigned_to_nat(4u);
return v___x_1563_;
}
default: 
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_unsigned_to_nat(5u);
return v___x_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___boxed(lean_object* v_x_1565_){
_start:
{
uint8_t v_x_boxed_1566_; lean_object* v_res_1567_; 
v_x_boxed_1566_ = lean_unbox(v_x_1565_);
v_res_1567_ = l_Lake_ComparatorOp_ctorIdx(v_x_boxed_1566_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx(uint8_t v_x_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lake_ComparatorOp_ctorIdx(v_x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx___boxed(lean_object* v_x_1570_){
_start:
{
uint8_t v_x_4__boxed_1571_; lean_object* v_res_1572_; 
v_x_4__boxed_1571_ = lean_unbox(v_x_1570_);
v_res_1572_ = l_Lake_ComparatorOp_toCtorIdx(v_x_4__boxed_1571_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg(lean_object* v_k_1573_){
_start:
{
lean_inc(v_k_1573_);
return v_k_1573_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg___boxed(lean_object* v_k_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lake_ComparatorOp_ctorElim___redArg(v_k_1574_);
lean_dec(v_k_1574_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim(lean_object* v_motive_1576_, lean_object* v_ctorIdx_1577_, uint8_t v_t_1578_, lean_object* v_h_1579_, lean_object* v_k_1580_){
_start:
{
lean_inc(v_k_1580_);
return v_k_1580_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___boxed(lean_object* v_motive_1581_, lean_object* v_ctorIdx_1582_, lean_object* v_t_1583_, lean_object* v_h_1584_, lean_object* v_k_1585_){
_start:
{
uint8_t v_t_boxed_1586_; lean_object* v_res_1587_; 
v_t_boxed_1586_ = lean_unbox(v_t_1583_);
v_res_1587_ = l_Lake_ComparatorOp_ctorElim(v_motive_1581_, v_ctorIdx_1582_, v_t_boxed_1586_, v_h_1584_, v_k_1585_);
lean_dec(v_k_1585_);
lean_dec(v_ctorIdx_1582_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg(lean_object* v_lt_1588_){
_start:
{
lean_inc(v_lt_1588_);
return v_lt_1588_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg___boxed(lean_object* v_lt_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lake_ComparatorOp_lt_elim___redArg(v_lt_1589_);
lean_dec(v_lt_1589_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim(lean_object* v_motive_1591_, uint8_t v_t_1592_, lean_object* v_h_1593_, lean_object* v_lt_1594_){
_start:
{
lean_inc(v_lt_1594_);
return v_lt_1594_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___boxed(lean_object* v_motive_1595_, lean_object* v_t_1596_, lean_object* v_h_1597_, lean_object* v_lt_1598_){
_start:
{
uint8_t v_t_boxed_1599_; lean_object* v_res_1600_; 
v_t_boxed_1599_ = lean_unbox(v_t_1596_);
v_res_1600_ = l_Lake_ComparatorOp_lt_elim(v_motive_1595_, v_t_boxed_1599_, v_h_1597_, v_lt_1598_);
lean_dec(v_lt_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg(lean_object* v_le_1601_){
_start:
{
lean_inc(v_le_1601_);
return v_le_1601_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg___boxed(lean_object* v_le_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lake_ComparatorOp_le_elim___redArg(v_le_1602_);
lean_dec(v_le_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim(lean_object* v_motive_1604_, uint8_t v_t_1605_, lean_object* v_h_1606_, lean_object* v_le_1607_){
_start:
{
lean_inc(v_le_1607_);
return v_le_1607_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___boxed(lean_object* v_motive_1608_, lean_object* v_t_1609_, lean_object* v_h_1610_, lean_object* v_le_1611_){
_start:
{
uint8_t v_t_boxed_1612_; lean_object* v_res_1613_; 
v_t_boxed_1612_ = lean_unbox(v_t_1609_);
v_res_1613_ = l_Lake_ComparatorOp_le_elim(v_motive_1608_, v_t_boxed_1612_, v_h_1610_, v_le_1611_);
lean_dec(v_le_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg(lean_object* v_gt_1614_){
_start:
{
lean_inc(v_gt_1614_);
return v_gt_1614_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg___boxed(lean_object* v_gt_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lake_ComparatorOp_gt_elim___redArg(v_gt_1615_);
lean_dec(v_gt_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim(lean_object* v_motive_1617_, uint8_t v_t_1618_, lean_object* v_h_1619_, lean_object* v_gt_1620_){
_start:
{
lean_inc(v_gt_1620_);
return v_gt_1620_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___boxed(lean_object* v_motive_1621_, lean_object* v_t_1622_, lean_object* v_h_1623_, lean_object* v_gt_1624_){
_start:
{
uint8_t v_t_boxed_1625_; lean_object* v_res_1626_; 
v_t_boxed_1625_ = lean_unbox(v_t_1622_);
v_res_1626_ = l_Lake_ComparatorOp_gt_elim(v_motive_1621_, v_t_boxed_1625_, v_h_1623_, v_gt_1624_);
lean_dec(v_gt_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg(lean_object* v_ge_1627_){
_start:
{
lean_inc(v_ge_1627_);
return v_ge_1627_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg___boxed(lean_object* v_ge_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lake_ComparatorOp_ge_elim___redArg(v_ge_1628_);
lean_dec(v_ge_1628_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim(lean_object* v_motive_1630_, uint8_t v_t_1631_, lean_object* v_h_1632_, lean_object* v_ge_1633_){
_start:
{
lean_inc(v_ge_1633_);
return v_ge_1633_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___boxed(lean_object* v_motive_1634_, lean_object* v_t_1635_, lean_object* v_h_1636_, lean_object* v_ge_1637_){
_start:
{
uint8_t v_t_boxed_1638_; lean_object* v_res_1639_; 
v_t_boxed_1638_ = lean_unbox(v_t_1635_);
v_res_1639_ = l_Lake_ComparatorOp_ge_elim(v_motive_1634_, v_t_boxed_1638_, v_h_1636_, v_ge_1637_);
lean_dec(v_ge_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg(lean_object* v_eq_1640_){
_start:
{
lean_inc(v_eq_1640_);
return v_eq_1640_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg___boxed(lean_object* v_eq_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lake_ComparatorOp_eq_elim___redArg(v_eq_1641_);
lean_dec(v_eq_1641_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim(lean_object* v_motive_1643_, uint8_t v_t_1644_, lean_object* v_h_1645_, lean_object* v_eq_1646_){
_start:
{
lean_inc(v_eq_1646_);
return v_eq_1646_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___boxed(lean_object* v_motive_1647_, lean_object* v_t_1648_, lean_object* v_h_1649_, lean_object* v_eq_1650_){
_start:
{
uint8_t v_t_boxed_1651_; lean_object* v_res_1652_; 
v_t_boxed_1651_ = lean_unbox(v_t_1648_);
v_res_1652_ = l_Lake_ComparatorOp_eq_elim(v_motive_1647_, v_t_boxed_1651_, v_h_1649_, v_eq_1650_);
lean_dec(v_eq_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg(lean_object* v_ne_1653_){
_start:
{
lean_inc(v_ne_1653_);
return v_ne_1653_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg___boxed(lean_object* v_ne_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lake_ComparatorOp_ne_elim___redArg(v_ne_1654_);
lean_dec(v_ne_1654_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim(lean_object* v_motive_1656_, uint8_t v_t_1657_, lean_object* v_h_1658_, lean_object* v_ne_1659_){
_start:
{
lean_inc(v_ne_1659_);
return v_ne_1659_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___boxed(lean_object* v_motive_1660_, lean_object* v_t_1661_, lean_object* v_h_1662_, lean_object* v_ne_1663_){
_start:
{
uint8_t v_t_boxed_1664_; lean_object* v_res_1665_; 
v_t_boxed_1664_ = lean_unbox(v_t_1661_);
v_res_1665_ = l_Lake_ComparatorOp_ne_elim(v_motive_1660_, v_t_boxed_1664_, v_h_1662_, v_ne_1663_);
lean_dec(v_ne_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr(uint8_t v_x_1684_, lean_object* v_prec_1685_){
_start:
{
lean_object* v___y_1687_; lean_object* v___y_1694_; lean_object* v___y_1701_; lean_object* v___y_1708_; lean_object* v___y_1715_; lean_object* v___y_1722_; 
switch(v_x_1684_)
{
case 0:
{
lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1728_ = lean_unsigned_to_nat(1024u);
v___x_1729_ = lean_nat_dec_le(v___x_1728_, v_prec_1685_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1687_ = v___x_1730_;
goto v___jp_1686_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1687_ = v___x_1731_;
goto v___jp_1686_;
}
}
case 1:
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = lean_unsigned_to_nat(1024u);
v___x_1733_ = lean_nat_dec_le(v___x_1732_, v_prec_1685_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1694_ = v___x_1734_;
goto v___jp_1693_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1694_ = v___x_1735_;
goto v___jp_1693_;
}
}
case 2:
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = lean_unsigned_to_nat(1024u);
v___x_1737_ = lean_nat_dec_le(v___x_1736_, v_prec_1685_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1701_ = v___x_1738_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1701_ = v___x_1739_;
goto v___jp_1700_;
}
}
case 3:
{
lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = lean_unsigned_to_nat(1024u);
v___x_1741_ = lean_nat_dec_le(v___x_1740_, v_prec_1685_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1708_ = v___x_1742_;
goto v___jp_1707_;
}
else
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1708_ = v___x_1743_;
goto v___jp_1707_;
}
}
case 4:
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = lean_unsigned_to_nat(1024u);
v___x_1745_ = lean_nat_dec_le(v___x_1744_, v_prec_1685_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1715_ = v___x_1746_;
goto v___jp_1714_;
}
else
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1715_ = v___x_1747_;
goto v___jp_1714_;
}
}
default: 
{
lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = lean_unsigned_to_nat(1024u);
v___x_1749_ = lean_nat_dec_le(v___x_1748_, v_prec_1685_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1722_ = v___x_1750_;
goto v___jp_1721_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1722_ = v___x_1751_;
goto v___jp_1721_;
}
}
}
v___jp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1688_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__1));
lean_inc(v___y_1687_);
v___x_1689_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___y_1687_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = 0;
v___x_1691_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set_uint8(v___x_1691_, sizeof(void*)*1, v___x_1690_);
v___x_1692_ = l_Repr_addAppParen(v___x_1691_, v_prec_1685_);
return v___x_1692_;
}
v___jp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1695_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__3));
lean_inc(v___y_1694_);
v___x_1696_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___y_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = 0;
v___x_1698_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set_uint8(v___x_1698_, sizeof(void*)*1, v___x_1697_);
v___x_1699_ = l_Repr_addAppParen(v___x_1698_, v_prec_1685_);
return v___x_1699_;
}
v___jp_1700_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1702_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__5));
lean_inc(v___y_1701_);
v___x_1703_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___y_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = 0;
v___x_1705_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*1, v___x_1704_);
v___x_1706_ = l_Repr_addAppParen(v___x_1705_, v_prec_1685_);
return v___x_1706_;
}
v___jp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1709_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__7));
lean_inc(v___y_1708_);
v___x_1710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___y_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = 0;
v___x_1712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*1, v___x_1711_);
v___x_1713_ = l_Repr_addAppParen(v___x_1712_, v_prec_1685_);
return v___x_1713_;
}
v___jp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1716_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__9));
lean_inc(v___y_1715_);
v___x_1717_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___y_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = 0;
v___x_1719_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*1, v___x_1718_);
v___x_1720_ = l_Repr_addAppParen(v___x_1719_, v_prec_1685_);
return v___x_1720_;
}
v___jp_1721_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1723_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__11));
lean_inc(v___y_1722_);
v___x_1724_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___y_1722_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = 0;
v___x_1726_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*1, v___x_1725_);
v___x_1727_ = l_Repr_addAppParen(v___x_1726_, v_prec_1685_);
return v___x_1727_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr___boxed(lean_object* v_x_1752_, lean_object* v_prec_1753_){
_start:
{
uint8_t v_x_341__boxed_1754_; lean_object* v_res_1755_; 
v_x_341__boxed_1754_ = lean_unbox(v_x_1752_);
v_res_1755_ = l_Lake_instReprComparatorOp_repr(v_x_341__boxed_1754_, v_prec_1753_);
lean_dec(v_prec_1753_);
return v_res_1755_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp_default(void){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = 0;
return v___x_1758_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp(void){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = 0;
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(lean_object* v_sym_1760_, uint8_t v_cmp_1761_, lean_object* v_t_1762_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_box(v_cmp_1761_);
lean_inc_ref(v_sym_1760_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v_sym_1760_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = l_Lean_Data_Trie_insert___redArg(v_t_1762_, v_sym_1760_, v___x_1764_);
lean_dec_ref(v_sym_1760_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0___boxed(lean_object* v_sym_1766_, lean_object* v_cmp_1767_, lean_object* v_t_1768_){
_start:
{
uint8_t v_cmp_boxed_1769_; lean_object* v_res_1770_; 
v_cmp_boxed_1769_ = lean_unbox(v_cmp_1767_);
v_res_1770_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v_sym_1766_, v_cmp_boxed_1769_, v_t_1768_);
return v_res_1770_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9(void){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_1780_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10(void){
_start:
{
lean_object* v___x_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1781_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9);
v___x_1782_ = 0;
v___x_1783_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
v___x_1784_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1783_, v___x_1782_, v___x_1781_);
return v___x_1784_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11(void){
_start:
{
lean_object* v___x_1785_; uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1785_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10);
v___x_1786_ = 1;
v___x_1787_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7));
v___x_1788_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1787_, v___x_1786_, v___x_1785_);
return v___x_1788_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12(void){
_start:
{
lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1789_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11);
v___x_1790_ = 1;
v___x_1791_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
v___x_1792_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1791_, v___x_1790_, v___x_1789_);
return v___x_1792_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13(void){
_start:
{
lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1793_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12);
v___x_1794_ = 2;
v___x_1795_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
v___x_1796_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1795_, v___x_1794_, v___x_1793_);
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14(void){
_start:
{
lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1797_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13);
v___x_1798_ = 3;
v___x_1799_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4));
v___x_1800_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1799_, v___x_1798_, v___x_1797_);
return v___x_1800_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15(void){
_start:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1801_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14);
v___x_1802_ = 3;
v___x_1803_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
v___x_1804_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1803_, v___x_1802_, v___x_1801_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16(void){
_start:
{
lean_object* v___x_1805_; uint8_t v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15);
v___x_1806_ = 4;
v___x_1807_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
v___x_1808_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1807_, v___x_1806_, v___x_1805_);
return v___x_1808_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17(void){
_start:
{
lean_object* v___x_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1809_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16);
v___x_1810_ = 5;
v___x_1811_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1));
v___x_1812_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1811_, v___x_1810_, v___x_1809_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18(void){
_start:
{
lean_object* v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1813_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17);
v___x_1814_ = 5;
v___x_1815_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
v___x_1816_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1815_, v___x_1814_, v___x_1813_);
return v___x_1816_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie(void){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(lean_object* v_s_1820_, lean_object* v_p_1821_){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie;
v___x_1823_ = lean_string_utf8_byte_size(v_s_1820_);
lean_inc(v_p_1821_);
v___x_1824_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_1820_, v___x_1822_, v_p_1821_, v___x_1823_);
if (lean_obj_tag(v___x_1824_) == 1)
{
lean_object* v_val_1825_; lean_object* v_fst_1826_; lean_object* v_snd_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1841_; 
v_val_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_val_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v_fst_1826_ = lean_ctor_get(v_val_1825_, 0);
v_snd_1827_ = lean_ctor_get(v_val_1825_, 1);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_val_1825_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1829_ = v_val_1825_;
v_isShared_1830_ = v_isSharedCheck_1841_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snd_1827_);
lean_inc(v_fst_1826_);
lean_dec(v_val_1825_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1841_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v_p_x27_1832_; uint8_t v___x_1833_; 
v___x_1831_ = lean_string_utf8_byte_size(v_fst_1826_);
lean_dec(v_fst_1826_);
v_p_x27_1832_ = lean_nat_add(v_p_1821_, v___x_1831_);
v___x_1833_ = lean_string_is_valid_pos(v_s_1820_, v_p_x27_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_dec(v_p_x27_1832_);
lean_dec(v_snd_1827_);
v___x_1834_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0));
if (v_isShared_1830_ == 0)
{
lean_ctor_set_tag(v___x_1829_, 1);
lean_ctor_set(v___x_1829_, 1, v_p_1821_);
lean_ctor_set(v___x_1829_, 0, v___x_1834_);
v___x_1836_ = v___x_1829_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_p_1821_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
else
{
lean_object* v___x_1839_; 
lean_dec(v_p_1821_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v_p_x27_1832_);
lean_ctor_set(v___x_1829_, 0, v_snd_1827_);
v___x_1839_ = v___x_1829_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_snd_1827_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_p_x27_1832_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_dec(v___x_1824_);
v___x_1842_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1));
v___x_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v_p_1821_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___boxed(lean_object* v_s_1844_, lean_object* v_p_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1844_, v_p_1845_);
lean_dec_ref(v_s_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f(lean_object* v_s_1847_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1847_, v___x_1848_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v_a_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
v_a_1851_ = lean_ctor_get(v___x_1849_, 1);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1849_, 2);
v___x_1852_ = lean_string_utf8_byte_size(v_s_1847_);
v___x_1853_ = lean_nat_dec_eq(v_a_1851_, v___x_1852_);
lean_dec(v_a_1851_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
lean_dec(v_a_1850_);
v___x_1854_ = lean_box(0);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v_a_1850_);
return v___x_1855_;
}
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref_known(v___x_1849_, 2);
v___x_1856_ = lean_box(0);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f___boxed(lean_object* v_s_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lake_ComparatorOp_ofString_x3f(v_s_1857_);
lean_dec_ref(v_s_1857_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString(uint8_t v_self_1859_){
_start:
{
switch(v_self_1859_)
{
case 0:
{
lean_object* v___x_1860_; 
v___x_1860_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
return v___x_1860_;
}
case 1:
{
lean_object* v___x_1861_; 
v___x_1861_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
return v___x_1861_;
}
case 2:
{
lean_object* v___x_1862_; 
v___x_1862_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
return v___x_1862_;
}
case 3:
{
lean_object* v___x_1863_; 
v___x_1863_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
return v___x_1863_;
}
case 4:
{
lean_object* v___x_1864_; 
v___x_1864_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
return v___x_1864_;
}
default: 
{
lean_object* v___x_1865_; 
v___x_1865_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
return v___x_1865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString___boxed(lean_object* v_self_1866_){
_start:
{
uint8_t v_self_boxed_1867_; lean_object* v_res_1868_; 
v_self_boxed_1867_ = lean_unbox(v_self_1866_);
v_res_1868_ = l_Lake_ComparatorOp_toString(v_self_boxed_1867_);
return v_res_1868_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_unsigned_to_nat(7u);
v___x_1881_ = lean_nat_to_int(v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_unsigned_to_nat(6u);
v___x_1886_ = lean_nat_to_int(v___x_1885_);
return v___x_1886_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_unsigned_to_nat(19u);
v___x_1891_ = lean_nat_to_int(v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___redArg(lean_object* v_x_1892_){
_start:
{
lean_object* v_ver_1893_; uint8_t v_op_1894_; uint8_t v_includeSuffixes_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_ver_1893_ = lean_ctor_get(v_x_1892_, 0);
lean_inc_ref(v_ver_1893_);
v_op_1894_ = lean_ctor_get_uint8(v_x_1892_, sizeof(void*)*1);
v_includeSuffixes_1895_ = lean_ctor_get_uint8(v_x_1892_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_1892_);
v___x_1896_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_1897_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__3));
v___x_1898_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__4, &l_Lake_instReprVerComparator_repr___redArg___closed__4_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__4);
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = l_Lake_instReprStdVer_repr___redArg(v_ver_1893_);
v___x_1901_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1898_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = 0;
v___x_1903_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set_uint8(v___x_1903_, sizeof(void*)*1, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1897_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_1906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_box(1);
v___x_1908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__6));
v___x_1910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1896_);
v___x_1912_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__7, &l_Lake_instReprVerComparator_repr___redArg___closed__7_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__7);
v___x_1913_ = l_Lake_instReprComparatorOp_repr(v_op_1894_, v___x_1899_);
v___x_1914_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*1, v___x_1902_);
v___x_1916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1911_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v___x_1905_);
v___x_1918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v___x_1907_);
v___x_1919_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__9));
v___x_1920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set(v___x_1921_, 1, v___x_1896_);
v___x_1922_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__10, &l_Lake_instReprVerComparator_repr___redArg___closed__10_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__10);
v___x_1923_ = l_Bool_repr___redArg(v_includeSuffixes_1895_);
v___x_1924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set_uint8(v___x_1925_, sizeof(void*)*1, v___x_1902_);
v___x_1926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1921_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_1928_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_1929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v___x_1926_);
v___x_1930_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_1931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1927_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*1, v___x_1902_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr(lean_object* v_x_1934_, lean_object* v_prec_1935_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lake_instReprVerComparator_repr___redArg(v_x_1934_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___boxed(lean_object* v_x_1937_, lean_object* v_prec_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lake_instReprVerComparator_repr(v_x_1937_, v_prec_1938_);
lean_dec(v_prec_1938_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(lean_object* v_s_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1951_, v_a_1952_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_a_1955_; lean_object* v___x_1956_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
v_a_1955_ = lean_ctor_get(v___x_1953_, 1);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1953_, 2);
lean_inc_ref(v_s_1951_);
v___x_1956_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_1951_, v_a_1955_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v_a_1958_; lean_object* v___x_1959_; lean_object* v_a_1960_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
v_a_1958_ = lean_ctor_get(v___x_1956_, 1);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1956_, 2);
v___x_1959_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_1951_, v_a_1958_);
lean_dec_ref(v_s_1951_);
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
if (lean_obj_tag(v_a_1960_) == 1)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1982_; 
v_a_1961_ = lean_ctor_get(v___x_1959_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1983_);
v___x_1963_ = v___x_1959_;
v_isShared_1964_ = v_isSharedCheck_1982_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1959_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1982_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_val_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_val_1965_ = lean_ctor_get(v_a_1960_, 0);
lean_inc(v_val_1965_);
lean_dec_ref_known(v_a_1960_, 1);
v___x_1966_ = lean_string_utf8_byte_size(v_val_1965_);
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = lean_nat_dec_eq(v___x_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; lean_object* v___x_1973_; 
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v_a_1957_);
lean_ctor_set(v___x_1969_, 1, v_val_1965_);
v___x_1970_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
v___x_1971_ = lean_unbox(v_a_1954_);
lean_dec(v_a_1954_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*1, v___x_1971_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*1 + 1, v___x_1968_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1970_);
v___x_1973_ = v___x_1963_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_a_1961_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1980_; 
lean_dec(v_val_1965_);
v___x_1975_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_a_1957_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
v___x_1978_ = lean_unbox(v_a_1954_);
lean_dec(v_a_1954_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*1, v___x_1978_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*1 + 1, v___x_1968_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1977_);
v___x_1980_ = v___x_1963_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_a_1961_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_a_1960_);
v_a_1984_ = lean_ctor_get(v___x_1959_, 1);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1997_);
v___x_1986_ = v___x_1959_;
v_isShared_1987_ = v_isSharedCheck_1996_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1959_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1996_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1994_; 
v___x_1988_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1957_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = 0;
v___x_1991_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
v___x_1992_ = lean_unbox(v_a_1954_);
lean_dec(v_a_1954_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*1, v___x_1992_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*1 + 1, v___x_1990_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1991_);
v___x_1994_ = v___x_1986_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_a_1984_);
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
lean_object* v_a_1998_; lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v_a_1954_);
lean_dec_ref(v_s_1951_);
v_a_1998_ = lean_ctor_get(v___x_1956_, 0);
v_a_1999_ = lean_ctor_get(v___x_1956_, 1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1956_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_inc(v_a_1998_);
lean_dec(v___x_1956_);
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
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1998_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_a_1999_);
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
lean_object* v_a_2007_; lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v_s_1951_);
v_a_2007_ = lean_ctor_get(v___x_1953_, 0);
v_a_2008_ = lean_ctor_get(v___x_1953_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1953_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_inc(v_a_2007_);
lean_dec(v___x_1953_);
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
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_parse(lean_object* v_s_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2018_ = ((lean_object*)(l_Lake_VerComparator_parse___closed__0));
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = lean_string_utf8_byte_size(v_s_2017_);
v___x_2021_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_2017_, v___x_2018_, v___x_2019_, v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT uint8_t l_Lake_VerComparator_test(lean_object* v_self_2022_, lean_object* v_ver_2023_){
_start:
{
uint8_t v___y_2025_; uint8_t v___y_2026_; uint8_t v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; uint8_t v___y_2030_; uint8_t v___y_2031_; uint8_t v___y_2036_; uint8_t v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; uint8_t v___y_2040_; uint8_t v___y_2041_; uint8_t v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; uint8_t v___y_2049_; uint8_t v___y_2050_; lean_object* v___y_2055_; lean_object* v___y_2056_; uint8_t v___y_2057_; uint8_t v___y_2058_; lean_object* v_ver_2062_; uint8_t v_op_2063_; uint8_t v_includeSuffixes_2064_; lean_object* v_ver_2066_; 
v_ver_2062_ = lean_ctor_get(v_self_2022_, 0);
v_op_2063_ = lean_ctor_get_uint8(v_self_2022_, sizeof(void*)*1);
v_includeSuffixes_2064_ = lean_ctor_get_uint8(v_self_2022_, sizeof(void*)*1 + 1);
if (v_includeSuffixes_2064_ == 0)
{
lean_object* v_toSemVerCore_2070_; lean_object* v_specialDescr_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_toSemVerCore_2070_ = lean_ctor_get(v_ver_2023_, 0);
v_specialDescr_2071_ = lean_ctor_get(v_ver_2023_, 1);
v___x_2072_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_2073_ = lean_string_dec_eq(v_specialDescr_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v_toSemVerCore_2074_; lean_object* v_specialDescr_2075_; uint8_t v___x_2076_; 
v_toSemVerCore_2074_ = lean_ctor_get(v_ver_2062_, 0);
v_specialDescr_2075_ = lean_ctor_get(v_ver_2062_, 1);
v___x_2076_ = lean_string_dec_eq(v_specialDescr_2075_, v___x_2072_);
if (v___x_2076_ == 0)
{
uint8_t v___x_2077_; 
v___x_2077_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_2074_, v_toSemVerCore_2070_);
if (v___x_2077_ == 0)
{
return v_includeSuffixes_2064_;
}
else
{
switch(v_op_2063_)
{
case 0:
{
uint8_t v___x_2078_; 
v___x_2078_ = lean_string_dec_lt(v_specialDescr_2071_, v_specialDescr_2075_);
return v___x_2078_;
}
case 1:
{
uint8_t v___x_2079_; 
v___x_2079_ = l_String_decLE(v_specialDescr_2071_, v_specialDescr_2075_);
return v___x_2079_;
}
case 2:
{
uint8_t v___x_2080_; 
v___x_2080_ = lean_string_dec_lt(v_specialDescr_2075_, v_specialDescr_2071_);
return v___x_2080_;
}
case 3:
{
uint8_t v___x_2081_; 
v___x_2081_ = l_String_decLE(v_specialDescr_2075_, v_specialDescr_2071_);
return v___x_2081_;
}
case 4:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_string_dec_eq(v_specialDescr_2071_, v_specialDescr_2075_);
return v___x_2082_;
}
default: 
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_string_dec_eq(v_specialDescr_2071_, v_specialDescr_2075_);
if (v___x_2083_ == 0)
{
return v___x_2077_;
}
else
{
return v___x_2076_;
}
}
}
}
}
else
{
return v_includeSuffixes_2064_;
}
}
else
{
v_ver_2066_ = v_ver_2023_;
goto v___jp_2065_;
}
}
else
{
v_ver_2066_ = v_ver_2023_;
goto v___jp_2065_;
}
v___jp_2024_:
{
uint8_t v___x_2032_; 
v___x_2032_ = l_Lake_instDecidableEqStdVer_decEq(v___y_2028_, v___y_2029_);
switch(v___y_2030_)
{
case 0:
{
return v___y_2026_;
}
case 1:
{
return v___y_2027_;
}
case 2:
{
return v___y_2025_;
}
case 3:
{
return v___y_2031_;
}
case 4:
{
return v___x_2032_;
}
default: 
{
if (v___x_2032_ == 0)
{
uint8_t v___x_2033_; 
v___x_2033_ = 1;
return v___x_2033_;
}
else
{
uint8_t v___x_2034_; 
v___x_2034_ = 0;
return v___x_2034_;
}
}
}
}
v___jp_2035_:
{
uint8_t v___x_2042_; 
v___x_2042_ = l_Lake_StdVer_compare(v___y_2039_, v___y_2038_);
if (v___x_2042_ == 2)
{
uint8_t v___x_2043_; 
v___x_2043_ = 0;
v___y_2025_ = v___y_2041_;
v___y_2026_ = v___y_2036_;
v___y_2027_ = v___y_2037_;
v___y_2028_ = v___y_2038_;
v___y_2029_ = v___y_2039_;
v___y_2030_ = v___y_2040_;
v___y_2031_ = v___x_2043_;
goto v___jp_2024_;
}
else
{
uint8_t v___x_2044_; 
v___x_2044_ = 1;
v___y_2025_ = v___y_2041_;
v___y_2026_ = v___y_2036_;
v___y_2027_ = v___y_2037_;
v___y_2028_ = v___y_2038_;
v___y_2029_ = v___y_2039_;
v___y_2030_ = v___y_2040_;
v___y_2031_ = v___x_2044_;
goto v___jp_2024_;
}
}
v___jp_2045_:
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Lake_StdVer_compare(v___y_2048_, v___y_2047_);
if (v___x_2051_ == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = 1;
v___y_2036_ = v___y_2046_;
v___y_2037_ = v___y_2050_;
v___y_2038_ = v___y_2047_;
v___y_2039_ = v___y_2048_;
v___y_2040_ = v___y_2049_;
v___y_2041_ = v___x_2052_;
goto v___jp_2035_;
}
else
{
uint8_t v___x_2053_; 
v___x_2053_ = 0;
v___y_2036_ = v___y_2046_;
v___y_2037_ = v___y_2050_;
v___y_2038_ = v___y_2047_;
v___y_2039_ = v___y_2048_;
v___y_2040_ = v___y_2049_;
v___y_2041_ = v___x_2053_;
goto v___jp_2035_;
}
}
v___jp_2054_:
{
uint8_t v___x_2059_; 
v___x_2059_ = l_Lake_StdVer_compare(v___y_2055_, v___y_2056_);
if (v___x_2059_ == 2)
{
uint8_t v___x_2060_; 
v___x_2060_ = 0;
v___y_2046_ = v___y_2058_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___y_2056_;
v___y_2049_ = v___y_2057_;
v___y_2050_ = v___x_2060_;
goto v___jp_2045_;
}
else
{
uint8_t v___x_2061_; 
v___x_2061_ = 1;
v___y_2046_ = v___y_2058_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___y_2056_;
v___y_2049_ = v___y_2057_;
v___y_2050_ = v___x_2061_;
goto v___jp_2045_;
}
}
v___jp_2065_:
{
uint8_t v___x_2067_; 
v___x_2067_ = l_Lake_StdVer_compare(v_ver_2066_, v_ver_2062_);
if (v___x_2067_ == 0)
{
uint8_t v___x_2068_; 
v___x_2068_ = 1;
v___y_2055_ = v_ver_2066_;
v___y_2056_ = v_ver_2062_;
v___y_2057_ = v_op_2063_;
v___y_2058_ = v___x_2068_;
goto v___jp_2054_;
}
else
{
uint8_t v___x_2069_; 
v___x_2069_ = 0;
v___y_2055_ = v_ver_2066_;
v___y_2056_ = v_ver_2062_;
v___y_2057_ = v_op_2063_;
v___y_2058_ = v___x_2069_;
goto v___jp_2054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_test___boxed(lean_object* v_self_2084_, lean_object* v_ver_2085_){
_start:
{
uint8_t v_res_2086_; lean_object* v_r_2087_; 
v_res_2086_ = l_Lake_VerComparator_test(v_self_2084_, v_ver_2085_);
lean_dec_ref(v_ver_2085_);
lean_dec_ref(v_self_2084_);
v_r_2087_ = lean_box(v_res_2086_);
return v_r_2087_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_toString(lean_object* v_self_2088_){
_start:
{
lean_object* v_ver_2089_; uint8_t v_op_2090_; uint8_t v_includeSuffixes_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_ver_2089_ = lean_ctor_get(v_self_2088_, 0);
lean_inc_ref(v_ver_2089_);
v_op_2090_ = lean_ctor_get_uint8(v_self_2088_, sizeof(void*)*1);
v_includeSuffixes_2091_ = lean_ctor_get_uint8(v_self_2088_, sizeof(void*)*1 + 1);
lean_dec_ref(v_self_2088_);
v___x_2092_ = l_Lake_ComparatorOp_toString(v_op_2090_);
v___x_2093_ = l_Lake_StdVer_toString(v_ver_2089_);
v___x_2094_ = lean_string_append(v___x_2092_, v___x_2093_);
lean_dec_ref(v___x_2093_);
if (v_includeSuffixes_2091_ == 0)
{
return v___x_2094_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_2096_ = lean_string_append(v___x_2094_, v___x_2095_);
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_2099_, lean_object* v_x_2100_, lean_object* v_x_2101_){
_start:
{
if (lean_obj_tag(v_x_2101_) == 0)
{
lean_dec(v_x_2099_);
return v_x_2100_;
}
else
{
lean_object* v_head_2102_; lean_object* v_tail_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2113_; 
v_head_2102_ = lean_ctor_get(v_x_2101_, 0);
v_tail_2103_ = lean_ctor_get(v_x_2101_, 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_x_2101_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2105_ = v_x_2101_;
v_isShared_2106_ = v_isSharedCheck_2113_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_tail_2103_);
lean_inc(v_head_2102_);
lean_dec(v_x_2101_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2113_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
lean_inc(v_x_2099_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 5);
lean_ctor_set(v___x_2105_, 1, v_x_2099_);
lean_ctor_set(v___x_2105_, 0, v_x_2100_);
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_x_2100_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_x_2099_);
v___x_2108_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2102_);
v___x_2110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v_x_2100_ = v___x_2110_;
v_x_2101_ = v_tail_2103_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2114_, lean_object* v_x_2115_, lean_object* v_x_2116_){
_start:
{
if (lean_obj_tag(v_x_2116_) == 0)
{
lean_dec(v_x_2114_);
return v_x_2115_;
}
else
{
lean_object* v_head_2117_; lean_object* v_tail_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2128_; 
v_head_2117_ = lean_ctor_get(v_x_2116_, 0);
v_tail_2118_ = lean_ctor_get(v_x_2116_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_x_2116_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2120_ = v_x_2116_;
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_tail_2118_);
lean_inc(v_head_2117_);
lean_dec(v_x_2116_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
lean_inc(v_x_2114_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set_tag(v___x_2120_, 5);
lean_ctor_set(v___x_2120_, 1, v_x_2114_);
lean_ctor_set(v___x_2120_, 0, v_x_2115_);
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_x_2115_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_x_2114_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2117_);
v___x_2125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_2114_, v___x_2125_, v_tail_2118_);
return v___x_2126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(lean_object* v_x_2129_, lean_object* v_x_2130_){
_start:
{
if (lean_obj_tag(v_x_2129_) == 0)
{
lean_object* v___x_2131_; 
lean_dec(v_x_2130_);
v___x_2131_ = lean_box(0);
return v___x_2131_;
}
else
{
lean_object* v_tail_2132_; 
v_tail_2132_ = lean_ctor_get(v_x_2129_, 1);
if (lean_obj_tag(v_tail_2132_) == 0)
{
lean_object* v_head_2133_; lean_object* v___x_2134_; 
lean_dec(v_x_2130_);
v_head_2133_ = lean_ctor_get(v_x_2129_, 0);
lean_inc(v_head_2133_);
lean_dec_ref_known(v_x_2129_, 2);
v___x_2134_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2133_);
return v___x_2134_;
}
else
{
lean_object* v_head_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_inc(v_tail_2132_);
v_head_2135_ = lean_ctor_get(v_x_2129_, 0);
lean_inc(v_head_2135_);
lean_dec_ref_known(v_x_2129_, 2);
v___x_2136_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2135_);
v___x_2137_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(v_x_2130_, v___x_2136_, v_tail_2132_);
return v___x_2137_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0));
v___x_2144_ = lean_string_length(v___x_2143_);
return v___x_2144_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3);
v___x_2146_ = lean_nat_to_int(v___x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(lean_object* v_xs_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2155_ = lean_array_get_size(v_xs_2154_);
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = lean_nat_dec_eq(v___x_2155_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2158_ = lean_array_to_list(v_xs_2154_);
v___x_2159_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2160_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(v___x_2158_, v___x_2159_);
v___x_2161_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2162_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v___x_2160_);
v___x_2164_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2161_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = l_Std_Format_fill(v___x_2166_);
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; 
lean_dec_ref(v_xs_2154_);
v___x_2168_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2168_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(lean_object* v_x_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_){
_start:
{
if (lean_obj_tag(v_x_2171_) == 0)
{
lean_dec(v_x_2169_);
return v_x_2170_;
}
else
{
lean_object* v_head_2172_; lean_object* v_tail_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2183_; 
v_head_2172_ = lean_ctor_get(v_x_2171_, 0);
v_tail_2173_ = lean_ctor_get(v_x_2171_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_x_2171_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2175_ = v_x_2171_;
v_isShared_2176_ = v_isSharedCheck_2183_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_tail_2173_);
lean_inc(v_head_2172_);
lean_dec(v_x_2171_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2183_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
lean_inc(v_x_2169_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set_tag(v___x_2175_, 5);
lean_ctor_set(v___x_2175_, 1, v_x_2169_);
lean_ctor_set(v___x_2175_, 0, v_x_2170_);
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_x_2170_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_x_2169_);
v___x_2178_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2172_);
v___x_2180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v_x_2170_ = v___x_2180_;
v_x_2171_ = v_tail_2173_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(lean_object* v_x_2184_, lean_object* v_x_2185_){
_start:
{
if (lean_obj_tag(v_x_2184_) == 0)
{
lean_object* v___x_2186_; 
lean_dec(v_x_2185_);
v___x_2186_ = lean_box(0);
return v___x_2186_;
}
else
{
lean_object* v_tail_2187_; 
v_tail_2187_ = lean_ctor_get(v_x_2184_, 1);
if (lean_obj_tag(v_tail_2187_) == 0)
{
lean_object* v_head_2188_; lean_object* v___x_2189_; 
lean_dec(v_x_2185_);
v_head_2188_ = lean_ctor_get(v_x_2184_, 0);
lean_inc(v_head_2188_);
lean_dec_ref_known(v_x_2184_, 2);
v___x_2189_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2188_);
return v___x_2189_;
}
else
{
lean_object* v_head_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_inc(v_tail_2187_);
v_head_2190_ = lean_ctor_get(v_x_2184_, 0);
lean_inc(v_head_2190_);
lean_dec_ref_known(v_x_2184_, 2);
v___x_2191_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2190_);
v___x_2192_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(v_x_2185_, v___x_2191_, v_tail_2187_);
return v___x_2192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(lean_object* v_xs_2193_){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2194_ = lean_array_get_size(v_xs_2193_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = lean_nat_dec_eq(v___x_2194_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2197_ = lean_array_to_list(v_xs_2193_);
v___x_2198_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2199_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(v___x_2197_, v___x_2198_);
v___x_2200_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2201_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___x_2199_);
v___x_2203_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2200_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = l_Std_Format_fill(v___x_2205_);
return v___x_2206_;
}
else
{
lean_object* v___x_2207_; 
lean_dec_ref(v_xs_2193_);
v___x_2207_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2207_;
}
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = lean_unsigned_to_nat(12u);
v___x_2218_ = lean_nat_to_int(v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_unsigned_to_nat(11u);
v___x_2223_ = lean_nat_to_int(v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object* v_x_2224_){
_start:
{
lean_object* v_toString_2225_; lean_object* v_clauses_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2260_; 
v_toString_2225_ = lean_ctor_get(v_x_2224_, 0);
v_clauses_2226_ = lean_ctor_get(v_x_2224_, 1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_x_2224_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2228_ = v_x_2224_;
v_isShared_2229_ = v_isSharedCheck_2260_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_clauses_2226_);
lean_inc(v_toString_2225_);
lean_dec(v_x_2224_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2260_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2230_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_2231_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__3));
v___x_2232_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__4, &l_Lake_instReprVerRange_repr___redArg___closed__4_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__4);
v___x_2233_ = l_String_quote(v_toString_2225_);
v___x_2234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set_tag(v___x_2228_, 4);
lean_ctor_set(v___x_2228_, 1, v___x_2234_);
lean_ctor_set(v___x_2228_, 0, v___x_2232_);
v___x_2236_ = v___x_2228_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2237_ = 0;
v___x_2238_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2238_, 0, v___x_2236_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*1, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2231_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_2241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = lean_box(1);
v___x_2243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__6));
v___x_2245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
lean_ctor_set(v___x_2246_, 1, v___x_2230_);
v___x_2247_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__7, &l_Lake_instReprVerRange_repr___redArg___closed__7_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__7);
v___x_2248_ = l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(v_clauses_2226_);
v___x_2249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set_uint8(v___x_2250_, sizeof(void*)*1, v___x_2237_);
v___x_2251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2246_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_2253_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_2254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v___x_2251_);
v___x_2255_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_2256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2252_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set_uint8(v___x_2258_, sizeof(void*)*1, v___x_2237_);
return v___x_2258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr(lean_object* v_x_2261_, lean_object* v_prec_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lake_instReprVerRange_repr___redArg(v_x_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___boxed(lean_object* v_x_2264_, lean_object* v_prec_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lake_instReprVerRange_repr(v_x_2264_, v_prec_2265_);
lean_dec(v_prec_2265_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0(lean_object* v_self_2276_){
_start:
{
lean_object* v_toString_2277_; 
v_toString_2277_ = lean_ctor_get(v_self_2276_, 0);
lean_inc_ref(v_toString_2277_);
return v_toString_2277_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0___boxed(lean_object* v_self_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lake_VerRange_instToString___lam__0(v_self_2278_);
lean_dec_ref(v_self_2278_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(lean_object* v_as_2283_, size_t v_i_2284_, size_t v_stop_2285_, lean_object* v_b_2286_){
_start:
{
uint8_t v___x_2287_; 
v___x_2287_ = lean_usize_dec_eq(v_i_2284_, v_stop_2285_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; size_t v___x_2293_; size_t v___x_2294_; 
v___x_2288_ = lean_array_uget_borrowed(v_as_2283_, v_i_2284_);
v___x_2289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0));
v___x_2290_ = lean_string_append(v_b_2286_, v___x_2289_);
lean_inc(v___x_2288_);
v___x_2291_ = l_Lake_VerComparator_toString(v___x_2288_);
v___x_2292_ = lean_string_append(v___x_2290_, v___x_2291_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = ((size_t)1ULL);
v___x_2294_ = lean_usize_add(v_i_2284_, v___x_2293_);
v_i_2284_ = v___x_2294_;
v_b_2286_ = v___x_2292_;
goto _start;
}
else
{
return v_b_2286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___boxed(lean_object* v_as_2296_, lean_object* v_i_2297_, lean_object* v_stop_2298_, lean_object* v_b_2299_){
_start:
{
size_t v_i_boxed_2300_; size_t v_stop_boxed_2301_; lean_object* v_res_2302_; 
v_i_boxed_2300_ = lean_unbox_usize(v_i_2297_);
lean_dec(v_i_2297_);
v_stop_boxed_2301_ = lean_unbox_usize(v_stop_2298_);
lean_dec(v_stop_2298_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_as_2296_, v_i_boxed_2300_, v_stop_boxed_2301_, v_b_2299_);
lean_dec_ref(v_as_2296_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(lean_object* v_ands_2304_){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___x_2305_ = lean_array_get_size(v_ands_2304_);
v___x_2306_ = lean_unsigned_to_nat(0u);
v___x_2307_ = lean_nat_dec_eq(v___x_2305_, v___x_2306_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2308_ = lean_array_fget_borrowed(v_ands_2304_, v___x_2306_);
lean_inc(v___x_2308_);
v___x_2309_ = l_Lake_VerComparator_toString(v___x_2308_);
v___x_2310_ = lean_unsigned_to_nat(1u);
v___x_2311_ = lean_nat_dec_lt(v___x_2310_, v___x_2305_);
if (v___x_2311_ == 0)
{
return v___x_2309_;
}
else
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_nat_dec_le(v___x_2305_, v___x_2305_);
if (v___x_2312_ == 0)
{
if (v___x_2311_ == 0)
{
return v___x_2309_;
}
else
{
size_t v___x_2313_; size_t v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = ((size_t)1ULL);
v___x_2314_ = lean_usize_of_nat(v___x_2305_);
v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2304_, v___x_2313_, v___x_2314_, v___x_2309_);
return v___x_2315_;
}
}
else
{
size_t v___x_2316_; size_t v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = ((size_t)1ULL);
v___x_2317_ = lean_usize_of_nat(v___x_2305_);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2304_, v___x_2316_, v___x_2317_, v___x_2309_);
return v___x_2318_;
}
}
}
else
{
lean_object* v___x_2319_; 
v___x_2319_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0));
return v___x_2319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___boxed(lean_object* v_ands_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v_ands_2320_);
lean_dec_ref(v_ands_2320_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(lean_object* v_as_2323_, size_t v_i_2324_, size_t v_stop_2325_, lean_object* v_b_2326_){
_start:
{
uint8_t v___x_2327_; 
v___x_2327_ = lean_usize_dec_eq(v_i_2324_, v_stop_2325_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; size_t v___x_2333_; size_t v___x_2334_; 
v___x_2328_ = lean_array_uget_borrowed(v_as_2323_, v_i_2324_);
v___x_2329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0));
v___x_2330_ = lean_string_append(v_b_2326_, v___x_2329_);
v___x_2331_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2328_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___boxed(lean_object* v_as_2336_, lean_object* v_i_2337_, lean_object* v_stop_2338_, lean_object* v_b_2339_){
_start:
{
size_t v_i_boxed_2340_; size_t v_stop_boxed_2341_; lean_object* v_res_2342_; 
v_i_boxed_2340_ = lean_unbox_usize(v_i_2337_);
lean_dec(v_i_2337_);
v_stop_boxed_2341_ = lean_unbox_usize(v_stop_2338_);
lean_dec(v_stop_2338_);
v_res_2342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_as_2336_, v_i_boxed_2340_, v_stop_boxed_2341_, v_b_2339_);
lean_dec_ref(v_as_2336_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(lean_object* v_ors_2343_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2344_ = lean_array_get_size(v_ors_2343_);
v___x_2345_ = lean_unsigned_to_nat(0u);
v___x_2346_ = lean_nat_dec_eq(v___x_2344_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; 
v___x_2347_ = lean_array_fget_borrowed(v_ors_2343_, v___x_2345_);
v___x_2348_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2347_);
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_dec_lt(v___x_2349_, v___x_2344_);
if (v___x_2350_ == 0)
{
return v___x_2348_;
}
else
{
uint8_t v___x_2351_; 
v___x_2351_ = lean_nat_dec_le(v___x_2344_, v___x_2344_);
if (v___x_2351_ == 0)
{
if (v___x_2350_ == 0)
{
return v___x_2348_;
}
else
{
size_t v___x_2352_; size_t v___x_2353_; lean_object* v___x_2354_; 
v___x_2352_ = ((size_t)1ULL);
v___x_2353_ = lean_usize_of_nat(v___x_2344_);
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2343_, v___x_2352_, v___x_2353_, v___x_2348_);
return v___x_2354_;
}
}
else
{
size_t v___x_2355_; size_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = lean_usize_of_nat(v___x_2344_);
v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2343_, v___x_2355_, v___x_2356_, v___x_2348_);
return v___x_2357_;
}
}
}
else
{
lean_object* v___x_2358_; 
v___x_2358_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
return v___x_2358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs___boxed(lean_object* v_ors_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_ors_2359_);
lean_dec_ref(v_ors_2359_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_ofClauses(lean_object* v_clauses_2361_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_clauses_2361_);
v___x_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v_clauses_2361_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_appendRange(lean_object* v_ands_2364_, lean_object* v_minVer_2365_, lean_object* v_maxVer_2366_, lean_object* v_specialDescr_2367_){
_start:
{
lean_object* v_minVer_2368_; lean_object* v___x_2369_; lean_object* v_maxVer_2370_; uint8_t v___x_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_minVer_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2368_, 0, v_minVer_2365_);
lean_ctor_set(v_minVer_2368_, 1, v_specialDescr_2367_);
v___x_2369_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2370_, 0, v_maxVer_2366_);
lean_ctor_set(v_maxVer_2370_, 1, v___x_2369_);
v___x_2371_ = 3;
v___x_2372_ = 0;
v___x_2373_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2373_, 0, v_minVer_2368_);
lean_ctor_set_uint8(v___x_2373_, sizeof(void*)*1, v___x_2371_);
lean_ctor_set_uint8(v___x_2373_, sizeof(void*)*1 + 1, v___x_2372_);
v___x_2374_ = lean_array_push(v_ands_2364_, v___x_2373_);
v___x_2375_ = 0;
v___x_2376_ = 1;
v___x_2377_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2377_, 0, v_maxVer_2370_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*1, v___x_2375_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*1 + 1, v___x_2376_);
v___x_2378_ = lean_array_push(v___x_2374_, v___x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(lean_object* v_s_2381_, lean_object* v_ands_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v_a_2387_; lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2559_; 
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2385_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2383_);
lean_inc_ref(v_s_2381_);
v___x_2386_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2381_, v___x_2385_, v_a_2383_, v_a_2383_);
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_a_2388_ = lean_ctor_get(v___x_2386_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2390_ = v___x_2386_;
v_isShared_2391_ = v_isSharedCheck_2559_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2559_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; 
v___x_2392_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2381_, v_a_2388_);
lean_dec_ref(v_s_2381_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2549_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_a_2394_ = lean_ctor_get(v___x_2392_, 1);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2396_ = v___x_2392_;
v_isShared_2397_ = v_isSharedCheck_2549_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2549_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2398_ = lean_array_get_size(v_a_2387_);
v___x_2399_ = lean_unsigned_to_nat(1u);
v___x_2400_ = lean_nat_dec_eq(v___x_2398_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = lean_unsigned_to_nat(2u);
v___x_2402_ = lean_nat_dec_eq(v___x_2398_, v___x_2401_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = lean_unsigned_to_nat(3u);
v___x_2404_ = lean_nat_dec_eq(v___x_2398_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_a_2387_);
lean_dec_ref(v_ands_2382_);
v___x_2405_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0));
v___x_2406_ = l_Nat_reprFast(v___x_2398_);
v___x_2407_ = lean_string_append(v___x_2405_, v___x_2406_);
lean_dec_ref(v___x_2406_);
v___x_2408_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2409_ = lean_string_append(v___x_2407_, v___x_2408_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2409_);
v___x_2411_ = v___x_2396_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_a_2394_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_array_fget_borrowed(v_a_2387_, v___x_2384_);
v___x_2414_ = l_String_Slice_toNat_x3f(v___x_2413_);
if (lean_obj_tag(v___x_2414_) == 1)
{
lean_object* v_val_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v_val_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_val_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v___x_2416_ = lean_array_fget_borrowed(v_a_2387_, v___x_2399_);
v___x_2417_ = l_String_Slice_toNat_x3f(v___x_2416_);
if (lean_obj_tag(v___x_2417_) == 1)
{
lean_object* v_val_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_val_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_val_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2419_ = lean_array_fget(v_a_2387_, v___x_2401_);
lean_dec(v_a_2387_);
v___x_2420_ = l_String_Slice_toNat_x3f(v___x_2419_);
if (lean_obj_tag(v___x_2420_) == 1)
{
lean_object* v_val_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_minVer_2426_; 
lean_dec(v___x_2419_);
v_val_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_val_2421_);
lean_dec_ref_known(v___x_2420_, 1);
lean_inc(v_val_2418_);
lean_inc(v_val_2415_);
v___x_2422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2422_, 0, v_val_2415_);
lean_ctor_set(v___x_2422_, 1, v_val_2418_);
lean_ctor_set(v___x_2422_, 2, v_val_2421_);
v___x_2423_ = lean_nat_add(v_val_2418_, v___x_2399_);
lean_dec(v_val_2418_);
v___x_2424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2424_, 0, v_val_2415_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
lean_ctor_set(v___x_2424_, 2, v___x_2384_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v_a_2393_);
lean_ctor_set(v___x_2390_, 0, v___x_2422_);
v_minVer_2426_ = v___x_2390_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_a_2393_);
v_minVer_2426_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v_maxVer_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2427_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2428_, 0, v___x_2424_);
lean_ctor_set(v_maxVer_2428_, 1, v___x_2427_);
v___x_2429_ = 3;
v___x_2430_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2430_, 0, v_minVer_2426_);
lean_ctor_set_uint8(v___x_2430_, sizeof(void*)*1, v___x_2429_);
lean_ctor_set_uint8(v___x_2430_, sizeof(void*)*1 + 1, v___x_2402_);
v___x_2431_ = lean_array_push(v_ands_2382_, v___x_2430_);
v___x_2432_ = 0;
v___x_2433_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2433_, 0, v_maxVer_2428_);
lean_ctor_set_uint8(v___x_2433_, sizeof(void*)*1, v___x_2432_);
lean_ctor_set_uint8(v___x_2433_, sizeof(void*)*1 + 1, v___x_2404_);
v___x_2434_ = lean_array_push(v___x_2431_, v___x_2433_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2434_);
v___x_2436_ = v___x_2396_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_a_2394_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
else
{
lean_object* v_str_2439_; lean_object* v_startInclusive_2440_; lean_object* v_endExclusive_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
lean_dec(v___x_2420_);
lean_dec(v_val_2418_);
lean_dec(v_val_2415_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec_ref(v_ands_2382_);
v_str_2439_ = lean_ctor_get(v___x_2419_, 0);
lean_inc_ref(v_str_2439_);
v_startInclusive_2440_ = lean_ctor_get(v___x_2419_, 1);
lean_inc(v_startInclusive_2440_);
v_endExclusive_2441_ = lean_ctor_get(v___x_2419_, 2);
lean_inc(v_endExclusive_2441_);
lean_dec(v___x_2419_);
v___x_2442_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2443_ = lean_string_utf8_extract(v_str_2439_, v_startInclusive_2440_, v_endExclusive_2441_);
lean_dec(v_endExclusive_2441_);
lean_dec(v_startInclusive_2440_);
lean_dec_ref(v_str_2439_);
v___x_2444_ = lean_string_append(v___x_2442_, v___x_2443_);
lean_dec_ref(v___x_2443_);
v___x_2445_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2446_ = lean_string_append(v___x_2444_, v___x_2445_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2446_);
v___x_2448_ = v___x_2396_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_a_2394_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_str_2450_; lean_object* v_startInclusive_2451_; lean_object* v_endExclusive_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2459_; 
lean_inc(v___x_2416_);
lean_dec(v___x_2417_);
lean_dec(v_val_2415_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_a_2387_);
lean_dec_ref(v_ands_2382_);
v_str_2450_ = lean_ctor_get(v___x_2416_, 0);
lean_inc_ref(v_str_2450_);
v_startInclusive_2451_ = lean_ctor_get(v___x_2416_, 1);
lean_inc(v_startInclusive_2451_);
v_endExclusive_2452_ = lean_ctor_get(v___x_2416_, 2);
lean_inc(v_endExclusive_2452_);
lean_dec(v___x_2416_);
v___x_2453_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2454_ = lean_string_utf8_extract(v_str_2450_, v_startInclusive_2451_, v_endExclusive_2452_);
lean_dec(v_endExclusive_2452_);
lean_dec(v_startInclusive_2451_);
lean_dec_ref(v_str_2450_);
v___x_2455_ = lean_string_append(v___x_2453_, v___x_2454_);
lean_dec_ref(v___x_2454_);
v___x_2456_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2457_ = lean_string_append(v___x_2455_, v___x_2456_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2457_);
v___x_2459_ = v___x_2396_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_a_2394_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
else
{
lean_object* v_str_2461_; lean_object* v_startInclusive_2462_; lean_object* v_endExclusive_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
lean_inc(v___x_2413_);
lean_dec(v___x_2414_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_a_2387_);
lean_dec_ref(v_ands_2382_);
v_str_2461_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_str_2461_);
v_startInclusive_2462_ = lean_ctor_get(v___x_2413_, 1);
lean_inc(v_startInclusive_2462_);
v_endExclusive_2463_ = lean_ctor_get(v___x_2413_, 2);
lean_inc(v_endExclusive_2463_);
lean_dec(v___x_2413_);
v___x_2464_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2465_ = lean_string_utf8_extract(v_str_2461_, v_startInclusive_2462_, v_endExclusive_2463_);
lean_dec(v_endExclusive_2463_);
lean_dec(v_startInclusive_2462_);
lean_dec_ref(v_str_2461_);
v___x_2466_ = lean_string_append(v___x_2464_, v___x_2465_);
lean_dec_ref(v___x_2465_);
v___x_2467_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2468_ = lean_string_append(v___x_2466_, v___x_2467_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2468_);
v___x_2470_ = v___x_2396_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_a_2394_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = lean_array_fget_borrowed(v_a_2387_, v___x_2384_);
v___x_2473_ = l_String_Slice_toNat_x3f(v___x_2472_);
if (lean_obj_tag(v___x_2473_) == 1)
{
lean_object* v_val_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_val_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_val_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = lean_array_fget(v_a_2387_, v___x_2399_);
lean_dec(v_a_2387_);
v___x_2476_ = l_String_Slice_toNat_x3f(v___x_2475_);
if (lean_obj_tag(v___x_2476_) == 1)
{
lean_object* v_val_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v_minVer_2482_; 
lean_dec(v___x_2475_);
v_val_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_n(v_val_2477_, 2);
lean_dec_ref_known(v___x_2476_, 1);
lean_inc(v_val_2474_);
v___x_2478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2478_, 0, v_val_2474_);
lean_ctor_set(v___x_2478_, 1, v_val_2477_);
lean_ctor_set(v___x_2478_, 2, v___x_2384_);
v___x_2479_ = lean_nat_add(v_val_2477_, v___x_2399_);
lean_dec(v_val_2477_);
v___x_2480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2480_, 0, v_val_2474_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
lean_ctor_set(v___x_2480_, 2, v___x_2384_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v_a_2393_);
lean_ctor_set(v___x_2390_, 0, v___x_2478_);
v_minVer_2482_ = v___x_2390_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_a_2393_);
v_minVer_2482_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2483_; lean_object* v_maxVer_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2483_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2484_, 0, v___x_2480_);
lean_ctor_set(v_maxVer_2484_, 1, v___x_2483_);
v___x_2485_ = 3;
v___x_2486_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2486_, 0, v_minVer_2482_);
lean_ctor_set_uint8(v___x_2486_, sizeof(void*)*1, v___x_2485_);
lean_ctor_set_uint8(v___x_2486_, sizeof(void*)*1 + 1, v___x_2400_);
v___x_2487_ = lean_array_push(v_ands_2382_, v___x_2486_);
v___x_2488_ = 0;
v___x_2489_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2489_, 0, v_maxVer_2484_);
lean_ctor_set_uint8(v___x_2489_, sizeof(void*)*1, v___x_2488_);
lean_ctor_set_uint8(v___x_2489_, sizeof(void*)*1 + 1, v___x_2402_);
v___x_2490_ = lean_array_push(v___x_2487_, v___x_2489_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2490_);
v___x_2492_ = v___x_2396_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_a_2394_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
else
{
lean_object* v_str_2495_; lean_object* v_startInclusive_2496_; lean_object* v_endExclusive_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
lean_dec(v___x_2476_);
lean_dec(v_val_2474_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec_ref(v_ands_2382_);
v_str_2495_ = lean_ctor_get(v___x_2475_, 0);
lean_inc_ref(v_str_2495_);
v_startInclusive_2496_ = lean_ctor_get(v___x_2475_, 1);
lean_inc(v_startInclusive_2496_);
v_endExclusive_2497_ = lean_ctor_get(v___x_2475_, 2);
lean_inc(v_endExclusive_2497_);
lean_dec(v___x_2475_);
v___x_2498_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2499_ = lean_string_utf8_extract(v_str_2495_, v_startInclusive_2496_, v_endExclusive_2497_);
lean_dec(v_endExclusive_2497_);
lean_dec(v_startInclusive_2496_);
lean_dec_ref(v_str_2495_);
v___x_2500_ = lean_string_append(v___x_2498_, v___x_2499_);
lean_dec_ref(v___x_2499_);
v___x_2501_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2502_ = lean_string_append(v___x_2500_, v___x_2501_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2502_);
v___x_2504_ = v___x_2396_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_a_2394_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
else
{
lean_object* v_str_2506_; lean_object* v_startInclusive_2507_; lean_object* v_endExclusive_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
lean_inc(v___x_2472_);
lean_dec(v___x_2473_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_a_2387_);
lean_dec_ref(v_ands_2382_);
v_str_2506_ = lean_ctor_get(v___x_2472_, 0);
lean_inc_ref(v_str_2506_);
v_startInclusive_2507_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_startInclusive_2507_);
v_endExclusive_2508_ = lean_ctor_get(v___x_2472_, 2);
lean_inc(v_endExclusive_2508_);
lean_dec(v___x_2472_);
v___x_2509_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2510_ = lean_string_utf8_extract(v_str_2506_, v_startInclusive_2507_, v_endExclusive_2508_);
lean_dec(v_endExclusive_2508_);
lean_dec(v_startInclusive_2507_);
lean_dec_ref(v_str_2506_);
v___x_2511_ = lean_string_append(v___x_2509_, v___x_2510_);
lean_dec_ref(v___x_2510_);
v___x_2512_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2513_ = lean_string_append(v___x_2511_, v___x_2512_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2513_);
v___x_2515_ = v___x_2396_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_a_2394_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_array_fget(v_a_2387_, v___x_2384_);
lean_dec(v_a_2387_);
v___x_2518_ = l_String_Slice_toNat_x3f(v___x_2517_);
if (lean_obj_tag(v___x_2518_) == 1)
{
lean_object* v_val_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v_minVer_2524_; 
lean_dec(v___x_2517_);
v_val_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc_n(v_val_2519_, 2);
lean_dec_ref_known(v___x_2518_, 1);
v___x_2520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2520_, 0, v_val_2519_);
lean_ctor_set(v___x_2520_, 1, v___x_2384_);
lean_ctor_set(v___x_2520_, 2, v___x_2384_);
v___x_2521_ = lean_nat_add(v_val_2519_, v___x_2399_);
lean_dec(v_val_2519_);
v___x_2522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___x_2384_);
lean_ctor_set(v___x_2522_, 2, v___x_2384_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v_a_2393_);
lean_ctor_set(v___x_2390_, 0, v___x_2520_);
v_minVer_2524_ = v___x_2390_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_a_2393_);
v_minVer_2524_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; lean_object* v_maxVer_2526_; uint8_t v___x_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2525_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2526_, 0, v___x_2522_);
lean_ctor_set(v_maxVer_2526_, 1, v___x_2525_);
v___x_2527_ = 3;
v___x_2528_ = 0;
v___x_2529_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2529_, 0, v_minVer_2524_);
lean_ctor_set_uint8(v___x_2529_, sizeof(void*)*1, v___x_2527_);
lean_ctor_set_uint8(v___x_2529_, sizeof(void*)*1 + 1, v___x_2528_);
v___x_2530_ = lean_array_push(v_ands_2382_, v___x_2529_);
v___x_2531_ = 0;
v___x_2532_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2532_, 0, v_maxVer_2526_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*1, v___x_2531_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*1 + 1, v___x_2400_);
v___x_2533_ = lean_array_push(v___x_2530_, v___x_2532_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2533_);
v___x_2535_ = v___x_2396_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_a_2394_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_object* v_str_2538_; lean_object* v_startInclusive_2539_; lean_object* v_endExclusive_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
lean_dec(v___x_2518_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec_ref(v_ands_2382_);
v_str_2538_ = lean_ctor_get(v___x_2517_, 0);
lean_inc_ref(v_str_2538_);
v_startInclusive_2539_ = lean_ctor_get(v___x_2517_, 1);
lean_inc(v_startInclusive_2539_);
v_endExclusive_2540_ = lean_ctor_get(v___x_2517_, 2);
lean_inc(v_endExclusive_2540_);
lean_dec(v___x_2517_);
v___x_2541_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2542_ = lean_string_utf8_extract(v_str_2538_, v_startInclusive_2539_, v_endExclusive_2540_);
lean_dec(v_endExclusive_2540_);
lean_dec(v_startInclusive_2539_);
lean_dec_ref(v_str_2538_);
v___x_2543_ = lean_string_append(v___x_2541_, v___x_2542_);
lean_dec_ref(v___x_2542_);
v___x_2544_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2545_);
v___x_2547_ = v___x_2396_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_a_2394_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_del_object(v___x_2390_);
lean_dec(v_a_2387_);
lean_dec_ref(v_ands_2382_);
v_a_2550_ = lean_ctor_get(v___x_2392_, 0);
v_a_2551_ = lean_ctor_get(v___x_2392_, 1);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2392_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_inc(v_a_2550_);
lean_dec(v___x_2392_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2550_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(lean_object* v_s_2562_, lean_object* v_ands_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v_a_2568_; lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2791_; 
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2564_);
lean_inc_ref(v_s_2562_);
v___x_2567_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2562_, v___x_2566_, v_a_2564_, v_a_2564_);
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_a_2569_ = lean_ctor_get(v___x_2567_, 1);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2571_ = v___x_2567_;
v_isShared_2572_ = v_isSharedCheck_2791_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2791_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; 
v___x_2573_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2562_, v_a_2569_);
lean_dec_ref(v_s_2562_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2781_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_a_2575_ = lean_ctor_get(v___x_2573_, 1);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2577_ = v___x_2573_;
v_isShared_2578_ = v_isSharedCheck_2781_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2781_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2579_ = lean_array_get_size(v_a_2568_);
v___x_2580_ = lean_unsigned_to_nat(1u);
v___x_2581_ = lean_nat_dec_eq(v___x_2579_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = lean_unsigned_to_nat(2u);
v___x_2583_ = lean_nat_dec_eq(v___x_2579_, v___x_2582_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = lean_unsigned_to_nat(3u);
v___x_2585_ = lean_nat_dec_eq(v___x_2579_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2592_; 
lean_dec(v_a_2574_);
lean_del_object(v___x_2571_);
lean_dec(v_a_2568_);
lean_dec_ref(v_ands_2563_);
v___x_2586_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0));
v___x_2587_ = l_Nat_reprFast(v___x_2579_);
v___x_2588_ = lean_string_append(v___x_2586_, v___x_2587_);
lean_dec_ref(v___x_2587_);
v___x_2589_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2590_ = lean_string_append(v___x_2588_, v___x_2589_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2590_);
v___x_2592_ = v___x_2577_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_a_2575_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_array_fget_borrowed(v_a_2568_, v___x_2565_);
v___x_2595_ = l_String_Slice_toNat_x3f(v___x_2594_);
if (lean_obj_tag(v___x_2595_) == 1)
{
lean_object* v_val_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_val_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_val_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = lean_array_fget_borrowed(v_a_2568_, v___x_2580_);
v___x_2598_ = l_String_Slice_toNat_x3f(v___x_2597_);
if (lean_obj_tag(v___x_2598_) == 1)
{
lean_object* v_val_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_val_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_val_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v___x_2600_ = lean_array_fget(v_a_2568_, v___x_2582_);
lean_dec(v_a_2568_);
v___x_2601_ = l_String_Slice_toNat_x3f(v___x_2600_);
if (lean_obj_tag(v___x_2601_) == 1)
{
lean_object* v_val_2602_; uint8_t v___y_2604_; uint8_t v___x_2624_; 
lean_dec(v___x_2600_);
v_val_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_val_2602_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2624_ = lean_nat_dec_eq(v_val_2596_, v___x_2565_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v_minVer_2628_; lean_object* v___x_2629_; lean_object* v_maxVer_2630_; uint8_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
lean_del_object(v___x_2577_);
lean_inc(v_val_2596_);
v___x_2625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2625_, 0, v_val_2596_);
lean_ctor_set(v___x_2625_, 1, v_val_2599_);
lean_ctor_set(v___x_2625_, 2, v_val_2602_);
v___x_2626_ = lean_nat_add(v_val_2596_, v___x_2580_);
lean_dec(v_val_2596_);
v___x_2627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v___x_2565_);
lean_ctor_set(v___x_2627_, 2, v___x_2565_);
v_minVer_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2628_, 0, v___x_2625_);
lean_ctor_set(v_minVer_2628_, 1, v_a_2574_);
v___x_2629_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2630_, 0, v___x_2627_);
lean_ctor_set(v_maxVer_2630_, 1, v___x_2629_);
v___x_2631_ = 3;
v___x_2632_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2632_, 0, v_minVer_2628_);
lean_ctor_set_uint8(v___x_2632_, sizeof(void*)*1, v___x_2631_);
lean_ctor_set_uint8(v___x_2632_, sizeof(void*)*1 + 1, v___x_2624_);
v___x_2633_ = lean_array_push(v_ands_2563_, v___x_2632_);
v___x_2634_ = 0;
v___x_2635_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2635_, 0, v_maxVer_2630_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*1, v___x_2634_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*1 + 1, v___x_2585_);
v___x_2636_ = lean_array_push(v___x_2633_, v___x_2635_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v_a_2575_);
lean_ctor_set(v___x_2571_, 0, v___x_2636_);
v___x_2638_ = v___x_2571_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2639_, 1, v_a_2575_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
else
{
uint8_t v___x_2640_; 
v___x_2640_ = lean_nat_dec_eq(v_val_2599_, v___x_2565_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v_minVer_2644_; lean_object* v___x_2645_; lean_object* v_maxVer_2646_; uint8_t v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_del_object(v___x_2577_);
lean_inc(v_val_2599_);
lean_inc(v_val_2596_);
v___x_2641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2641_, 0, v_val_2596_);
lean_ctor_set(v___x_2641_, 1, v_val_2599_);
lean_ctor_set(v___x_2641_, 2, v_val_2602_);
v___x_2642_ = lean_nat_add(v_val_2599_, v___x_2580_);
lean_dec(v_val_2599_);
v___x_2643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2643_, 0, v_val_2596_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
lean_ctor_set(v___x_2643_, 2, v___x_2565_);
v_minVer_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2644_, 0, v___x_2641_);
lean_ctor_set(v_minVer_2644_, 1, v_a_2574_);
v___x_2645_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2646_, 0, v___x_2643_);
lean_ctor_set(v_maxVer_2646_, 1, v___x_2645_);
v___x_2647_ = 3;
v___x_2648_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2648_, 0, v_minVer_2644_);
lean_ctor_set_uint8(v___x_2648_, sizeof(void*)*1, v___x_2647_);
lean_ctor_set_uint8(v___x_2648_, sizeof(void*)*1 + 1, v___x_2640_);
v___x_2649_ = lean_array_push(v_ands_2563_, v___x_2648_);
v___x_2650_ = 0;
v___x_2651_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2651_, 0, v_maxVer_2646_);
lean_ctor_set_uint8(v___x_2651_, sizeof(void*)*1, v___x_2650_);
lean_ctor_set_uint8(v___x_2651_, sizeof(void*)*1 + 1, v___x_2624_);
v___x_2652_ = lean_array_push(v___x_2649_, v___x_2651_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v_a_2575_);
lean_ctor_set(v___x_2571_, 0, v___x_2652_);
v___x_2654_ = v___x_2571_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_a_2575_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
else
{
uint8_t v___x_2656_; 
lean_del_object(v___x_2571_);
v___x_2656_ = lean_nat_dec_eq(v_val_2602_, v___x_2565_);
if (v___x_2656_ == 0)
{
v___y_2604_ = v___x_2656_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = lean_string_utf8_byte_size(v_a_2574_);
v___x_2658_ = lean_nat_dec_eq(v___x_2657_, v___x_2565_);
v___y_2604_ = v___x_2658_;
goto v___jp_2603_;
}
}
}
v___jp_2603_:
{
if (v___y_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v_minVer_2608_; lean_object* v___x_2609_; lean_object* v_maxVer_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_inc(v_val_2602_);
lean_inc(v_val_2599_);
lean_inc(v_val_2596_);
v___x_2605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2605_, 0, v_val_2596_);
lean_ctor_set(v___x_2605_, 1, v_val_2599_);
lean_ctor_set(v___x_2605_, 2, v_val_2602_);
v___x_2606_ = lean_nat_add(v_val_2602_, v___x_2580_);
lean_dec(v_val_2602_);
v___x_2607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2607_, 0, v_val_2596_);
lean_ctor_set(v___x_2607_, 1, v_val_2599_);
lean_ctor_set(v___x_2607_, 2, v___x_2606_);
v_minVer_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2608_, 0, v___x_2605_);
lean_ctor_set(v_minVer_2608_, 1, v_a_2574_);
v___x_2609_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2610_, 0, v___x_2607_);
lean_ctor_set(v_maxVer_2610_, 1, v___x_2609_);
v___x_2611_ = 3;
v___x_2612_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2612_, 0, v_minVer_2608_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*1, v___x_2611_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*1 + 1, v___y_2604_);
v___x_2613_ = lean_array_push(v_ands_2563_, v___x_2612_);
v___x_2614_ = 0;
v___x_2615_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2615_, 0, v_maxVer_2610_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*1, v___x_2614_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*1 + 1, v___x_2585_);
v___x_2616_ = lean_array_push(v___x_2613_, v___x_2615_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2616_);
v___x_2618_ = v___x_2577_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_a_2575_);
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
lean_object* v___x_2620_; lean_object* v___x_2622_; 
lean_dec(v_val_2602_);
lean_dec(v_val_2599_);
lean_dec(v_val_2596_);
lean_dec(v_a_2574_);
lean_dec_ref(v_ands_2563_);
v___x_2620_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1));
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2620_);
v___x_2622_ = v___x_2577_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_a_2575_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v_str_2659_; lean_object* v_startInclusive_2660_; lean_object* v_endExclusive_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
lean_dec(v___x_2601_);
lean_dec(v_val_2599_);
lean_dec(v_val_2596_);
lean_dec(v_a_2574_);
lean_del_object(v___x_2571_);
lean_dec_ref(v_ands_2563_);
v_str_2659_ = lean_ctor_get(v___x_2600_, 0);
lean_inc_ref(v_str_2659_);
v_startInclusive_2660_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_startInclusive_2660_);
v_endExclusive_2661_ = lean_ctor_get(v___x_2600_, 2);
lean_inc(v_endExclusive_2661_);
lean_dec(v___x_2600_);
v___x_2662_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2663_ = lean_string_utf8_extract(v_str_2659_, v_startInclusive_2660_, v_endExclusive_2661_);
lean_dec(v_endExclusive_2661_);
lean_dec(v_startInclusive_2660_);
lean_dec_ref(v_str_2659_);
v___x_2664_ = lean_string_append(v___x_2662_, v___x_2663_);
lean_dec_ref(v___x_2663_);
v___x_2665_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2666_ = lean_string_append(v___x_2664_, v___x_2665_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2666_);
v___x_2668_ = v___x_2577_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_a_2575_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
else
{
lean_object* v_str_2670_; lean_object* v_startInclusive_2671_; lean_object* v_endExclusive_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
lean_inc(v___x_2597_);
lean_dec(v___x_2598_);
lean_dec(v_val_2596_);
lean_dec(v_a_2574_);
lean_del_object(v___x_2571_);
lean_dec(v_a_2568_);
lean_dec_ref(v_ands_2563_);
v_str_2670_ = lean_ctor_get(v___x_2597_, 0);
lean_inc_ref(v_str_2670_);
v_startInclusive_2671_ = lean_ctor_get(v___x_2597_, 1);
lean_inc(v_startInclusive_2671_);
v_endExclusive_2672_ = lean_ctor_get(v___x_2597_, 2);
lean_inc(v_endExclusive_2672_);
lean_dec(v___x_2597_);
v___x_2673_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2674_ = lean_string_utf8_extract(v_str_2670_, v_startInclusive_2671_, v_endExclusive_2672_);
lean_dec(v_endExclusive_2672_);
lean_dec(v_startInclusive_2671_);
lean_dec_ref(v_str_2670_);
v___x_2675_ = lean_string_append(v___x_2673_, v___x_2674_);
lean_dec_ref(v___x_2674_);
v___x_2676_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2677_ = lean_string_append(v___x_2675_, v___x_2676_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2677_);
v___x_2679_ = v___x_2577_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_a_2575_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
else
{
lean_object* v_str_2681_; lean_object* v_startInclusive_2682_; lean_object* v_endExclusive_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_inc(v___x_2594_);
lean_dec(v___x_2595_);
lean_dec(v_a_2574_);
lean_del_object(v___x_2571_);
lean_dec(v_a_2568_);
lean_dec_ref(v_ands_2563_);
v_str_2681_ = lean_ctor_get(v___x_2594_, 0);
lean_inc_ref(v_str_2681_);
v_startInclusive_2682_ = lean_ctor_get(v___x_2594_, 1);
lean_inc(v_startInclusive_2682_);
v_endExclusive_2683_ = lean_ctor_get(v___x_2594_, 2);
lean_inc(v_endExclusive_2683_);
lean_dec(v___x_2594_);
v___x_2684_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2685_ = lean_string_utf8_extract(v_str_2681_, v_startInclusive_2682_, v_endExclusive_2683_);
lean_dec(v_endExclusive_2683_);
lean_dec(v_startInclusive_2682_);
lean_dec_ref(v_str_2681_);
v___x_2686_ = lean_string_append(v___x_2684_, v___x_2685_);
lean_dec_ref(v___x_2685_);
v___x_2687_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2688_ = lean_string_append(v___x_2686_, v___x_2687_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2688_);
v___x_2690_ = v___x_2577_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_a_2575_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_del_object(v___x_2571_);
v___x_2692_ = lean_array_fget_borrowed(v_a_2568_, v___x_2565_);
v___x_2693_ = l_String_Slice_toNat_x3f(v___x_2692_);
if (lean_obj_tag(v___x_2693_) == 1)
{
lean_object* v_val_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_val_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_val_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v___x_2695_ = lean_array_fget(v_a_2568_, v___x_2580_);
lean_dec(v_a_2568_);
v___x_2696_ = l_String_Slice_toNat_x3f(v___x_2695_);
if (lean_obj_tag(v___x_2696_) == 1)
{
lean_object* v_val_2697_; uint8_t v___x_2698_; 
lean_dec(v___x_2695_);
v_val_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v___x_2696_, 1);
v___x_2698_ = lean_nat_dec_eq(v_val_2694_, v___x_2565_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v_minVer_2702_; lean_object* v___x_2703_; lean_object* v_maxVer_2704_; uint8_t v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
lean_inc(v_val_2694_);
v___x_2699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2699_, 0, v_val_2694_);
lean_ctor_set(v___x_2699_, 1, v_val_2697_);
lean_ctor_set(v___x_2699_, 2, v___x_2565_);
v___x_2700_ = lean_nat_add(v_val_2694_, v___x_2580_);
lean_dec(v_val_2694_);
v___x_2701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v___x_2565_);
lean_ctor_set(v___x_2701_, 2, v___x_2565_);
v_minVer_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2702_, 0, v___x_2699_);
lean_ctor_set(v_minVer_2702_, 1, v_a_2574_);
v___x_2703_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2704_, 0, v___x_2701_);
lean_ctor_set(v_maxVer_2704_, 1, v___x_2703_);
v___x_2705_ = 3;
v___x_2706_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2706_, 0, v_minVer_2702_);
lean_ctor_set_uint8(v___x_2706_, sizeof(void*)*1, v___x_2705_);
lean_ctor_set_uint8(v___x_2706_, sizeof(void*)*1 + 1, v___x_2698_);
v___x_2707_ = lean_array_push(v_ands_2563_, v___x_2706_);
v___x_2708_ = 0;
v___x_2709_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2709_, 0, v_maxVer_2704_);
lean_ctor_set_uint8(v___x_2709_, sizeof(void*)*1, v___x_2708_);
lean_ctor_set_uint8(v___x_2709_, sizeof(void*)*1 + 1, v___x_2583_);
v___x_2710_ = lean_array_push(v___x_2707_, v___x_2709_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2710_);
v___x_2712_ = v___x_2577_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_a_2575_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v_minVer_2717_; lean_object* v___x_2718_; lean_object* v_maxVer_2719_; uint8_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_inc(v_val_2697_);
lean_inc(v_val_2694_);
v___x_2714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2714_, 0, v_val_2694_);
lean_ctor_set(v___x_2714_, 1, v_val_2697_);
lean_ctor_set(v___x_2714_, 2, v___x_2565_);
v___x_2715_ = lean_nat_add(v_val_2697_, v___x_2580_);
lean_dec(v_val_2697_);
v___x_2716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2716_, 0, v_val_2694_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
lean_ctor_set(v___x_2716_, 2, v___x_2565_);
v_minVer_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2717_, 0, v___x_2714_);
lean_ctor_set(v_minVer_2717_, 1, v_a_2574_);
v___x_2718_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2719_, 0, v___x_2716_);
lean_ctor_set(v_maxVer_2719_, 1, v___x_2718_);
v___x_2720_ = 3;
v___x_2721_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2721_, 0, v_minVer_2717_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*1, v___x_2720_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*1 + 1, v___x_2581_);
v___x_2722_ = lean_array_push(v_ands_2563_, v___x_2721_);
v___x_2723_ = 0;
v___x_2724_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2724_, 0, v_maxVer_2719_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*1, v___x_2723_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*1 + 1, v___x_2698_);
v___x_2725_ = lean_array_push(v___x_2722_, v___x_2724_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2725_);
v___x_2727_ = v___x_2577_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_a_2575_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
else
{
lean_object* v_str_2729_; lean_object* v_startInclusive_2730_; lean_object* v_endExclusive_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_dec(v___x_2696_);
lean_dec(v_val_2694_);
lean_dec(v_a_2574_);
lean_dec_ref(v_ands_2563_);
v_str_2729_ = lean_ctor_get(v___x_2695_, 0);
lean_inc_ref(v_str_2729_);
v_startInclusive_2730_ = lean_ctor_get(v___x_2695_, 1);
lean_inc(v_startInclusive_2730_);
v_endExclusive_2731_ = lean_ctor_get(v___x_2695_, 2);
lean_inc(v_endExclusive_2731_);
lean_dec(v___x_2695_);
v___x_2732_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2733_ = lean_string_utf8_extract(v_str_2729_, v_startInclusive_2730_, v_endExclusive_2731_);
lean_dec(v_endExclusive_2731_);
lean_dec(v_startInclusive_2730_);
lean_dec_ref(v_str_2729_);
v___x_2734_ = lean_string_append(v___x_2732_, v___x_2733_);
lean_dec_ref(v___x_2733_);
v___x_2735_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2736_ = lean_string_append(v___x_2734_, v___x_2735_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2736_);
v___x_2738_ = v___x_2577_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_a_2575_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v_str_2740_; lean_object* v_startInclusive_2741_; lean_object* v_endExclusive_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2749_; 
lean_inc(v___x_2692_);
lean_dec(v___x_2693_);
lean_dec(v_a_2574_);
lean_dec(v_a_2568_);
lean_dec_ref(v_ands_2563_);
v_str_2740_ = lean_ctor_get(v___x_2692_, 0);
lean_inc_ref(v_str_2740_);
v_startInclusive_2741_ = lean_ctor_get(v___x_2692_, 1);
lean_inc(v_startInclusive_2741_);
v_endExclusive_2742_ = lean_ctor_get(v___x_2692_, 2);
lean_inc(v_endExclusive_2742_);
lean_dec(v___x_2692_);
v___x_2743_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2744_ = lean_string_utf8_extract(v_str_2740_, v_startInclusive_2741_, v_endExclusive_2742_);
lean_dec(v_endExclusive_2742_);
lean_dec(v_startInclusive_2741_);
lean_dec_ref(v_str_2740_);
v___x_2745_ = lean_string_append(v___x_2743_, v___x_2744_);
lean_dec_ref(v___x_2744_);
v___x_2746_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2747_ = lean_string_append(v___x_2745_, v___x_2746_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2747_);
v___x_2749_ = v___x_2577_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_a_2575_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_del_object(v___x_2571_);
v___x_2751_ = lean_array_fget(v_a_2568_, v___x_2565_);
lean_dec(v_a_2568_);
v___x_2752_ = l_String_Slice_toNat_x3f(v___x_2751_);
if (lean_obj_tag(v___x_2752_) == 1)
{
lean_object* v_val_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v_minVer_2757_; lean_object* v___x_2758_; lean_object* v_maxVer_2759_; uint8_t v___x_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_dec(v___x_2751_);
v_val_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc_n(v_val_2753_, 2);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2754_, 0, v_val_2753_);
lean_ctor_set(v___x_2754_, 1, v___x_2565_);
lean_ctor_set(v___x_2754_, 2, v___x_2565_);
v___x_2755_ = lean_nat_add(v_val_2753_, v___x_2580_);
lean_dec(v_val_2753_);
v___x_2756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v___x_2565_);
lean_ctor_set(v___x_2756_, 2, v___x_2565_);
v_minVer_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2757_, 0, v___x_2754_);
lean_ctor_set(v_minVer_2757_, 1, v_a_2574_);
v___x_2758_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2759_, 0, v___x_2756_);
lean_ctor_set(v_maxVer_2759_, 1, v___x_2758_);
v___x_2760_ = 3;
v___x_2761_ = 0;
v___x_2762_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2762_, 0, v_minVer_2757_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*1, v___x_2760_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*1 + 1, v___x_2761_);
v___x_2763_ = lean_array_push(v_ands_2563_, v___x_2762_);
v___x_2764_ = 0;
v___x_2765_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2765_, 0, v_maxVer_2759_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*1, v___x_2764_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*1 + 1, v___x_2581_);
v___x_2766_ = lean_array_push(v___x_2763_, v___x_2765_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2766_);
v___x_2768_ = v___x_2577_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v_a_2575_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
else
{
lean_object* v_str_2770_; lean_object* v_startInclusive_2771_; lean_object* v_endExclusive_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
lean_dec(v___x_2752_);
lean_dec(v_a_2574_);
lean_dec_ref(v_ands_2563_);
v_str_2770_ = lean_ctor_get(v___x_2751_, 0);
lean_inc_ref(v_str_2770_);
v_startInclusive_2771_ = lean_ctor_get(v___x_2751_, 1);
lean_inc(v_startInclusive_2771_);
v_endExclusive_2772_ = lean_ctor_get(v___x_2751_, 2);
lean_inc(v_endExclusive_2772_);
lean_dec(v___x_2751_);
v___x_2773_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2774_ = lean_string_utf8_extract(v_str_2770_, v_startInclusive_2771_, v_endExclusive_2772_);
lean_dec(v_endExclusive_2772_);
lean_dec(v_startInclusive_2771_);
lean_dec_ref(v_str_2770_);
v___x_2775_ = lean_string_append(v___x_2773_, v___x_2774_);
lean_dec_ref(v___x_2774_);
v___x_2776_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2777_ = lean_string_append(v___x_2775_, v___x_2776_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2777_);
v___x_2779_ = v___x_2577_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_a_2575_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_del_object(v___x_2571_);
lean_dec(v_a_2568_);
lean_dec_ref(v_ands_2563_);
v_a_2782_ = lean_ctor_get(v___x_2573_, 0);
v_a_2783_ = lean_ctor_get(v___x_2573_, 1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2573_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_inc(v_a_2782_);
lean_dec(v___x_2573_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2782_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(lean_object* v_s_2797_, lean_object* v_ands_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___y_2801_; lean_object* v___y_2805_; lean_object* v___y_2810_; lean_object* v___x_2813_; lean_object* v___y_2815_; uint8_t v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v_a_2903_; lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2988_; 
v___x_2813_ = lean_unsigned_to_nat(0u);
v___x_2901_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2799_);
lean_inc_ref(v_s_2797_);
v___x_2902_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2797_, v___x_2901_, v_a_2799_, v_a_2799_);
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_a_2904_ = lean_ctor_get(v___x_2902_, 1);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2906_ = v___x_2902_;
v_isShared_2907_ = v_isSharedCheck_2988_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2988_;
goto v_resetjp_2905_;
}
v___jp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0));
v___x_2803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set(v___x_2803_, 1, v___y_2801_);
return v___x_2803_;
}
v___jp_2804_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2806_ = ((lean_object*)(l_Lake_VerComparator_wild));
v___x_2807_ = lean_array_push(v_ands_2798_, v___x_2806_);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
lean_ctor_set(v___x_2808_, 1, v___y_2805_);
return v___x_2808_;
}
v___jp_2809_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1));
v___x_2812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v___y_2810_);
return v___x_2812_;
}
v___jp_2814_:
{
lean_object* v___x_2822_; 
v___x_2822_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2819_, v___y_2821_, v___y_2818_);
lean_dec(v___y_2821_);
if (lean_obj_tag(v___x_2822_) == 0)
{
switch(lean_obj_tag(v___y_2820_))
{
case 2:
{
switch(lean_obj_tag(v___y_2815_))
{
case 2:
{
lean_object* v_a_2823_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
if (lean_obj_tag(v_a_2823_) == 1)
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2846_; 
v_a_2824_ = lean_ctor_get(v___x_2822_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v___x_2822_, 0);
lean_dec(v_unused_2847_);
v___x_2826_ = v___x_2822_;
v_isShared_2827_ = v_isSharedCheck_2846_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2822_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2846_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v_n_2828_; lean_object* v_n_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v_minVer_2834_; lean_object* v_maxVer_2835_; uint8_t v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; uint8_t v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2844_; 
v_n_2828_ = lean_ctor_get(v___y_2820_, 0);
lean_inc_n(v_n_2828_, 2);
lean_dec_ref_known(v___y_2820_, 1);
v_n_2829_ = lean_ctor_get(v___y_2815_, 0);
lean_inc_n(v_n_2829_, 2);
lean_dec_ref_known(v___y_2815_, 1);
v___x_2830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2830_, 0, v_n_2828_);
lean_ctor_set(v___x_2830_, 1, v_n_2829_);
lean_ctor_set(v___x_2830_, 2, v___x_2813_);
v___x_2831_ = lean_nat_add(v_n_2829_, v___y_2817_);
lean_dec(v_n_2829_);
v___x_2832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2832_, 0, v_n_2828_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
lean_ctor_set(v___x_2832_, 2, v___x_2813_);
v___x_2833_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2834_, 0, v___x_2830_);
lean_ctor_set(v_minVer_2834_, 1, v___x_2833_);
v_maxVer_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2835_, 0, v___x_2832_);
lean_ctor_set(v_maxVer_2835_, 1, v___x_2833_);
v___x_2836_ = 3;
v___x_2837_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2837_, 0, v_minVer_2834_);
lean_ctor_set_uint8(v___x_2837_, sizeof(void*)*1, v___x_2836_);
lean_ctor_set_uint8(v___x_2837_, sizeof(void*)*1 + 1, v___y_2816_);
v___x_2838_ = lean_array_push(v_ands_2798_, v___x_2837_);
v___x_2839_ = 0;
v___x_2840_ = 1;
v___x_2841_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2841_, 0, v_maxVer_2835_);
lean_ctor_set_uint8(v___x_2841_, sizeof(void*)*1, v___x_2839_);
lean_ctor_set_uint8(v___x_2841_, sizeof(void*)*1 + 1, v___x_2840_);
v___x_2842_ = lean_array_push(v___x_2838_, v___x_2841_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2842_);
v___x_2844_ = v___x_2826_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_a_2824_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
else
{
lean_object* v_a_2848_; 
lean_dec_ref_known(v___y_2815_, 1);
lean_dec(v_a_2823_);
lean_dec_ref_known(v___y_2820_, 1);
lean_dec_ref(v_ands_2798_);
v_a_2848_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2822_, 2);
v___y_2801_ = v_a_2848_;
goto v___jp_2800_;
}
}
case 1:
{
lean_object* v_a_2849_; 
v_a_2849_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2849_);
if (lean_obj_tag(v_a_2849_) == 2)
{
lean_object* v_a_2850_; 
lean_dec_ref_known(v_a_2849_, 1);
lean_dec_ref_known(v___y_2820_, 1);
lean_dec_ref(v_ands_2798_);
v_a_2850_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2822_, 2);
v___y_2810_ = v_a_2850_;
goto v___jp_2809_;
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_a_2849_);
v_a_2851_ = lean_ctor_get(v___x_2822_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v___x_2822_, 0);
lean_dec(v_unused_2873_);
v___x_2853_ = v___x_2822_;
v_isShared_2854_ = v_isSharedCheck_2872_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2822_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2872_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v_n_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v_minVer_2860_; lean_object* v_maxVer_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; uint8_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
v_n_2855_ = lean_ctor_get(v___y_2820_, 0);
lean_inc_n(v_n_2855_, 2);
lean_dec_ref_known(v___y_2820_, 1);
v___x_2856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2856_, 0, v_n_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2813_);
lean_ctor_set(v___x_2856_, 2, v___x_2813_);
v___x_2857_ = lean_nat_add(v_n_2855_, v___y_2817_);
lean_dec(v_n_2855_);
v___x_2858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
lean_ctor_set(v___x_2858_, 1, v___x_2813_);
lean_ctor_set(v___x_2858_, 2, v___x_2813_);
v___x_2859_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2860_, 0, v___x_2856_);
lean_ctor_set(v_minVer_2860_, 1, v___x_2859_);
v_maxVer_2861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2861_, 0, v___x_2858_);
lean_ctor_set(v_maxVer_2861_, 1, v___x_2859_);
v___x_2862_ = 3;
v___x_2863_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2863_, 0, v_minVer_2860_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*1, v___x_2862_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*1 + 1, v___y_2816_);
v___x_2864_ = lean_array_push(v_ands_2798_, v___x_2863_);
v___x_2865_ = 0;
v___x_2866_ = 1;
v___x_2867_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2867_, 0, v_maxVer_2861_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*1, v___x_2865_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*1 + 1, v___x_2866_);
v___x_2868_ = lean_array_push(v___x_2864_, v___x_2867_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2868_);
v___x_2870_ = v___x_2853_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_a_2851_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
default: 
{
lean_object* v_a_2874_; 
lean_dec_ref_known(v___y_2820_, 1);
lean_dec(v___y_2815_);
lean_dec_ref(v_ands_2798_);
v_a_2874_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2822_, 2);
v___y_2801_ = v_a_2874_;
goto v___jp_2800_;
}
}
}
case 1:
{
lean_object* v_a_2875_; 
v_a_2875_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2875_);
if (lean_obj_tag(v_a_2875_) == 2)
{
lean_object* v_a_2876_; 
lean_dec_ref_known(v_a_2875_, 1);
lean_dec(v___y_2815_);
lean_dec_ref(v_ands_2798_);
v_a_2876_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2822_, 2);
v___y_2810_ = v_a_2876_;
goto v___jp_2809_;
}
else
{
lean_dec(v_a_2875_);
if (lean_obj_tag(v___y_2815_) == 2)
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2885_; 
lean_dec_ref_known(v___y_2815_, 1);
lean_dec_ref(v_ands_2798_);
v_a_2877_ = lean_ctor_get(v___x_2822_, 1);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; 
v_unused_2886_ = lean_ctor_get(v___x_2822_, 0);
lean_dec(v_unused_2886_);
v___x_2879_ = v___x_2822_;
v_isShared_2880_ = v_isSharedCheck_2885_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2822_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2885_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2));
if (v_isShared_2880_ == 0)
{
lean_ctor_set_tag(v___x_2879_, 1);
lean_ctor_set(v___x_2879_, 0, v___x_2881_);
v___x_2883_ = v___x_2879_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_a_2877_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
else
{
lean_object* v_a_2887_; 
lean_dec(v___y_2815_);
v_a_2887_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2822_, 2);
v___y_2805_ = v_a_2887_;
goto v___jp_2804_;
}
}
}
default: 
{
lean_dec(v___y_2820_);
if (lean_obj_tag(v___y_2815_) == 1)
{
lean_object* v_a_2888_; 
v_a_2888_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2888_);
if (lean_obj_tag(v_a_2888_) == 2)
{
lean_object* v_a_2889_; 
lean_dec_ref_known(v_a_2888_, 1);
lean_dec_ref(v_ands_2798_);
v_a_2889_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2822_, 2);
v___y_2810_ = v_a_2889_;
goto v___jp_2809_;
}
else
{
lean_object* v_a_2890_; 
lean_dec(v_a_2888_);
v_a_2890_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2822_, 2);
v___y_2805_ = v_a_2890_;
goto v___jp_2804_;
}
}
else
{
lean_object* v_a_2891_; 
lean_dec(v___y_2815_);
v_a_2891_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2822_, 2);
v___y_2805_ = v_a_2891_;
goto v___jp_2804_;
}
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v___y_2820_);
lean_dec(v___y_2815_);
lean_dec_ref(v_ands_2798_);
v_a_2892_ = lean_ctor_get(v___x_2822_, 0);
v_a_2893_ = lean_ctor_get(v___x_2822_, 1);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2822_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_inc(v_a_2892_);
lean_dec(v___x_2822_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2892_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
v_resetjp_2905_:
{
lean_object* v___y_2909_; lean_object* v___y_2919_; lean_object* v___y_2920_; uint8_t v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2945_; lean_object* v___y_2946_; uint8_t v___y_2947_; lean_object* v___y_2948_; uint8_t v___y_2968_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2978_ = lean_string_utf8_byte_size(v_s_2797_);
v___x_2979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2979_, 0, v_s_2797_);
lean_ctor_set(v___x_2979_, 1, v___x_2813_);
lean_ctor_set(v___x_2979_, 2, v___x_2978_);
v___x_2980_ = l_String_Slice_Pos_get_x3f(v___x_2979_, v_a_2904_);
lean_dec_ref_known(v___x_2979_, 3);
if (lean_obj_tag(v___x_2980_) == 0)
{
uint8_t v___x_2981_; 
v___x_2981_ = 0;
v___y_2968_ = v___x_2981_;
goto v___jp_2967_;
}
else
{
lean_object* v_val_2982_; uint32_t v___x_2983_; uint32_t v___x_2984_; uint8_t v___x_2985_; 
v_val_2982_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_val_2982_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2983_ = 45;
v___x_2984_ = lean_unbox_uint32(v_val_2982_);
lean_dec(v_val_2982_);
v___x_2985_ = lean_uint32_dec_eq(v___x_2984_, v___x_2983_);
if (v___x_2985_ == 0)
{
v___y_2968_ = v___x_2985_;
goto v___jp_2967_;
}
else
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_del_object(v___x_2906_);
lean_dec(v_a_2903_);
lean_dec_ref(v_ands_2798_);
v___x_2986_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4));
v___x_2987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v_a_2904_);
return v___x_2987_;
}
}
v___jp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2910_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3));
v___x_2911_ = l_Nat_reprFast(v___y_2909_);
v___x_2912_ = lean_string_append(v___x_2910_, v___x_2911_);
lean_dec_ref(v___x_2911_);
v___x_2913_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2914_ = lean_string_append(v___x_2912_, v___x_2913_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set_tag(v___x_2906_, 1);
lean_ctor_set(v___x_2906_, 0, v___x_2914_);
v___x_2916_ = v___x_2906_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_a_2904_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
v___jp_2918_:
{
lean_object* v___x_2926_; 
v___x_2926_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2922_, v___y_2925_, v___y_2919_);
lean_dec(v___y_2925_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v_a_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
v_a_2928_ = lean_ctor_get(v___x_2926_, 1);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2926_, 2);
v___x_2929_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__12));
v___x_2930_ = lean_unsigned_to_nat(2u);
v___x_2931_ = lean_nat_dec_lt(v___x_2930_, v___y_2920_);
lean_dec(v___y_2920_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; 
lean_dec(v_a_2903_);
v___x_2932_ = lean_box(0);
v___y_2815_ = v_a_2927_;
v___y_2816_ = v___y_2921_;
v___y_2817_ = v___y_2923_;
v___y_2818_ = v_a_2928_;
v___y_2819_ = v___x_2929_;
v___y_2820_ = v___y_2924_;
v___y_2821_ = v___x_2932_;
goto v___jp_2814_;
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_array_fget(v_a_2903_, v___x_2930_);
lean_dec(v_a_2903_);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
v___y_2815_ = v_a_2927_;
v___y_2816_ = v___y_2921_;
v___y_2817_ = v___y_2923_;
v___y_2818_ = v_a_2928_;
v___y_2819_ = v___x_2929_;
v___y_2820_ = v___y_2924_;
v___y_2821_ = v___x_2934_;
goto v___jp_2814_;
}
}
else
{
lean_object* v_a_2935_; lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v___y_2924_);
lean_dec(v___y_2920_);
lean_dec(v_a_2903_);
lean_dec_ref(v_ands_2798_);
v_a_2935_ = lean_ctor_get(v___x_2926_, 0);
v_a_2936_ = lean_ctor_get(v___x_2926_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2926_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_inc(v_a_2935_);
lean_dec(v___x_2926_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2935_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_a_2936_);
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
v___jp_2944_:
{
lean_object* v___x_2949_; 
v___x_2949_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2945_, v___y_2948_, v_a_2904_);
lean_dec(v___y_2948_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v_a_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
v_a_2951_ = lean_ctor_get(v___x_2949_, 1);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2949_, 2);
v___x_2952_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__10));
v___x_2953_ = lean_unsigned_to_nat(1u);
v___x_2954_ = lean_nat_dec_lt(v___x_2953_, v___y_2946_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_box(0);
v___y_2919_ = v_a_2951_;
v___y_2920_ = v___y_2946_;
v___y_2921_ = v___y_2947_;
v___y_2922_ = v___x_2952_;
v___y_2923_ = v___x_2953_;
v___y_2924_ = v_a_2950_;
v___y_2925_ = v___x_2955_;
goto v___jp_2918_;
}
else
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_array_fget_borrowed(v_a_2903_, v___x_2953_);
lean_inc(v___x_2956_);
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
v___y_2919_ = v_a_2951_;
v___y_2920_ = v___y_2946_;
v___y_2921_ = v___y_2947_;
v___y_2922_ = v___x_2952_;
v___y_2923_ = v___x_2953_;
v___y_2924_ = v_a_2950_;
v___y_2925_ = v___x_2957_;
goto v___jp_2918_;
}
}
else
{
lean_object* v_a_2958_; lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec(v___y_2946_);
lean_dec(v_a_2903_);
lean_dec_ref(v_ands_2798_);
v_a_2958_ = lean_ctor_get(v___x_2949_, 0);
v_a_2959_ = lean_ctor_get(v___x_2949_, 1);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2949_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_inc(v_a_2958_);
lean_dec(v___x_2949_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2958_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
v___jp_2967_:
{
lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2969_ = lean_array_get_size(v_a_2903_);
v___x_2970_ = lean_nat_dec_eq(v___x_2969_, v___x_2813_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = lean_unsigned_to_nat(3u);
v___x_2972_ = lean_nat_dec_lt(v___x_2971_, v___x_2969_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; uint8_t v___x_2974_; 
lean_del_object(v___x_2906_);
v___x_2973_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__1));
v___x_2974_ = lean_nat_dec_lt(v___x_2813_, v___x_2969_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_box(0);
v___y_2945_ = v___x_2973_;
v___y_2946_ = v___x_2969_;
v___y_2947_ = v___y_2968_;
v___y_2948_ = v___x_2975_;
goto v___jp_2944_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_array_fget_borrowed(v_a_2903_, v___x_2813_);
lean_inc(v___x_2976_);
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
v___y_2945_ = v___x_2973_;
v___y_2946_ = v___x_2969_;
v___y_2947_ = v___y_2968_;
v___y_2948_ = v___x_2977_;
goto v___jp_2944_;
}
}
else
{
lean_dec(v_a_2903_);
lean_dec_ref(v_ands_2798_);
v___y_2909_ = v___x_2969_;
goto v___jp_2908_;
}
}
else
{
lean_dec(v_a_2903_);
lean_dec_ref(v_ands_2798_);
v___y_2909_ = v___x_2969_;
goto v___jp_2908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(lean_object* v_s_2993_, uint8_t v_needsRange_2994_, lean_object* v_ors_2995_, lean_object* v_ands_2996_, lean_object* v_p_2997_){
_start:
{
lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = lean_string_utf8_byte_size(v_s_2993_);
v___x_3005_ = lean_nat_dec_eq(v_p_2997_, v___x_3004_);
if (v___x_3005_ == 0)
{
uint32_t v_c_3020_; uint8_t v___y_3022_; uint8_t v___y_3023_; uint8_t v___y_3064_; uint8_t v___y_3065_; uint8_t v___y_3071_; uint8_t v___y_3112_; uint32_t v___x_3122_; uint8_t v___x_3123_; 
v_c_3020_ = lean_string_utf8_get_fast(v_s_2993_, v_p_2997_);
v___x_3122_ = 65;
v___x_3123_ = lean_uint32_dec_le(v___x_3122_, v_c_3020_);
if (v___x_3123_ == 0)
{
goto v___jp_3117_;
}
else
{
uint32_t v___x_3124_; uint8_t v___x_3125_; 
v___x_3124_ = 90;
v___x_3125_ = lean_uint32_dec_le(v_c_3020_, v___x_3124_);
if (v___x_3125_ == 0)
{
goto v___jp_3117_;
}
else
{
goto v___jp_3006_;
}
}
v___jp_3021_:
{
if (v___y_3023_ == 0)
{
uint32_t v___x_3024_; uint8_t v___x_3025_; 
v___x_3024_ = 44;
v___x_3025_ = lean_uint32_dec_eq(v_c_3020_, v___x_3024_);
if (v___x_3025_ == 0)
{
uint32_t v___x_3026_; uint8_t v___x_3027_; 
v___x_3026_ = 124;
v___x_3027_ = lean_uint32_dec_eq(v_c_3020_, v___x_3026_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; 
lean_inc_ref(v_s_2993_);
v___x_3028_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_2993_, v_p_2997_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v_a_3030_; lean_object* v___x_3031_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
v_a_3030_ = lean_ctor_get(v___x_3028_, 1);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3028_, 2);
v___x_3031_ = lean_array_push(v_ands_2996_, v_a_3029_);
v_needsRange_2994_ = v___x_3027_;
v_ands_2996_ = v___x_3031_;
v_p_2997_ = v_a_3030_;
goto _start;
}
else
{
lean_object* v_a_3033_; lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v_ands_2996_);
lean_dec_ref(v_ors_2995_);
lean_dec_ref(v_s_2993_);
v_a_3033_ = lean_ctor_get(v___x_3028_, 0);
v_a_3034_ = lean_ctor_get(v___x_3028_, 1);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3028_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_inc(v_a_3033_);
lean_dec(v___x_3028_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3033_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
else
{
lean_object* v_p_3042_; uint8_t v___x_3043_; 
v_p_3042_ = lean_string_utf8_next_fast(v_s_2993_, v_p_2997_);
lean_dec(v_p_2997_);
v___x_3043_ = lean_nat_dec_eq(v_p_3042_, v___x_3004_);
if (v___x_3043_ == 0)
{
uint32_t v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = lean_string_utf8_get_fast(v_s_2993_, v_p_3042_);
v___x_3045_ = lean_uint32_dec_eq(v___x_3044_, v___x_3026_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
lean_dec_ref(v_ands_2996_);
lean_dec_ref(v_ors_2995_);
lean_dec_ref(v_s_2993_);
v___x_3046_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v_p_3042_);
return v___x_3047_;
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3048_ = lean_array_get_size(v_ands_2996_);
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_nat_dec_eq(v___x_3048_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = lean_array_push(v_ors_2995_, v_ands_2996_);
v___x_3052_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2));
v___x_3053_ = lean_string_utf8_next_fast(v_s_2993_, v_p_3042_);
v_needsRange_2994_ = v___y_3022_;
v_ors_2995_ = v___x_3051_;
v_ands_2996_ = v___x_3052_;
v_p_2997_ = v___x_3053_;
goto _start;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_dec_ref(v_ands_2996_);
lean_dec_ref(v_ors_2995_);
lean_dec_ref(v_s_2993_);
v___x_3055_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v_p_3042_);
return v___x_3056_;
}
}
}
else
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref(v_ands_2996_);
lean_dec_ref(v_ors_2995_);
lean_dec_ref(v_s_2993_);
v___x_3057_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v_p_3042_);
return v___x_3058_;
}
}
}
else
{
if (v_needsRange_2994_ == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_string_utf8_next_fast(v_s_2993_, v_p_2997_);
lean_dec(v_p_2997_);
v_needsRange_2994_ = v___y_3022_;
v_p_2997_ = v___x_3059_;
goto _start;
}
else
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec_ref(v_ands_2996_);
lean_dec_ref(v_ors_2995_);
lean_dec_ref(v_s_2993_);
v___x_3061_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
lean_ctor_set(v___x_3062_, 1, v_p_2997_);
return v___x_3062_;
}
}
}
else
{
goto v___jp_3001_;
}
}
v___jp_3063_:
{
if (v___y_3065_ == 0)
{
uint32_t v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = 13;
v___x_3067_ = lean_uint32_dec_eq(v_c_3020_, v___x_3066_);
if (v___x_3067_ == 0)
{
uint32_t v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = 10;
v___x_3069_ = lean_uint32_dec_eq(v_c_3020_, v___x_3068_);
v___y_3022_ = v___y_3064_;
v___y_3023_ = v___x_3069_;
goto v___jp_3021_;
}
else
{
v___y_3022_ = v___y_3064_;
v___y_3023_ = v___x_3067_;
goto v___jp_3021_;
}
}
else
{
goto v___jp_3001_;
}
}
v___jp_3070_:
{
if (v___y_3071_ == 0)
{
uint32_t v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = 42;
v___x_3073_ = lean_uint32_dec_eq(v_c_3020_, v___x_3072_);
if (v___x_3073_ == 0)
{
uint32_t v___x_3074_; uint8_t v___x_3075_; 
v___x_3074_ = 94;
v___x_3075_ = lean_uint32_dec_eq(v_c_3020_, v___x_3074_);
if (v___x_3075_ == 0)
{
uint32_t v___x_3076_; uint8_t v___x_3077_; 
v___x_3076_ = 126;
v___x_3077_ = lean_uint32_dec_eq(v_c_3020_, v___x_3076_);
if (v___x_3077_ == 0)
{
uint8_t v___x_3078_; uint32_t v___x_3079_; uint8_t v___x_3080_; 
v___x_3078_ = 1;
v___x_3079_ = 32;
v___x_3080_ = lean_uint32_dec_eq(v_c_3020_, v___x_3079_);
if (v___x_3080_ == 0)
{
uint32_t v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = 9;
v___x_3082_ = lean_uint32_dec_eq(v_c_3020_, v___x_3081_);
v___y_3064_ = v___x_3078_;
v___y_3065_ = v___x_3082_;
goto v___jp_3063_;
}
else
{
v___y_3064_ = v___x_3078_;
v___y_3065_ = v___x_3080_;
goto v___jp_3063_;
}
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_string_utf8_next_fast(v_s_2993_, v_p_2997_);
lean_dec(v_p_2997_);
lean_inc_ref(v_s_2993_);
v___x_3084_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(v_s_2993_, v_ands_2996_, v___x_3083_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v_a_3086_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3085_);
v_a_3086_ = lean_ctor_get(v___x_3084_, 1);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3084_, 2);
v_needsRange_2994_ = v___x_3075_;
v_ands_2996_ = v_a_3085_;
v_p_2997_ = v_a_3086_;
goto _start;
}
else
{
lean_object* v_a_3088_; lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec_ref(v_ors_2995_);
lean_dec_ref(v_s_2993_);
v_a_3088_ = lean_ctor_get(v___x_3084_, 0);
v_a_3089_ = lean_ctor_get(v___x_3084_, 1);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3084_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_inc(v_a_3088_);
lean_dec(v___x_3084_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3088_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = lean_string_utf8_next_fast(v_s_2993_, v_p_2997_);
lean_dec(v_p_2997_);
lean_inc_ref(v_s_2993_);
v___x_3098_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(v_s_2993_, v_ands_2996_, v___x_3097_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v_a_3100_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3099_);
v_a_3100_ = lean_ctor_get(v___x_3098_, 1);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3098_, 2);
v_needsRange_2994_ = v___x_3073_;
v_ands_2996_ = v_a_3099_;
v_p_2997_ = v_a_3100_;
goto _start;
}
else
{
lean_object* v_a_3102_; lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref(v_ors_2995_);
lean_dec_ref(v_s_2993_);
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
}
else
{
goto v___jp_3006_;
}
}
else
{
goto v___jp_3006_;
}
}
v___jp_3111_:
{
if (v___y_3112_ == 0)
{
uint32_t v___x_3113_; uint8_t v___x_3114_; 
v___x_3113_ = 48;
v___x_3114_ = lean_uint32_dec_le(v___x_3113_, v_c_3020_);
if (v___x_3114_ == 0)
{
v___y_3071_ = v___x_3114_;
goto v___jp_3070_;
}
else
{
uint32_t v___x_3115_; uint8_t v___x_3116_; 
v___x_3115_ = 57;
v___x_3116_ = lean_uint32_dec_le(v_c_3020_, v___x_3115_);
v___y_3071_ = v___x_3116_;
goto v___jp_3070_;
}
}
else
{
goto v___jp_3006_;
}
}
v___jp_3117_:
{
uint32_t v___x_3118_; uint8_t v___x_3119_; 
v___x_3118_ = 97;
v___x_3119_ = lean_uint32_dec_le(v___x_3118_, v_c_3020_);
if (v___x_3119_ == 0)
{
v___y_3112_ = v___x_3119_;
goto v___jp_3111_;
}
else
{
uint32_t v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = 122;
v___x_3121_ = lean_uint32_dec_le(v_c_3020_, v___x_3120_);
v___y_3112_ = v___x_3121_;
goto v___jp_3111_;
}
}
}
else
{
lean_dec_ref(v_s_2993_);
if (v_needsRange_2994_ == 0)
{
lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3126_ = lean_array_get_size(v_ands_2996_);
v___x_3127_ = lean_unsigned_to_nat(0u);
v___x_3128_ = lean_nat_dec_eq(v___x_3126_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_array_push(v_ors_2995_, v_ands_2996_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
lean_ctor_set(v___x_3130_, 1, v_p_2997_);
return v___x_3130_;
}
else
{
lean_dec_ref(v_ands_2996_);
lean_dec_ref(v_ors_2995_);
goto v___jp_2998_;
}
}
else
{
lean_dec_ref(v_ands_2996_);
lean_dec_ref(v_ors_2995_);
goto v___jp_2998_;
}
}
v___jp_2998_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
lean_ctor_set(v___x_3000_, 1, v_p_2997_);
return v___x_3000_;
}
v___jp_3001_:
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_string_utf8_next_fast(v_s_2993_, v_p_2997_);
lean_dec(v_p_2997_);
v_p_2997_ = v___x_3002_;
goto _start;
}
v___jp_3006_:
{
lean_object* v___x_3007_; 
lean_inc_ref(v_s_2993_);
v___x_3007_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(v_s_2993_, v_ands_2996_, v_p_2997_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v_a_3009_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
v_a_3009_ = lean_ctor_get(v___x_3007_, 1);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3007_, 2);
v_needsRange_2994_ = v___x_3005_;
v_ands_2996_ = v_a_3008_;
v_p_2997_ = v_a_3009_;
goto _start;
}
else
{
lean_object* v_a_3011_; lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec_ref(v_ors_2995_);
lean_dec_ref(v_s_2993_);
v_a_3011_ = lean_ctor_get(v___x_3007_, 0);
v_a_3012_ = lean_ctor_get(v___x_3007_, 1);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3007_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_inc(v_a_3011_);
lean_dec(v___x_3007_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3011_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(lean_object* v_s_3131_, lean_object* v_needsRange_3132_, lean_object* v_ors_3133_, lean_object* v_ands_3134_, lean_object* v_p_3135_){
_start:
{
uint8_t v_needsRange_boxed_3136_; lean_object* v_res_3137_; 
v_needsRange_boxed_3136_ = lean_unbox(v_needsRange_3132_);
v_res_3137_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3131_, v_needsRange_boxed_3136_, v_ors_3133_, v_ands_3134_, v_p_3135_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object* v_s_3140_, lean_object* v_a_3141_){
_start:
{
uint8_t v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = 1;
v___x_3143_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3140_);
v___x_3144_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3140_, v___x_3142_, v___x_3143_, v___x_3143_, v_a_3141_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3154_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_a_3146_ = lean_ctor_get(v___x_3144_, 1);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3148_ = v___x_3144_;
v_isShared_3149_ = v_isSharedCheck_3154_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3154_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_s_3140_);
lean_ctor_set(v___x_3150_, 1, v_a_3145_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 0, v___x_3150_);
v___x_3152_ = v___x_3148_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_a_3146_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v_s_3140_);
v_a_3155_ = lean_ctor_get(v___x_3144_, 0);
v_a_3156_ = lean_ctor_get(v___x_3144_, 1);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3144_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_inc(v_a_3155_);
lean_dec(v___x_3144_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3155_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_parse(lean_object* v_s_3165_){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3166_ = ((lean_object*)(l_Lake_VerRange_parse___closed__0));
v___x_3167_ = lean_unsigned_to_nat(0u);
v___x_3168_ = lean_string_utf8_byte_size(v_s_3165_);
v___x_3169_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_3165_, v___x_3166_, v___x_3167_, v___x_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(lean_object* v_ver_3170_, lean_object* v_as_3171_, size_t v_i_3172_, size_t v_stop_3173_){
_start:
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_usize_dec_eq(v_i_3172_, v_stop_3173_);
if (v___x_3174_ == 0)
{
uint8_t v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3175_ = 1;
v___x_3176_ = lean_array_uget_borrowed(v_as_3171_, v_i_3172_);
v___x_3177_ = l_Lake_VerComparator_test(v___x_3176_, v_ver_3170_);
if (v___x_3177_ == 0)
{
return v___x_3175_;
}
else
{
if (v___x_3174_ == 0)
{
size_t v___x_3178_; size_t v___x_3179_; 
v___x_3178_ = ((size_t)1ULL);
v___x_3179_ = lean_usize_add(v_i_3172_, v___x_3178_);
v_i_3172_ = v___x_3179_;
goto _start;
}
else
{
return v___x_3175_;
}
}
}
else
{
uint8_t v___x_3181_; 
v___x_3181_ = 0;
return v___x_3181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0___boxed(lean_object* v_ver_3182_, lean_object* v_as_3183_, lean_object* v_i_3184_, lean_object* v_stop_3185_){
_start:
{
size_t v_i_boxed_3186_; size_t v_stop_boxed_3187_; uint8_t v_res_3188_; lean_object* v_r_3189_; 
v_i_boxed_3186_ = lean_unbox_usize(v_i_3184_);
lean_dec(v_i_3184_);
v_stop_boxed_3187_ = lean_unbox_usize(v_stop_3185_);
lean_dec(v_stop_3185_);
v_res_3188_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3182_, v_as_3183_, v_i_boxed_3186_, v_stop_boxed_3187_);
lean_dec_ref(v_as_3183_);
lean_dec_ref(v_ver_3182_);
v_r_3189_ = lean_box(v_res_3188_);
return v_r_3189_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(lean_object* v_ver_3190_, lean_object* v_as_3191_, size_t v_i_3192_, size_t v_stop_3193_){
_start:
{
uint8_t v___x_3194_; 
v___x_3194_ = lean_usize_dec_eq(v_i_3192_, v_stop_3193_);
if (v___x_3194_ == 0)
{
uint8_t v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v___x_3195_ = 1;
v___x_3196_ = lean_array_uget_borrowed(v_as_3191_, v_i_3192_);
v___x_3197_ = lean_unsigned_to_nat(0u);
v___x_3198_ = lean_array_get_size(v___x_3196_);
v___x_3199_ = lean_nat_dec_lt(v___x_3197_, v___x_3198_);
if (v___x_3199_ == 0)
{
return v___x_3195_;
}
else
{
if (v___x_3199_ == 0)
{
return v___x_3195_;
}
else
{
size_t v___x_3200_; size_t v___x_3201_; uint8_t v___x_3202_; 
v___x_3200_ = ((size_t)0ULL);
v___x_3201_ = lean_usize_of_nat(v___x_3198_);
v___x_3202_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3190_, v___x_3196_, v___x_3200_, v___x_3201_);
if (v___x_3202_ == 0)
{
return v___x_3195_;
}
else
{
if (v___x_3194_ == 0)
{
size_t v___x_3203_; size_t v___x_3204_; 
v___x_3203_ = ((size_t)1ULL);
v___x_3204_ = lean_usize_add(v_i_3192_, v___x_3203_);
v_i_3192_ = v___x_3204_;
goto _start;
}
else
{
return v___x_3195_;
}
}
}
}
}
else
{
uint8_t v___x_3206_; 
v___x_3206_ = 0;
return v___x_3206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1___boxed(lean_object* v_ver_3207_, lean_object* v_as_3208_, lean_object* v_i_3209_, lean_object* v_stop_3210_){
_start:
{
size_t v_i_boxed_3211_; size_t v_stop_boxed_3212_; uint8_t v_res_3213_; lean_object* v_r_3214_; 
v_i_boxed_3211_ = lean_unbox_usize(v_i_3209_);
lean_dec(v_i_3209_);
v_stop_boxed_3212_ = lean_unbox_usize(v_stop_3210_);
lean_dec(v_stop_3210_);
v_res_3213_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3207_, v_as_3208_, v_i_boxed_3211_, v_stop_boxed_3212_);
lean_dec_ref(v_as_3208_);
lean_dec_ref(v_ver_3207_);
v_r_3214_ = lean_box(v_res_3213_);
return v_r_3214_;
}
}
LEAN_EXPORT uint8_t l_Lake_VerRange_test(lean_object* v_self_3215_, lean_object* v_ver_3216_){
_start:
{
lean_object* v_clauses_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v_clauses_3217_ = lean_ctor_get(v_self_3215_, 1);
v___x_3218_ = lean_unsigned_to_nat(0u);
v___x_3219_ = lean_array_get_size(v_clauses_3217_);
v___x_3220_ = lean_nat_dec_lt(v___x_3218_, v___x_3219_);
if (v___x_3220_ == 0)
{
return v___x_3220_;
}
else
{
if (v___x_3220_ == 0)
{
return v___x_3220_;
}
else
{
size_t v___x_3221_; size_t v___x_3222_; uint8_t v___x_3223_; 
v___x_3221_ = ((size_t)0ULL);
v___x_3222_ = lean_usize_of_nat(v___x_3219_);
v___x_3223_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3216_, v_clauses_3217_, v___x_3221_, v___x_3222_);
return v___x_3223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_test___boxed(lean_object* v_self_3224_, lean_object* v_ver_3225_){
_start:
{
uint8_t v_res_3226_; lean_object* v_r_3227_; 
v_res_3226_ = l_Lake_VerRange_test(v_self_3224_, v_ver_3225_);
lean_dec_ref(v_ver_3225_);
lean_dec_ref(v_self_3224_);
v_r_3227_ = lean_box(v_res_3226_);
return v_r_3227_;
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
