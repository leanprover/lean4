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
lean_object* l_Lean_Data_Trie_empty___redArg();
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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pr-release-"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ToolchainVer_ofString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "-nightly"};
static const lean_object* l_Lake_ToolchainVer_ofString___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_ofString___closed__0_value;
static const lean_string_object l_Lake_ToolchainVer_ofString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l_Lake_ToolchainVer_ofString___closed__1 = (const lean_object*)&l_Lake_ToolchainVer_ofString___closed__1_value;
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
if (lean_obj_tag(v_a_257_) == 1)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_273_; 
lean_inc_ref(v_a_257_);
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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(lean_object* v_s_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_string_utf8_byte_size(v_s_1126_);
v___x_1128_ = lean_unsigned_to_nat(8u);
v___x_1129_ = lean_nat_dec_le(v___x_1128_, v___x_1127_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
lean_dec_ref(v_s_1126_);
v___x_1130_ = lean_box(0);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1131_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_string_memcmp(v_s_1126_, v___x_1131_, v___x_1132_, v___x_1132_, v___x_1128_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec_ref(v_s_1126_);
v___x_1134_ = lean_box(0);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_inc_ref(v_s_1126_);
v___x_1135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1135_, 0, v_s_1126_);
lean_ctor_set(v___x_1135_, 1, v___x_1132_);
lean_ctor_set(v___x_1135_, 2, v___x_1127_);
v___x_1136_ = l_String_Slice_pos_x21(v___x_1135_, v___x_1128_);
lean_dec_ref_known(v___x_1135_, 3);
v___x_1137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1137_, 0, v_s_1126_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
lean_ctor_set(v___x_1137_, 2, v___x_1127_);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(lean_object* v_s_1139_, lean_object* v_pat_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v_s_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(lean_object* v_s_1142_, lean_object* v_pat_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(v_s_1142_, v_pat_1143_);
lean_dec_ref(v_pat_1143_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(lean_object* v_s_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1146_ = lean_string_utf8_byte_size(v_s_1145_);
v___x_1147_ = lean_unsigned_to_nat(16u);
v___x_1148_ = lean_nat_dec_le(v___x_1147_, v___x_1146_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
lean_dec_ref(v_s_1145_);
v___x_1149_ = lean_box(0);
return v___x_1149_;
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1151_ = lean_unsigned_to_nat(0u);
v___x_1152_ = lean_string_memcmp(v_s_1145_, v___x_1150_, v___x_1151_, v___x_1151_, v___x_1147_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
lean_dec_ref(v_s_1145_);
v___x_1153_ = lean_box(0);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_inc_ref(v_s_1145_);
v___x_1154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1154_, 0, v_s_1145_);
lean_ctor_set(v___x_1154_, 1, v___x_1151_);
lean_ctor_set(v___x_1154_, 2, v___x_1146_);
v___x_1155_ = l_String_Slice_pos_x21(v___x_1154_, v___x_1147_);
lean_dec_ref_known(v___x_1154_, 3);
v___x_1156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1156_, 0, v_s_1145_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
lean_ctor_set(v___x_1156_, 2, v___x_1146_);
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(lean_object* v_s_1158_, lean_object* v_pat_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v_s_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(lean_object* v_s_1161_, lean_object* v_pat_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(v_s_1161_, v_pat_1162_);
lean_dec_ref(v_pat_1162_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object* v_s_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = lean_string_utf8_byte_size(v_s_1165_);
v___x_1167_ = lean_unsigned_to_nat(11u);
v___x_1168_ = lean_nat_dec_le(v___x_1167_, v___x_1166_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
lean_dec_ref(v_s_1165_);
v___x_1169_ = lean_box(0);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1170_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0));
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_string_memcmp(v_s_1165_, v___x_1170_, v___x_1171_, v___x_1171_, v___x_1167_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec_ref(v_s_1165_);
v___x_1173_ = lean_box(0);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_inc_ref(v_s_1165_);
v___x_1174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1174_, 0, v_s_1165_);
lean_ctor_set(v___x_1174_, 1, v___x_1171_);
lean_ctor_set(v___x_1174_, 2, v___x_1166_);
v___x_1175_ = l_String_Slice_pos_x21(v___x_1174_, v___x_1167_);
lean_dec_ref_known(v___x_1174_, 3);
v___x_1176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1176_, 0, v_s_1165_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
lean_ctor_set(v___x_1176_, 2, v___x_1166_);
v___x_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(lean_object* v_s_1178_, lean_object* v_pat_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v_s_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object* v_s_1181_, lean_object* v_pat_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(v_s_1181_, v_pat_1182_);
lean_dec_ref(v_pat_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(lean_object* v___x_1184_, lean_object* v_ver_1185_, lean_object* v_a_1186_, lean_object* v_b_1187_){
_start:
{
uint8_t v_decide_1188_; 
v_decide_1188_ = lean_nat_dec_eq(v_a_1186_, v___x_1184_);
if (v_decide_1188_ == 0)
{
uint32_t v___x_1189_; uint32_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1189_ = lean_string_utf8_get_fast(v_ver_1185_, v_a_1186_);
v___x_1190_ = 58;
v___x_1191_ = lean_uint32_dec_eq(v___x_1189_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_string_utf8_next_fast(v_ver_1185_, v_a_1186_);
lean_dec(v_a_1186_);
v_a_1186_ = v___x_1193_;
v_b_1187_ = v___x_1192_;
goto _start;
}
else
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_a_1186_);
return v___x_1195_;
}
}
else
{
lean_dec(v_a_1186_);
lean_inc(v_b_1187_);
return v_b_1187_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg___boxed(lean_object* v___x_1196_, lean_object* v_ver_1197_, lean_object* v_a_1198_, lean_object* v_b_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1196_, v_ver_1197_, v_a_1198_, v_b_1199_);
lean_dec(v_b_1199_);
lean_dec_ref(v_ver_1197_);
lean_dec(v___x_1196_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object* v___x_1201_, lean_object* v_rest_1202_, lean_object* v_a_1203_, lean_object* v_b_1204_){
_start:
{
uint8_t v_decide_1205_; 
v_decide_1205_ = lean_nat_dec_eq(v_a_1203_, v___x_1201_);
if (v_decide_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_string_utf8_next_fast(v_rest_1202_, v_a_1203_);
lean_dec(v_a_1203_);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_add(v_b_1204_, v___x_1207_);
lean_dec(v_b_1204_);
v_a_1203_ = v___x_1206_;
v_b_1204_ = v___x_1208_;
goto _start;
}
else
{
lean_dec(v_a_1203_);
return v_b_1204_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg___boxed(lean_object* v___x_1210_, lean_object* v_rest_1211_, lean_object* v_a_1212_, lean_object* v_b_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___x_1210_, v_rest_1211_, v_a_1212_, v_b_1213_);
lean_dec_ref(v_rest_1211_);
lean_dec(v___x_1210_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofString(lean_object* v_ver_1217_){
_start:
{
lean_object* v___y_1219_; uint8_t v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1254_; lean_object* v___y_1255_; uint8_t v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1264_; uint8_t v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___y_1337_; lean_object* v_searcher_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_searcher_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_string_utf8_byte_size(v_ver_1217_);
v___x_1347_ = lean_box(0);
v___x_1348_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1346_, v_ver_1217_, v_searcher_1345_, v___x_1347_);
if (lean_obj_tag(v___x_1348_) == 0)
{
v___y_1337_ = v___x_1346_;
goto v___jp_1336_;
}
else
{
lean_object* v_val_1349_; 
v_val_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_val_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___y_1337_ = v_val_1349_;
goto v___jp_1336_;
}
v___jp_1218_:
{
if (v___y_1220_ == 0)
{
lean_object* v___x_1224_; 
v___x_1224_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v___y_1223_);
if (lean_obj_tag(v___x_1224_) == 1)
{
lean_object* v_val_1225_; lean_object* v_startInclusive_1226_; lean_object* v_endExclusive_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v_val_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v_startInclusive_1226_ = lean_ctor_get(v_val_1225_, 1);
v_endExclusive_1227_ = lean_ctor_get(v_val_1225_, 2);
v___x_1228_ = lean_nat_sub(v_endExclusive_1227_, v_startInclusive_1226_);
v___x_1229_ = lean_nat_dec_eq(v___x_1228_, v___y_1219_);
lean_dec(v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1230_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1231_ = lean_unsigned_to_nat(8u);
v___x_1232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___y_1219_);
lean_ctor_set(v___x_1232_, 2, v___x_1231_);
v___x_1233_ = l_String_Slice_beq(v_val_1225_, v___x_1232_);
lean_dec_ref_known(v___x_1232_, 3);
lean_dec(v_val_1225_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_inc_ref(v_ver_1217_);
v___x_1234_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1234_, 0, v_ver_1217_);
lean_ctor_set(v___x_1234_, 1, v_ver_1217_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; 
lean_dec_ref(v_ver_1217_);
v___x_1235_ = l_Lake_ToolchainVer_nightly___override(v___y_1222_, v___y_1221_);
return v___x_1235_;
}
}
else
{
lean_object* v___x_1236_; 
lean_dec(v_val_1225_);
lean_dec(v___y_1219_);
lean_dec_ref(v_ver_1217_);
v___x_1236_ = l_Lake_ToolchainVer_nightly___override(v___y_1222_, v___y_1221_);
return v___x_1236_;
}
}
else
{
lean_object* v___x_1237_; 
lean_dec(v___x_1224_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec(v___y_1219_);
lean_inc_ref(v_ver_1217_);
v___x_1237_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_ver_1217_);
lean_ctor_set(v___x_1237_, 1, v_ver_1217_);
return v___x_1237_;
}
}
else
{
lean_object* v___x_1238_; 
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1219_);
lean_dec_ref(v_ver_1217_);
v___x_1238_ = l_Lake_ToolchainVer_nightly___override(v___y_1222_, v___y_1221_);
return v___x_1238_;
}
}
v___jp_1239_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
lean_dec_ref(v___y_1245_);
v___x_1249_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_1243_);
v___x_1250_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___y_1240_, v___y_1244_, v___x_1249_, v___y_1243_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1240_);
v___x_1251_ = lean_nat_dec_le(v___x_1250_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec(v___x_1250_);
if (v___x_1251_ == 0)
{
if (lean_obj_tag(v___y_1248_) == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1243_);
lean_inc_ref(v_ver_1217_);
v___x_1252_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_ver_1217_);
lean_ctor_set(v___x_1252_, 1, v_ver_1217_);
return v___x_1252_;
}
else
{
v___y_1219_ = v___y_1243_;
v___y_1220_ = v___y_1242_;
v___y_1221_ = v___y_1248_;
v___y_1222_ = v___y_1246_;
v___y_1223_ = v___y_1247_;
goto v___jp_1218_;
}
}
else
{
v___y_1219_ = v___y_1243_;
v___y_1220_ = v___y_1242_;
v___y_1221_ = v___y_1248_;
v___y_1222_ = v___y_1246_;
v___y_1223_ = v___y_1247_;
goto v___jp_1218_;
}
}
v___jp_1253_:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_box(0);
v___y_1240_ = v___y_1254_;
v___y_1241_ = v___y_1257_;
v___y_1242_ = v___y_1256_;
v___y_1243_ = v___y_1255_;
v___y_1244_ = v___y_1258_;
v___y_1245_ = v___y_1259_;
v___y_1246_ = v___y_1260_;
v___y_1247_ = v___y_1261_;
v___y_1248_ = v___x_1262_;
goto v___jp_1239_;
}
v___jp_1263_:
{
lean_object* v___x_1268_; 
lean_inc_ref(v___y_1264_);
v___x_1268_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v___y_1264_);
if (lean_obj_tag(v___x_1268_) == 1)
{
lean_object* v_val_1269_; lean_object* v_rest_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_dec_ref(v___y_1264_);
v_val_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v_rest_1270_ = l_String_Slice_toString(v_val_1269_);
lean_dec(v_val_1269_);
v___x_1271_ = lean_unsigned_to_nat(10u);
v___x_1272_ = lean_string_utf8_byte_size(v_rest_1270_);
lean_inc_n(v___y_1266_, 3);
lean_inc_ref_n(v_rest_1270_, 2);
v___x_1273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1273_, 0, v_rest_1270_);
lean_ctor_set(v___x_1273_, 1, v___y_1266_);
lean_ctor_set(v___x_1273_, 2, v___x_1272_);
v___x_1274_ = l_String_Slice_Pos_nextn(v___x_1273_, v___y_1266_, v___x_1271_);
lean_inc(v___x_1274_);
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v_rest_1270_);
lean_ctor_set(v___x_1275_, 1, v___y_1266_);
lean_ctor_set(v___x_1275_, 2, v___x_1274_);
v___x_1276_ = l_String_Slice_toString(v___x_1275_);
lean_dec_ref_known(v___x_1275_, 3);
v___x_1277_ = l_Lake_Date_ofString_x3f(v___x_1276_);
if (lean_obj_tag(v___x_1277_) == 1)
{
lean_object* v_val_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_val_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_val_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = lean_unsigned_to_nat(4u);
v___x_1280_ = lean_nat_sub(v___x_1272_, v___x_1274_);
v___x_1281_ = lean_nat_dec_le(v___x_1279_, v___x_1280_);
lean_dec(v___x_1280_);
if (v___x_1281_ == 0)
{
lean_dec(v___x_1274_);
v___y_1254_ = v___x_1272_;
v___y_1255_ = v___y_1266_;
v___y_1256_ = v___y_1265_;
v___y_1257_ = v___x_1271_;
v___y_1258_ = v_rest_1270_;
v___y_1259_ = v___x_1273_;
v___y_1260_ = v_val_1278_;
v___y_1261_ = v___y_1267_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1283_ = lean_string_memcmp(v_rest_1270_, v___x_1282_, v___x_1274_, v___y_1266_, v___x_1279_);
if (v___x_1283_ == 0)
{
lean_dec(v___x_1274_);
v___y_1254_ = v___x_1272_;
v___y_1255_ = v___y_1266_;
v___y_1256_ = v___y_1265_;
v___y_1257_ = v___x_1271_;
v___y_1258_ = v_rest_1270_;
v___y_1259_ = v___x_1273_;
v___y_1260_ = v_val_1278_;
v___y_1261_ = v___y_1267_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_inc(v___x_1274_);
lean_inc_ref_n(v_rest_1270_, 2);
v___x_1284_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1284_, 0, v_rest_1270_);
lean_ctor_set(v___x_1284_, 1, v___x_1274_);
lean_ctor_set(v___x_1284_, 2, v___x_1272_);
v___x_1285_ = l_String_Slice_pos_x21(v___x_1284_, v___x_1279_);
lean_dec_ref_known(v___x_1284_, 3);
v___x_1286_ = lean_nat_add(v___x_1274_, v___x_1285_);
lean_dec(v___x_1285_);
lean_dec(v___x_1274_);
v___x_1287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1287_, 0, v_rest_1270_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
lean_ctor_set(v___x_1287_, 2, v___x_1272_);
v___x_1288_ = l_String_Slice_toString(v___x_1287_);
lean_dec_ref_known(v___x_1287_, 3);
v___x_1289_ = lean_string_utf8_byte_size(v___x_1288_);
lean_inc(v___y_1266_);
v___x_1290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___y_1266_);
lean_ctor_set(v___x_1290_, 2, v___x_1289_);
v___x_1291_ = l_String_Slice_toNat_x3f(v___x_1290_);
lean_dec_ref_known(v___x_1290_, 3);
v___y_1240_ = v___x_1272_;
v___y_1241_ = v___x_1271_;
v___y_1242_ = v___y_1265_;
v___y_1243_ = v___y_1266_;
v___y_1244_ = v_rest_1270_;
v___y_1245_ = v___x_1273_;
v___y_1246_ = v_val_1278_;
v___y_1247_ = v___y_1267_;
v___y_1248_ = v___x_1291_;
goto v___jp_1239_;
}
}
}
else
{
lean_object* v___x_1292_; 
lean_dec(v___x_1277_);
lean_dec(v___x_1274_);
lean_dec_ref_known(v___x_1273_, 3);
lean_dec_ref(v_rest_1270_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_inc_ref(v_ver_1217_);
v___x_1292_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_ver_1217_);
lean_ctor_set(v___x_1292_, 1, v_ver_1217_);
return v___x_1292_;
}
}
else
{
lean_object* v___x_1293_; 
lean_dec(v___x_1268_);
lean_dec(v___y_1266_);
v___x_1293_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___y_1264_);
if (lean_obj_tag(v___x_1293_) == 1)
{
lean_object* v_val_1294_; lean_object* v___x_1295_; 
v_val_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_val_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = l_String_Slice_toNat_x3f(v_val_1294_);
lean_dec(v_val_1294_);
if (lean_obj_tag(v___x_1295_) == 1)
{
if (v___y_1265_ == 0)
{
lean_object* v_val_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_val_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v___x_1297_ = ((lean_object*)(l_Lake_ToolchainVer_prOrigin___closed__0));
v___x_1298_ = lean_string_dec_eq(v___y_1267_, v___x_1297_);
lean_dec_ref(v___y_1267_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
lean_dec(v_val_1296_);
lean_inc_ref(v_ver_1217_);
v___x_1299_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1299_, 0, v_ver_1217_);
lean_ctor_set(v___x_1299_, 1, v_ver_1217_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; 
lean_dec_ref(v_ver_1217_);
v___x_1300_ = l_Lake_ToolchainVer_pr___override(v_val_1296_);
return v___x_1300_;
}
}
else
{
lean_object* v_val_1301_; lean_object* v___x_1302_; 
lean_dec_ref(v___y_1267_);
lean_dec_ref(v_ver_1217_);
v_val_1301_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_val_1301_);
lean_dec_ref_known(v___x_1295_, 1);
v___x_1302_ = l_Lake_ToolchainVer_pr___override(v_val_1301_);
return v___x_1302_;
}
}
else
{
lean_object* v___x_1303_; 
lean_dec(v___x_1295_);
lean_dec_ref(v___y_1267_);
lean_inc_ref(v_ver_1217_);
v___x_1303_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1303_, 0, v_ver_1217_);
lean_ctor_set(v___x_1303_, 1, v_ver_1217_);
return v___x_1303_;
}
}
else
{
lean_object* v___x_1304_; 
lean_dec(v___x_1293_);
lean_inc_ref(v_ver_1217_);
v___x_1304_ = l_Lake_StdVer_parse(v_ver_1217_);
if (lean_obj_tag(v___x_1304_) == 1)
{
if (v___y_1265_ == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1307_ = lean_string_dec_eq(v___y_1267_, v___x_1306_);
lean_dec_ref(v___y_1267_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_dec(v_a_1305_);
lean_inc_ref(v_ver_1217_);
v___x_1308_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_ver_1217_);
lean_ctor_set(v___x_1308_, 1, v_ver_1217_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; 
lean_dec_ref(v_ver_1217_);
v___x_1309_ = l_Lake_ToolchainVer_release___override(v_a_1305_);
return v___x_1309_;
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1311_; 
lean_dec_ref(v___y_1267_);
lean_dec_ref(v_ver_1217_);
v_a_1310_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1311_ = l_Lake_ToolchainVer_release___override(v_a_1310_);
return v___x_1311_;
}
}
else
{
lean_object* v___x_1312_; 
lean_dec_ref(v___x_1304_);
lean_dec_ref(v___y_1267_);
lean_inc_ref(v_ver_1217_);
v___x_1312_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1312_, 0, v_ver_1217_);
lean_ctor_set(v___x_1312_, 1, v_ver_1217_);
return v___x_1312_;
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v_noOrigin_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1316_ = lean_string_utf8_byte_size(v_fst_1314_);
v___x_1317_ = lean_unsigned_to_nat(0u);
v_noOrigin_1318_ = lean_nat_dec_eq(v___x_1316_, v___x_1317_);
v___x_1319_ = lean_string_utf8_byte_size(v_snd_1315_);
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_dec_le(v___x_1320_, v___x_1319_);
if (v___x_1321_ == 0)
{
v___y_1264_ = v_snd_1315_;
v___y_1265_ = v_noOrigin_1318_;
v___y_1266_ = v___x_1317_;
v___y_1267_ = v_fst_1314_;
goto v___jp_1263_;
}
else
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__1));
v___x_1323_ = lean_string_memcmp(v_snd_1315_, v___x_1322_, v___x_1317_, v___x_1317_, v___x_1320_);
if (v___x_1323_ == 0)
{
v___y_1264_ = v_snd_1315_;
v___y_1265_ = v_noOrigin_1318_;
v___y_1266_ = v___x_1317_;
v___y_1267_ = v_fst_1314_;
goto v___jp_1263_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_inc_ref(v_snd_1315_);
v___x_1324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1324_, 0, v_snd_1315_);
lean_ctor_set(v___x_1324_, 1, v___x_1317_);
lean_ctor_set(v___x_1324_, 2, v___x_1319_);
v___x_1325_ = l_String_Slice_Pos_nextn(v___x_1324_, v___x_1317_, v___x_1320_);
lean_dec_ref_known(v___x_1324_, 3);
v___x_1326_ = lean_string_utf8_extract_fast(v_snd_1315_, v___x_1325_, v___x_1319_);
lean_dec(v___x_1325_);
lean_dec_ref(v_snd_1315_);
v___x_1327_ = l_Lake_StdVer_parse(v___x_1326_);
if (lean_obj_tag(v___x_1327_) == 1)
{
if (v_noOrigin_1318_ == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1330_ = lean_string_dec_eq(v_fst_1314_, v___x_1329_);
lean_dec_ref(v_fst_1314_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
lean_dec(v_a_1328_);
lean_inc_ref(v_ver_1217_);
v___x_1331_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_ver_1217_);
lean_ctor_set(v___x_1331_, 1, v_ver_1217_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; 
lean_dec_ref(v_ver_1217_);
v___x_1332_ = l_Lake_ToolchainVer_release___override(v_a_1328_);
return v___x_1332_;
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v_fst_1314_);
lean_dec_ref(v_ver_1217_);
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
lean_dec_ref(v_fst_1314_);
lean_inc_ref(v_ver_1217_);
v___x_1335_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_ver_1217_);
lean_ctor_set(v___x_1335_, 1, v_ver_1217_);
return v___x_1335_;
}
}
}
}
v___jp_1336_:
{
lean_object* v___x_1338_; uint8_t v_decide_1339_; 
v___x_1338_ = lean_string_utf8_byte_size(v_ver_1217_);
v_decide_1339_ = lean_nat_dec_eq(v___y_1337_, v___x_1338_);
if (v_decide_1339_ == 0)
{
lean_object* v_pos_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_pos_1340_ = lean_string_utf8_next_fast(v_ver_1217_, v___y_1337_);
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = lean_string_utf8_extract_fast(v_ver_1217_, v___x_1341_, v___y_1337_);
lean_dec(v___y_1337_);
v___x_1343_ = lean_string_utf8_extract_fast(v_ver_1217_, v_pos_1340_, v___x_1338_);
v_fst_1314_ = v___x_1342_;
v_snd_1315_ = v___x_1343_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1344_; 
lean_dec(v___y_1337_);
v___x_1344_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
lean_inc_ref(v_ver_1217_);
v_fst_1314_ = v___x_1344_;
v_snd_1315_ = v_ver_1217_;
goto v___jp_1313_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(lean_object* v___x_1350_, lean_object* v___x_1351_, lean_object* v_rest_1352_, lean_object* v_inst_1353_, lean_object* v_R_1354_, lean_object* v_a_1355_, lean_object* v_b_1356_, lean_object* v_c_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___x_1350_, v_rest_1352_, v_a_1355_, v_b_1356_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v_rest_1361_, lean_object* v_inst_1362_, lean_object* v_R_1363_, lean_object* v_a_1364_, lean_object* v_b_1365_, lean_object* v_c_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(v___x_1359_, v___x_1360_, v_rest_1361_, v_inst_1362_, v_R_1363_, v_a_1364_, v_b_1365_, v_c_1366_);
lean_dec_ref(v_rest_1361_);
lean_dec_ref(v___x_1360_);
lean_dec(v___x_1359_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(lean_object* v___x_1368_, lean_object* v___x_1369_, lean_object* v_ver_1370_, lean_object* v_inst_1371_, lean_object* v_R_1372_, lean_object* v_a_1373_, lean_object* v_b_1374_, lean_object* v_c_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1368_, v_ver_1370_, v_a_1373_, v_b_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___boxed(lean_object* v___x_1377_, lean_object* v___x_1378_, lean_object* v_ver_1379_, lean_object* v_inst_1380_, lean_object* v_R_1381_, lean_object* v_a_1382_, lean_object* v_b_1383_, lean_object* v_c_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(v___x_1377_, v___x_1378_, v_ver_1379_, v_inst_1380_, v_R_1381_, v_a_1382_, v_b_1383_, v_c_1384_);
lean_dec(v_b_1383_);
lean_dec_ref(v_ver_1379_);
lean_dec_ref(v___x_1378_);
lean_dec(v___x_1377_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object* v_toolchainFile_1386_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_IO_FS_readFile(v_toolchainFile_1386_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1406_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1406_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1406_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_str_1397_; lean_object* v_startInclusive_1398_; lean_object* v_endExclusive_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = lean_string_utf8_byte_size(v_a_1389_);
v___x_1395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1395_, 0, v_a_1389_);
lean_ctor_set(v___x_1395_, 1, v___x_1393_);
lean_ctor_set(v___x_1395_, 2, v___x_1394_);
v___x_1396_ = l_String_Slice_trimAscii(v___x_1395_);
v_str_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc_ref(v_str_1397_);
v_startInclusive_1398_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_startInclusive_1398_);
v_endExclusive_1399_ = lean_ctor_get(v___x_1396_, 2);
lean_inc(v_endExclusive_1399_);
lean_dec_ref(v___x_1396_);
v___x_1400_ = lean_string_utf8_extract_fast(v_str_1397_, v_startInclusive_1398_, v_endExclusive_1399_);
lean_dec(v_endExclusive_1399_);
lean_dec(v_startInclusive_1398_);
lean_dec_ref(v_str_1397_);
v___x_1401_ = l_Lake_ToolchainVer_ofString(v___x_1400_);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1402_);
v___x_1404_ = v___x_1391_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
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
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1418_; 
v_a_1407_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1409_ = v___x_1388_;
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1388_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
if (lean_obj_tag(v_a_1407_) == 11)
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_dec_ref_known(v_a_1407_, 2);
v___x_1411_ = lean_box(0);
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
else
{
lean_object* v___x_1416_; 
if (v_isShared_1410_ == 0)
{
v___x_1416_ = v___x_1409_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1407_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f___boxed(lean_object* v_toolchainFile_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lake_ToolchainVer_ofFile_x3f(v_toolchainFile_1419_);
lean_dec_ref(v_toolchainFile_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f(lean_object* v_dir_1422_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((lean_object*)(l_Lake_toolchainFileName___closed__0));
v___x_1425_ = l_System_FilePath_join(v_dir_1422_, v___x_1424_);
v___x_1426_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1425_);
lean_dec_ref(v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f___boxed(lean_object* v_dir_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lake_ToolchainVer_ofDir_x3f(v_dir_1427_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0(lean_object* v_x_1432_){
_start:
{
lean_object* v_toString_1433_; lean_object* v___x_1434_; 
v_toString_1433_ = lean_ctor_get(v_x_1432_, 0);
lean_inc_ref(v_toString_1433_);
v___x_1434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1434_, 0, v_toString_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0___boxed(lean_object* v_x_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lake_ToolchainVer_instToJson___lam__0(v_x_1435_);
lean_dec_ref(v_x_1435_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instFromJson___lam__0(lean_object* v_x_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Json_getStr_x3f(v_x_1439_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1457_; 
v_a_1449_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1451_ = v___x_1440_;
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1440_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = l_Lake_ToolchainVer_ofString(v_a_1449_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1453_);
v___x_1455_ = v___x_1451_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_blt(lean_object* v_a_1460_, lean_object* v_b_1461_){
_start:
{
switch(lean_obj_tag(v_a_1460_))
{
case 0:
{
if (lean_obj_tag(v_b_1461_) == 0)
{
lean_object* v_ver_1462_; lean_object* v_ver_1463_; uint8_t v___x_1464_; 
v_ver_1462_ = lean_ctor_get(v_a_1460_, 1);
v_ver_1463_ = lean_ctor_get(v_b_1461_, 1);
v___x_1464_ = l_Lake_StdVer_compare(v_ver_1462_, v_ver_1463_);
if (v___x_1464_ == 0)
{
uint8_t v___x_1465_; 
v___x_1465_ = 1;
return v___x_1465_;
}
else
{
uint8_t v___x_1466_; 
v___x_1466_ = 0;
return v___x_1466_;
}
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = 0;
return v___x_1467_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1461_) == 1)
{
lean_object* v_date_1468_; lean_object* v_rev_1469_; lean_object* v_date_1470_; lean_object* v_rev_1471_; lean_object* v___y_1473_; uint8_t v___x_1478_; 
v_date_1468_ = lean_ctor_get(v_a_1460_, 1);
v_rev_1469_ = lean_ctor_get(v_a_1460_, 2);
v_date_1470_ = lean_ctor_get(v_b_1461_, 1);
v_rev_1471_ = lean_ctor_get(v_b_1461_, 2);
v___x_1478_ = l_Lake_instOrdDate_ord(v_date_1468_, v_date_1470_);
if (v___x_1478_ == 0)
{
uint8_t v___x_1479_; 
v___x_1479_ = 1;
return v___x_1479_;
}
else
{
uint8_t v___x_1480_; 
v___x_1480_ = l_Lake_instDecidableEqDate_decEq(v_date_1468_, v_date_1470_);
if (v___x_1480_ == 0)
{
return v___x_1480_;
}
else
{
if (lean_obj_tag(v_rev_1469_) == 0)
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_unsigned_to_nat(0u);
v___y_1473_ = v___x_1481_;
goto v___jp_1472_;
}
else
{
lean_object* v_val_1482_; 
v_val_1482_ = lean_ctor_get(v_rev_1469_, 0);
v___y_1473_ = v_val_1482_;
goto v___jp_1472_;
}
}
}
v___jp_1472_:
{
if (lean_obj_tag(v_rev_1471_) == 0)
{
lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_nat_dec_lt(v___y_1473_, v___x_1474_);
return v___x_1475_;
}
else
{
lean_object* v_val_1476_; uint8_t v___x_1477_; 
v_val_1476_ = lean_ctor_get(v_rev_1471_, 0);
v___x_1477_ = lean_nat_dec_lt(v___y_1473_, v_val_1476_);
return v___x_1477_;
}
}
}
else
{
uint8_t v___x_1483_; 
v___x_1483_ = 0;
return v___x_1483_;
}
}
default: 
{
uint8_t v___x_1484_; 
v___x_1484_ = 0;
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_blt___boxed(lean_object* v_a_1485_, lean_object* v_b_1486_){
_start:
{
uint8_t v_res_1487_; lean_object* v_r_1488_; 
v_res_1487_ = l_Lake_ToolchainVer_blt(v_a_1485_, v_b_1486_);
lean_dec_ref(v_b_1486_);
lean_dec_ref(v_a_1485_);
v_r_1488_ = lean_box(v_res_1487_);
return v_r_1488_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLT(void){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_box(0);
return v___x_1489_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLt(lean_object* v_a_1490_, lean_object* v_b_1491_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = l_Lake_ToolchainVer_blt(v_a_1490_, v_b_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLt___boxed(lean_object* v_a_1493_, lean_object* v_b_1494_){
_start:
{
uint8_t v_res_1495_; lean_object* v_r_1496_; 
v_res_1495_ = l_Lake_ToolchainVer_decLt(v_a_1493_, v_b_1494_);
lean_dec_ref(v_b_1494_);
lean_dec_ref(v_a_1493_);
v_r_1496_ = lean_box(v_res_1495_);
return v_r_1496_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_ble(lean_object* v_a_1497_, lean_object* v_b_1498_){
_start:
{
switch(lean_obj_tag(v_a_1497_))
{
case 0:
{
if (lean_obj_tag(v_b_1498_) == 0)
{
lean_object* v_ver_1499_; lean_object* v_ver_1500_; uint8_t v___x_1501_; 
v_ver_1499_ = lean_ctor_get(v_a_1497_, 1);
v_ver_1500_ = lean_ctor_get(v_b_1498_, 1);
v___x_1501_ = l_Lake_StdVer_compare(v_ver_1499_, v_ver_1500_);
if (v___x_1501_ == 2)
{
uint8_t v___x_1502_; 
v___x_1502_ = 0;
return v___x_1502_;
}
else
{
uint8_t v___x_1503_; 
v___x_1503_ = 1;
return v___x_1503_;
}
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = 0;
return v___x_1504_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1498_) == 1)
{
lean_object* v_date_1505_; lean_object* v_rev_1506_; lean_object* v_date_1507_; lean_object* v_rev_1508_; lean_object* v___y_1510_; uint8_t v___x_1515_; 
v_date_1505_ = lean_ctor_get(v_a_1497_, 1);
v_rev_1506_ = lean_ctor_get(v_a_1497_, 2);
v_date_1507_ = lean_ctor_get(v_b_1498_, 1);
v_rev_1508_ = lean_ctor_get(v_b_1498_, 2);
v___x_1515_ = l_Lake_instOrdDate_ord(v_date_1505_, v_date_1507_);
if (v___x_1515_ == 0)
{
uint8_t v___x_1516_; 
v___x_1516_ = 1;
return v___x_1516_;
}
else
{
uint8_t v___x_1517_; 
v___x_1517_ = l_Lake_instDecidableEqDate_decEq(v_date_1505_, v_date_1507_);
if (v___x_1517_ == 0)
{
return v___x_1517_;
}
else
{
if (lean_obj_tag(v_rev_1506_) == 0)
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_unsigned_to_nat(0u);
v___y_1510_ = v___x_1518_;
goto v___jp_1509_;
}
else
{
lean_object* v_val_1519_; 
v_val_1519_ = lean_ctor_get(v_rev_1506_, 0);
v___y_1510_ = v_val_1519_;
goto v___jp_1509_;
}
}
}
v___jp_1509_:
{
if (lean_obj_tag(v_rev_1508_) == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = lean_unsigned_to_nat(0u);
v___x_1512_ = lean_nat_dec_le(v___y_1510_, v___x_1511_);
return v___x_1512_;
}
else
{
lean_object* v_val_1513_; uint8_t v___x_1514_; 
v_val_1513_ = lean_ctor_get(v_rev_1508_, 0);
v___x_1514_ = lean_nat_dec_le(v___y_1510_, v_val_1513_);
return v___x_1514_;
}
}
}
else
{
uint8_t v___x_1520_; 
v___x_1520_ = 0;
return v___x_1520_;
}
}
case 2:
{
if (lean_obj_tag(v_b_1498_) == 2)
{
lean_object* v_n_1521_; lean_object* v_n_1522_; uint8_t v___x_1523_; 
v_n_1521_ = lean_ctor_get(v_a_1497_, 1);
v_n_1522_ = lean_ctor_get(v_b_1498_, 1);
v___x_1523_ = lean_nat_dec_eq(v_n_1521_, v_n_1522_);
return v___x_1523_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = 0;
return v___x_1524_;
}
}
default: 
{
if (lean_obj_tag(v_b_1498_) == 3)
{
lean_object* v_v_1525_; lean_object* v_v_1526_; uint8_t v___x_1527_; 
v_v_1525_ = lean_ctor_get(v_a_1497_, 1);
v_v_1526_ = lean_ctor_get(v_b_1498_, 1);
v___x_1527_ = lean_string_dec_eq(v_v_1525_, v_v_1526_);
return v___x_1527_;
}
else
{
uint8_t v___x_1528_; 
v___x_1528_ = 0;
return v___x_1528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ble___boxed(lean_object* v_a_1529_, lean_object* v_b_1530_){
_start:
{
uint8_t v_res_1531_; lean_object* v_r_1532_; 
v_res_1531_ = l_Lake_ToolchainVer_ble(v_a_1529_, v_b_1530_);
lean_dec_ref(v_b_1530_);
lean_dec_ref(v_a_1529_);
v_r_1532_ = lean_box(v_res_1531_);
return v_r_1532_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLE(void){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_box(0);
return v___x_1533_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLe(lean_object* v_a_1534_, lean_object* v_b_1535_){
_start:
{
uint8_t v___x_1536_; 
v___x_1536_ = l_Lake_ToolchainVer_ble(v_a_1534_, v_b_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLe___boxed(lean_object* v_a_1537_, lean_object* v_b_1538_){
_start:
{
uint8_t v_res_1539_; lean_object* v_r_1540_; 
v_res_1539_ = l_Lake_ToolchainVer_decLe(v_a_1537_, v_b_1538_);
lean_dec_ref(v_b_1538_);
lean_dec_ref(v_a_1537_);
v_r_1540_ = lean_box(v_res_1539_);
return v_r_1540_;
}
}
LEAN_EXPORT lean_object* l_Lake_normalizeToolchain(lean_object* v_s_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v_toString_1543_; 
v___x_1542_ = l_Lake_ToolchainVer_ofString(v_s_1541_);
v_toString_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc_ref(v_toString_1543_);
lean_dec_ref(v___x_1542_);
return v_toString_1543_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeVersionToolchainVer___lam__0(lean_object* v_x_1548_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = l_Lake_ToolchainVer_ofString(v_x_1548_);
v___x_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx(uint8_t v_x_1553_){
_start:
{
switch(v_x_1553_)
{
case 0:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_unsigned_to_nat(0u);
return v___x_1554_;
}
case 1:
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_unsigned_to_nat(1u);
return v___x_1555_;
}
case 2:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_unsigned_to_nat(2u);
return v___x_1556_;
}
case 3:
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_unsigned_to_nat(3u);
return v___x_1557_;
}
case 4:
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_unsigned_to_nat(4u);
return v___x_1558_;
}
default: 
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_unsigned_to_nat(5u);
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___boxed(lean_object* v_x_1560_){
_start:
{
uint8_t v_x_boxed_1561_; lean_object* v_res_1562_; 
v_x_boxed_1561_ = lean_unbox(v_x_1560_);
v_res_1562_ = l_Lake_ComparatorOp_ctorIdx(v_x_boxed_1561_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg(lean_object* v_k_1563_){
_start:
{
lean_inc(v_k_1563_);
return v_k_1563_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg___boxed(lean_object* v_k_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lake_ComparatorOp_ctorElim___redArg(v_k_1564_);
lean_dec(v_k_1564_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim(lean_object* v_motive_1566_, lean_object* v_ctorIdx_1567_, uint8_t v_t_1568_, lean_object* v_h_1569_, lean_object* v_k_1570_){
_start:
{
lean_inc(v_k_1570_);
return v_k_1570_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___boxed(lean_object* v_motive_1571_, lean_object* v_ctorIdx_1572_, lean_object* v_t_1573_, lean_object* v_h_1574_, lean_object* v_k_1575_){
_start:
{
uint8_t v_t_boxed_1576_; lean_object* v_res_1577_; 
v_t_boxed_1576_ = lean_unbox(v_t_1573_);
v_res_1577_ = l_Lake_ComparatorOp_ctorElim(v_motive_1571_, v_ctorIdx_1572_, v_t_boxed_1576_, v_h_1574_, v_k_1575_);
lean_dec(v_k_1575_);
lean_dec(v_ctorIdx_1572_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg(lean_object* v_lt_1578_){
_start:
{
lean_inc(v_lt_1578_);
return v_lt_1578_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg___boxed(lean_object* v_lt_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lake_ComparatorOp_lt_elim___redArg(v_lt_1579_);
lean_dec(v_lt_1579_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim(lean_object* v_motive_1581_, uint8_t v_t_1582_, lean_object* v_h_1583_, lean_object* v_lt_1584_){
_start:
{
lean_inc(v_lt_1584_);
return v_lt_1584_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___boxed(lean_object* v_motive_1585_, lean_object* v_t_1586_, lean_object* v_h_1587_, lean_object* v_lt_1588_){
_start:
{
uint8_t v_t_boxed_1589_; lean_object* v_res_1590_; 
v_t_boxed_1589_ = lean_unbox(v_t_1586_);
v_res_1590_ = l_Lake_ComparatorOp_lt_elim(v_motive_1585_, v_t_boxed_1589_, v_h_1587_, v_lt_1588_);
lean_dec(v_lt_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg(lean_object* v_le_1591_){
_start:
{
lean_inc(v_le_1591_);
return v_le_1591_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg___boxed(lean_object* v_le_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lake_ComparatorOp_le_elim___redArg(v_le_1592_);
lean_dec(v_le_1592_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim(lean_object* v_motive_1594_, uint8_t v_t_1595_, lean_object* v_h_1596_, lean_object* v_le_1597_){
_start:
{
lean_inc(v_le_1597_);
return v_le_1597_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___boxed(lean_object* v_motive_1598_, lean_object* v_t_1599_, lean_object* v_h_1600_, lean_object* v_le_1601_){
_start:
{
uint8_t v_t_boxed_1602_; lean_object* v_res_1603_; 
v_t_boxed_1602_ = lean_unbox(v_t_1599_);
v_res_1603_ = l_Lake_ComparatorOp_le_elim(v_motive_1598_, v_t_boxed_1602_, v_h_1600_, v_le_1601_);
lean_dec(v_le_1601_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg(lean_object* v_gt_1604_){
_start:
{
lean_inc(v_gt_1604_);
return v_gt_1604_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg___boxed(lean_object* v_gt_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lake_ComparatorOp_gt_elim___redArg(v_gt_1605_);
lean_dec(v_gt_1605_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim(lean_object* v_motive_1607_, uint8_t v_t_1608_, lean_object* v_h_1609_, lean_object* v_gt_1610_){
_start:
{
lean_inc(v_gt_1610_);
return v_gt_1610_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___boxed(lean_object* v_motive_1611_, lean_object* v_t_1612_, lean_object* v_h_1613_, lean_object* v_gt_1614_){
_start:
{
uint8_t v_t_boxed_1615_; lean_object* v_res_1616_; 
v_t_boxed_1615_ = lean_unbox(v_t_1612_);
v_res_1616_ = l_Lake_ComparatorOp_gt_elim(v_motive_1611_, v_t_boxed_1615_, v_h_1613_, v_gt_1614_);
lean_dec(v_gt_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg(lean_object* v_ge_1617_){
_start:
{
lean_inc(v_ge_1617_);
return v_ge_1617_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg___boxed(lean_object* v_ge_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lake_ComparatorOp_ge_elim___redArg(v_ge_1618_);
lean_dec(v_ge_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim(lean_object* v_motive_1620_, uint8_t v_t_1621_, lean_object* v_h_1622_, lean_object* v_ge_1623_){
_start:
{
lean_inc(v_ge_1623_);
return v_ge_1623_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___boxed(lean_object* v_motive_1624_, lean_object* v_t_1625_, lean_object* v_h_1626_, lean_object* v_ge_1627_){
_start:
{
uint8_t v_t_boxed_1628_; lean_object* v_res_1629_; 
v_t_boxed_1628_ = lean_unbox(v_t_1625_);
v_res_1629_ = l_Lake_ComparatorOp_ge_elim(v_motive_1624_, v_t_boxed_1628_, v_h_1626_, v_ge_1627_);
lean_dec(v_ge_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg(lean_object* v_eq_1630_){
_start:
{
lean_inc(v_eq_1630_);
return v_eq_1630_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg___boxed(lean_object* v_eq_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lake_ComparatorOp_eq_elim___redArg(v_eq_1631_);
lean_dec(v_eq_1631_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim(lean_object* v_motive_1633_, uint8_t v_t_1634_, lean_object* v_h_1635_, lean_object* v_eq_1636_){
_start:
{
lean_inc(v_eq_1636_);
return v_eq_1636_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___boxed(lean_object* v_motive_1637_, lean_object* v_t_1638_, lean_object* v_h_1639_, lean_object* v_eq_1640_){
_start:
{
uint8_t v_t_boxed_1641_; lean_object* v_res_1642_; 
v_t_boxed_1641_ = lean_unbox(v_t_1638_);
v_res_1642_ = l_Lake_ComparatorOp_eq_elim(v_motive_1637_, v_t_boxed_1641_, v_h_1639_, v_eq_1640_);
lean_dec(v_eq_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg(lean_object* v_ne_1643_){
_start:
{
lean_inc(v_ne_1643_);
return v_ne_1643_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg___boxed(lean_object* v_ne_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lake_ComparatorOp_ne_elim___redArg(v_ne_1644_);
lean_dec(v_ne_1644_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim(lean_object* v_motive_1646_, uint8_t v_t_1647_, lean_object* v_h_1648_, lean_object* v_ne_1649_){
_start:
{
lean_inc(v_ne_1649_);
return v_ne_1649_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___boxed(lean_object* v_motive_1650_, lean_object* v_t_1651_, lean_object* v_h_1652_, lean_object* v_ne_1653_){
_start:
{
uint8_t v_t_boxed_1654_; lean_object* v_res_1655_; 
v_t_boxed_1654_ = lean_unbox(v_t_1651_);
v_res_1655_ = l_Lake_ComparatorOp_ne_elim(v_motive_1650_, v_t_boxed_1654_, v_h_1652_, v_ne_1653_);
lean_dec(v_ne_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr(uint8_t v_x_1674_, lean_object* v_prec_1675_){
_start:
{
lean_object* v___y_1677_; lean_object* v___y_1684_; lean_object* v___y_1691_; lean_object* v___y_1698_; lean_object* v___y_1705_; lean_object* v___y_1712_; 
switch(v_x_1674_)
{
case 0:
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = lean_unsigned_to_nat(1024u);
v___x_1719_ = lean_nat_dec_le(v___x_1718_, v_prec_1675_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1677_ = v___x_1720_;
goto v___jp_1676_;
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1677_ = v___x_1721_;
goto v___jp_1676_;
}
}
case 1:
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = lean_unsigned_to_nat(1024u);
v___x_1723_ = lean_nat_dec_le(v___x_1722_, v_prec_1675_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1684_ = v___x_1724_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1684_ = v___x_1725_;
goto v___jp_1683_;
}
}
case 2:
{
lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = lean_unsigned_to_nat(1024u);
v___x_1727_ = lean_nat_dec_le(v___x_1726_, v_prec_1675_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1691_ = v___x_1728_;
goto v___jp_1690_;
}
else
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1691_ = v___x_1729_;
goto v___jp_1690_;
}
}
case 3:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = lean_unsigned_to_nat(1024u);
v___x_1731_ = lean_nat_dec_le(v___x_1730_, v_prec_1675_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1698_ = v___x_1732_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1698_ = v___x_1733_;
goto v___jp_1697_;
}
}
case 4:
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = lean_unsigned_to_nat(1024u);
v___x_1735_ = lean_nat_dec_le(v___x_1734_, v_prec_1675_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1705_ = v___x_1736_;
goto v___jp_1704_;
}
else
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1705_ = v___x_1737_;
goto v___jp_1704_;
}
}
default: 
{
lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = lean_unsigned_to_nat(1024u);
v___x_1739_ = lean_nat_dec_le(v___x_1738_, v_prec_1675_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1712_ = v___x_1740_;
goto v___jp_1711_;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1712_ = v___x_1741_;
goto v___jp_1711_;
}
}
}
v___jp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1678_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__1));
lean_inc(v___y_1677_);
v___x_1679_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___y_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = 0;
v___x_1681_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*1, v___x_1680_);
v___x_1682_ = l_Repr_addAppParen(v___x_1681_, v_prec_1675_);
return v___x_1682_;
}
v___jp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1685_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__3));
lean_inc(v___y_1684_);
v___x_1686_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___y_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = 0;
v___x_1688_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set_uint8(v___x_1688_, sizeof(void*)*1, v___x_1687_);
v___x_1689_ = l_Repr_addAppParen(v___x_1688_, v_prec_1675_);
return v___x_1689_;
}
v___jp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1692_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__5));
lean_inc(v___y_1691_);
v___x_1693_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___y_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = 0;
v___x_1695_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*1, v___x_1694_);
v___x_1696_ = l_Repr_addAppParen(v___x_1695_, v_prec_1675_);
return v___x_1696_;
}
v___jp_1697_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1699_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__7));
lean_inc(v___y_1698_);
v___x_1700_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___y_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = 0;
v___x_1702_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
lean_ctor_set_uint8(v___x_1702_, sizeof(void*)*1, v___x_1701_);
v___x_1703_ = l_Repr_addAppParen(v___x_1702_, v_prec_1675_);
return v___x_1703_;
}
v___jp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1706_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__9));
lean_inc(v___y_1705_);
v___x_1707_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___y_1705_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = 0;
v___x_1709_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*1, v___x_1708_);
v___x_1710_ = l_Repr_addAppParen(v___x_1709_, v_prec_1675_);
return v___x_1710_;
}
v___jp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1713_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__11));
lean_inc(v___y_1712_);
v___x_1714_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___y_1712_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = 0;
v___x_1716_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*1, v___x_1715_);
v___x_1717_ = l_Repr_addAppParen(v___x_1716_, v_prec_1675_);
return v___x_1717_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr___boxed(lean_object* v_x_1742_, lean_object* v_prec_1743_){
_start:
{
uint8_t v_x_329__boxed_1744_; lean_object* v_res_1745_; 
v_x_329__boxed_1744_ = lean_unbox(v_x_1742_);
v_res_1745_ = l_Lake_instReprComparatorOp_repr(v_x_329__boxed_1744_, v_prec_1743_);
lean_dec(v_prec_1743_);
return v_res_1745_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp_default(void){
_start:
{
uint8_t v___x_1748_; 
v___x_1748_ = 0;
return v___x_1748_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp(void){
_start:
{
uint8_t v___x_1749_; 
v___x_1749_ = 0;
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(lean_object* v_sym_1750_, uint8_t v_cmp_1751_, lean_object* v_t_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_box(v_cmp_1751_);
lean_inc_ref(v_sym_1750_);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_sym_1750_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Lean_Data_Trie_insert___redArg(v_t_1752_, v_sym_1750_, v___x_1754_);
lean_dec_ref(v_sym_1750_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0___boxed(lean_object* v_sym_1756_, lean_object* v_cmp_1757_, lean_object* v_t_1758_){
_start:
{
uint8_t v_cmp_boxed_1759_; lean_object* v_res_1760_; 
v_cmp_boxed_1759_ = lean_unbox(v_cmp_1757_);
v_res_1760_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v_sym_1756_, v_cmp_boxed_1759_, v_t_1758_);
return v_res_1760_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9(void){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Data_Trie_empty___redArg();
return v___x_1770_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10(void){
_start:
{
lean_object* v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1771_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9);
v___x_1772_ = 0;
v___x_1773_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
v___x_1774_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1773_, v___x_1772_, v___x_1771_);
return v___x_1774_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11(void){
_start:
{
lean_object* v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1775_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10);
v___x_1776_ = 1;
v___x_1777_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7));
v___x_1778_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1777_, v___x_1776_, v___x_1775_);
return v___x_1778_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12(void){
_start:
{
lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1779_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11);
v___x_1780_ = 1;
v___x_1781_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
v___x_1782_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1781_, v___x_1780_, v___x_1779_);
return v___x_1782_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13(void){
_start:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1783_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12);
v___x_1784_ = 2;
v___x_1785_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
v___x_1786_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1785_, v___x_1784_, v___x_1783_);
return v___x_1786_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14(void){
_start:
{
lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1787_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13);
v___x_1788_ = 3;
v___x_1789_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4));
v___x_1790_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1789_, v___x_1788_, v___x_1787_);
return v___x_1790_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15(void){
_start:
{
lean_object* v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1791_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14);
v___x_1792_ = 3;
v___x_1793_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
v___x_1794_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1793_, v___x_1792_, v___x_1791_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16(void){
_start:
{
lean_object* v___x_1795_; uint8_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1795_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15);
v___x_1796_ = 4;
v___x_1797_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
v___x_1798_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1797_, v___x_1796_, v___x_1795_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17(void){
_start:
{
lean_object* v___x_1799_; uint8_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1799_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16);
v___x_1800_ = 5;
v___x_1801_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1));
v___x_1802_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1801_, v___x_1800_, v___x_1799_);
return v___x_1802_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18(void){
_start:
{
lean_object* v___x_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1803_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17);
v___x_1804_ = 5;
v___x_1805_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
v___x_1806_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1805_, v___x_1804_, v___x_1803_);
return v___x_1806_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie(void){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(lean_object* v_s_1810_, lean_object* v_p_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie;
v___x_1813_ = lean_string_utf8_byte_size(v_s_1810_);
lean_inc(v_p_1811_);
v___x_1814_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_1810_, v___x_1812_, v_p_1811_, v___x_1813_);
if (lean_obj_tag(v___x_1814_) == 1)
{
lean_object* v_val_1815_; lean_object* v_fst_1816_; lean_object* v_snd_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1831_; 
v_val_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_val_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v_fst_1816_ = lean_ctor_get(v_val_1815_, 0);
v_snd_1817_ = lean_ctor_get(v_val_1815_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_val_1815_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1819_ = v_val_1815_;
v_isShared_1820_ = v_isSharedCheck_1831_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_snd_1817_);
lean_inc(v_fst_1816_);
lean_dec(v_val_1815_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1831_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v_p_x27_1822_; uint8_t v___x_1823_; 
v___x_1821_ = lean_string_utf8_byte_size(v_fst_1816_);
lean_dec(v_fst_1816_);
v_p_x27_1822_ = lean_nat_add(v_p_1811_, v___x_1821_);
v___x_1823_ = lean_string_is_valid_pos(v_s_1810_, v_p_x27_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
lean_dec(v_p_x27_1822_);
lean_dec(v_snd_1817_);
v___x_1824_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0));
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 1);
lean_ctor_set(v___x_1819_, 1, v_p_1811_);
lean_ctor_set(v___x_1819_, 0, v___x_1824_);
v___x_1826_ = v___x_1819_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_p_1811_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
else
{
lean_object* v___x_1829_; 
lean_dec(v_p_1811_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v_p_x27_1822_);
lean_ctor_set(v___x_1819_, 0, v_snd_1817_);
v___x_1829_ = v___x_1819_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_snd_1817_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_p_x27_1822_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_dec(v___x_1814_);
v___x_1832_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1));
v___x_1833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v_p_1811_);
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___boxed(lean_object* v_s_1834_, lean_object* v_p_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1834_, v_p_1835_);
lean_dec_ref(v_s_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f(lean_object* v_s_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1837_, v___x_1838_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v_a_1841_; lean_object* v___x_1842_; uint8_t v_decide_1843_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
v_a_1841_ = lean_ctor_get(v___x_1839_, 1);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1839_, 2);
v___x_1842_ = lean_string_utf8_byte_size(v_s_1837_);
v_decide_1843_ = lean_nat_dec_eq(v_a_1841_, v___x_1842_);
lean_dec(v_a_1841_);
if (v_decide_1843_ == 0)
{
lean_object* v___x_1844_; 
lean_dec(v_a_1840_);
v___x_1844_ = lean_box(0);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_a_1840_);
return v___x_1845_;
}
}
else
{
lean_object* v___x_1846_; 
lean_dec_ref_known(v___x_1839_, 2);
v___x_1846_ = lean_box(0);
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f___boxed(lean_object* v_s_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lake_ComparatorOp_ofString_x3f(v_s_1847_);
lean_dec_ref(v_s_1847_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString(uint8_t v_self_1849_){
_start:
{
switch(v_self_1849_)
{
case 0:
{
lean_object* v___x_1850_; 
v___x_1850_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
return v___x_1850_;
}
case 1:
{
lean_object* v___x_1851_; 
v___x_1851_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
return v___x_1851_;
}
case 2:
{
lean_object* v___x_1852_; 
v___x_1852_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
return v___x_1852_;
}
case 3:
{
lean_object* v___x_1853_; 
v___x_1853_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
return v___x_1853_;
}
case 4:
{
lean_object* v___x_1854_; 
v___x_1854_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
return v___x_1854_;
}
default: 
{
lean_object* v___x_1855_; 
v___x_1855_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
return v___x_1855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString___boxed(lean_object* v_self_1856_){
_start:
{
uint8_t v_self_boxed_1857_; lean_object* v_res_1858_; 
v_self_boxed_1857_ = lean_unbox(v_self_1856_);
v_res_1858_ = l_Lake_ComparatorOp_toString(v_self_boxed_1857_);
return v_res_1858_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_unsigned_to_nat(7u);
v___x_1871_ = lean_nat_to_int(v___x_1870_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_unsigned_to_nat(6u);
v___x_1876_ = lean_nat_to_int(v___x_1875_);
return v___x_1876_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_unsigned_to_nat(19u);
v___x_1881_ = lean_nat_to_int(v___x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___redArg(lean_object* v_x_1882_){
_start:
{
lean_object* v_ver_1883_; uint8_t v_op_1884_; uint8_t v_includeSuffixes_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_ver_1883_ = lean_ctor_get(v_x_1882_, 0);
lean_inc_ref(v_ver_1883_);
v_op_1884_ = lean_ctor_get_uint8(v_x_1882_, sizeof(void*)*1);
v_includeSuffixes_1885_ = lean_ctor_get_uint8(v_x_1882_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_1882_);
v___x_1886_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_1887_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__3));
v___x_1888_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__4, &l_Lake_instReprVerComparator_repr___redArg___closed__4_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__4);
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = l_Lake_instReprStdVer_repr___redArg(v_ver_1883_);
v___x_1891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1888_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = 0;
v___x_1893_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*1, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1887_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_1896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_box(1);
v___x_1898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__6));
v___x_1900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v___x_1886_);
v___x_1902_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__7, &l_Lake_instReprVerComparator_repr___redArg___closed__7_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__7);
v___x_1903_ = l_Lake_instReprComparatorOp_repr(v_op_1884_, v___x_1889_);
v___x_1904_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1902_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*1, v___x_1892_);
v___x_1906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1901_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1895_);
v___x_1908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___x_1897_);
v___x_1909_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__9));
v___x_1910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1886_);
v___x_1912_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__10, &l_Lake_instReprVerComparator_repr___redArg___closed__10_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__10);
v___x_1913_ = l_Bool_repr___redArg(v_includeSuffixes_1885_);
v___x_1914_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*1, v___x_1892_);
v___x_1916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1911_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_1918_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_1919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1916_);
v___x_1920_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_1921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1917_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set_uint8(v___x_1923_, sizeof(void*)*1, v___x_1892_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr(lean_object* v_x_1924_, lean_object* v_prec_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lake_instReprVerComparator_repr___redArg(v_x_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___boxed(lean_object* v_x_1927_, lean_object* v_prec_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lake_instReprVerComparator_repr(v_x_1927_, v_prec_1928_);
lean_dec(v_prec_1928_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(lean_object* v_s_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v___x_1945_; 
lean_inc(v_a_1944_);
v___x_1945_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1943_, v_a_1944_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_2012_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_a_1947_ = lean_ctor_get(v___x_1945_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1949_ = v___x_1945_;
v_isShared_1950_ = v_isSharedCheck_2012_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_2012_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; uint8_t v_decide_1952_; 
v___x_1951_ = lean_string_utf8_byte_size(v_s_1943_);
v_decide_1952_ = lean_nat_dec_eq(v_a_1947_, v___x_1951_);
if (v_decide_1952_ == 0)
{
lean_object* v___x_1953_; 
lean_del_object(v___x_1949_);
lean_dec(v_a_1944_);
lean_inc_ref(v_s_1943_);
v___x_1953_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_1943_, v_a_1947_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_a_1955_; lean_object* v___x_1956_; lean_object* v_a_1957_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
v_a_1955_ = lean_ctor_get(v___x_1953_, 1);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1953_, 2);
v___x_1956_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_1943_, v_a_1955_);
lean_dec_ref(v_s_1943_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
if (lean_obj_tag(v_a_1957_) == 1)
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1979_; 
lean_inc_ref(v_a_1957_);
v_a_1958_ = lean_ctor_get(v___x_1956_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v___x_1956_, 0);
lean_dec(v_unused_1980_);
v___x_1960_ = v___x_1956_;
v_isShared_1961_ = v_isSharedCheck_1979_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1979_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_val_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_val_1962_ = lean_ctor_get(v_a_1957_, 0);
lean_inc(v_val_1962_);
lean_dec_ref_known(v_a_1957_, 1);
v___x_1963_ = lean_string_utf8_byte_size(v_val_1962_);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_nat_dec_eq(v___x_1963_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; lean_object* v___x_1970_; 
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_a_1954_);
lean_ctor_set(v___x_1966_, 1, v_val_1962_);
v___x_1967_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
v___x_1968_ = lean_unbox(v_a_1946_);
lean_dec(v_a_1946_);
lean_ctor_set_uint8(v___x_1967_, sizeof(void*)*1, v___x_1968_);
lean_ctor_set_uint8(v___x_1967_, sizeof(void*)*1 + 1, v___x_1965_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1967_);
v___x_1970_ = v___x_1960_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_a_1958_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; lean_object* v___x_1977_; 
lean_dec(v_val_1962_);
v___x_1972_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_a_1954_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
v___x_1975_ = lean_unbox(v_a_1946_);
lean_dec(v_a_1946_);
lean_ctor_set_uint8(v___x_1974_, sizeof(void*)*1, v___x_1975_);
lean_ctor_set_uint8(v___x_1974_, sizeof(void*)*1 + 1, v___x_1965_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1974_);
v___x_1977_ = v___x_1960_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_a_1958_);
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
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1992_; 
v_a_1981_ = lean_ctor_get(v___x_1956_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v___x_1956_, 0);
lean_dec(v_unused_1993_);
v___x_1983_ = v___x_1956_;
v_isShared_1984_ = v_isSharedCheck_1992_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1956_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1992_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1990_; 
v___x_1985_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_a_1954_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
v___x_1988_ = lean_unbox(v_a_1946_);
lean_dec(v_a_1946_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*1, v___x_1988_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*1 + 1, v_decide_1952_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1987_);
v___x_1990_ = v___x_1983_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_a_1981_);
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
lean_object* v_a_1994_; lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec(v_a_1946_);
lean_dec_ref(v_s_1943_);
v_a_1994_ = lean_ctor_get(v___x_1953_, 0);
v_a_1995_ = lean_ctor_get(v___x_1953_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1953_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_inc(v_a_1994_);
lean_dec(v___x_1953_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1994_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
lean_dec(v_a_1946_);
v___x_2003_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0));
v___x_2004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2004_, 0, v_s_1943_);
lean_ctor_set(v___x_2004_, 1, v_a_1944_);
lean_ctor_set(v___x_2004_, 2, v___x_1951_);
v___x_2005_ = l_String_Slice_toString(v___x_2004_);
lean_dec_ref_known(v___x_2004_, 3);
v___x_2006_ = lean_string_append(v___x_2003_, v___x_2005_);
lean_dec_ref(v___x_2005_);
v___x_2007_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1));
v___x_2008_ = lean_string_append(v___x_2006_, v___x_2007_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set_tag(v___x_1949_, 1);
lean_ctor_set(v___x_1949_, 0, v___x_2008_);
v___x_2010_ = v___x_1949_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_a_1947_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec(v_a_1944_);
lean_dec_ref(v_s_1943_);
v_a_2013_ = lean_ctor_get(v___x_1945_, 0);
v_a_2014_ = lean_ctor_get(v___x_1945_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_1945_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_inc(v_a_2013_);
lean_dec(v___x_1945_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2013_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_parse(lean_object* v_s_2022_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = lean_string_utf8_byte_size(v_s_2022_);
lean_inc_ref(v_s_2022_);
v___x_2025_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_2022_, v___x_2023_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v_a_2027_; uint8_t v_decide_2028_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
v_a_2027_ = lean_ctor_get(v___x_2025_, 1);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2025_, 2);
v_decide_2028_ = lean_nat_dec_eq(v_a_2027_, v___x_2024_);
if (v_decide_2028_ == 0)
{
lean_object* v_tail_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec(v_a_2026_);
v_tail_2029_ = lean_string_utf8_extract(v_s_2022_, v_a_2027_, v___x_2024_);
lean_dec(v_a_2027_);
lean_dec_ref(v_s_2022_);
v___x_2030_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_2031_ = lean_string_append(v___x_2030_, v_tail_2029_);
lean_dec_ref(v_tail_2029_);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; 
lean_dec(v_a_2027_);
lean_dec_ref(v_s_2022_);
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_a_2026_);
return v___x_2033_;
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2035_; 
lean_dec_ref(v_s_2022_);
v_a_2034_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2025_, 2);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_a_2034_);
return v___x_2035_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_VerComparator_test(lean_object* v_self_2036_, lean_object* v_ver_2037_){
_start:
{
lean_object* v_ver_2038_; uint8_t v_op_2039_; uint8_t v_includeSuffixes_2040_; lean_object* v_ver_2042_; 
v_ver_2038_ = lean_ctor_get(v_self_2036_, 0);
v_op_2039_ = lean_ctor_get_uint8(v_self_2036_, sizeof(void*)*1);
v_includeSuffixes_2040_ = lean_ctor_get_uint8(v_self_2036_, sizeof(void*)*1 + 1);
if (v_includeSuffixes_2040_ == 0)
{
lean_object* v_toSemVerCore_2059_; lean_object* v_specialDescr_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v_toSemVerCore_2059_ = lean_ctor_get(v_ver_2037_, 0);
v_specialDescr_2060_ = lean_ctor_get(v_ver_2037_, 1);
v___x_2061_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_2062_ = lean_string_dec_eq(v_specialDescr_2060_, v___x_2061_);
if (v___x_2062_ == 0)
{
lean_object* v_toSemVerCore_2063_; lean_object* v_specialDescr_2064_; uint8_t v___x_2065_; 
v_toSemVerCore_2063_ = lean_ctor_get(v_ver_2038_, 0);
v_specialDescr_2064_ = lean_ctor_get(v_ver_2038_, 1);
v___x_2065_ = lean_string_dec_eq(v_specialDescr_2064_, v___x_2061_);
if (v___x_2065_ == 0)
{
uint8_t v___x_2066_; 
v___x_2066_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_2063_, v_toSemVerCore_2059_);
if (v___x_2066_ == 0)
{
return v___x_2066_;
}
else
{
switch(v_op_2039_)
{
case 0:
{
uint8_t v___x_2067_; 
v___x_2067_ = lean_string_dec_lt(v_specialDescr_2060_, v_specialDescr_2064_);
return v___x_2067_;
}
case 1:
{
uint8_t v___x_2068_; 
v___x_2068_ = l_String_decLE(v_specialDescr_2060_, v_specialDescr_2064_);
return v___x_2068_;
}
case 2:
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_string_dec_lt(v_specialDescr_2064_, v_specialDescr_2060_);
return v___x_2069_;
}
case 3:
{
uint8_t v___x_2070_; 
v___x_2070_ = l_String_decLE(v_specialDescr_2064_, v_specialDescr_2060_);
return v___x_2070_;
}
case 4:
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_string_dec_eq(v_specialDescr_2060_, v_specialDescr_2064_);
return v___x_2071_;
}
default: 
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_string_dec_eq(v_specialDescr_2060_, v_specialDescr_2064_);
if (v___x_2072_ == 0)
{
return v___x_2066_;
}
else
{
return v___x_2065_;
}
}
}
}
}
else
{
return v_includeSuffixes_2040_;
}
}
else
{
v_ver_2042_ = v_ver_2037_;
goto v___jp_2041_;
}
}
else
{
v_ver_2042_ = v_ver_2037_;
goto v___jp_2041_;
}
v___jp_2041_:
{
switch(v_op_2039_)
{
case 0:
{
uint8_t v___x_2043_; 
v___x_2043_ = l_Lake_StdVer_compare(v_ver_2042_, v_ver_2038_);
if (v___x_2043_ == 0)
{
uint8_t v___x_2044_; 
v___x_2044_ = 1;
return v___x_2044_;
}
else
{
uint8_t v___x_2045_; 
v___x_2045_ = 0;
return v___x_2045_;
}
}
case 1:
{
uint8_t v___x_2046_; 
v___x_2046_ = l_Lake_StdVer_compare(v_ver_2042_, v_ver_2038_);
if (v___x_2046_ == 2)
{
uint8_t v___x_2047_; 
v___x_2047_ = 0;
return v___x_2047_;
}
else
{
uint8_t v___x_2048_; 
v___x_2048_ = 1;
return v___x_2048_;
}
}
case 2:
{
uint8_t v___x_2049_; 
v___x_2049_ = l_Lake_StdVer_compare(v_ver_2038_, v_ver_2042_);
if (v___x_2049_ == 0)
{
uint8_t v___x_2050_; 
v___x_2050_ = 1;
return v___x_2050_;
}
else
{
uint8_t v___x_2051_; 
v___x_2051_ = 0;
return v___x_2051_;
}
}
case 3:
{
uint8_t v___x_2052_; 
v___x_2052_ = l_Lake_StdVer_compare(v_ver_2038_, v_ver_2042_);
if (v___x_2052_ == 2)
{
uint8_t v___x_2053_; 
v___x_2053_ = 0;
return v___x_2053_;
}
else
{
uint8_t v___x_2054_; 
v___x_2054_ = 1;
return v___x_2054_;
}
}
case 4:
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_2042_, v_ver_2038_);
return v___x_2055_;
}
default: 
{
uint8_t v___x_2056_; 
v___x_2056_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_2042_, v_ver_2038_);
if (v___x_2056_ == 0)
{
uint8_t v___x_2057_; 
v___x_2057_ = 1;
return v___x_2057_;
}
else
{
uint8_t v___x_2058_; 
v___x_2058_ = 0;
return v___x_2058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_test___boxed(lean_object* v_self_2073_, lean_object* v_ver_2074_){
_start:
{
uint8_t v_res_2075_; lean_object* v_r_2076_; 
v_res_2075_ = l_Lake_VerComparator_test(v_self_2073_, v_ver_2074_);
lean_dec_ref(v_ver_2074_);
lean_dec_ref(v_self_2073_);
v_r_2076_ = lean_box(v_res_2075_);
return v_r_2076_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_toString(lean_object* v_self_2077_){
_start:
{
lean_object* v_ver_2078_; uint8_t v_op_2079_; uint8_t v_includeSuffixes_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v_ver_2078_ = lean_ctor_get(v_self_2077_, 0);
lean_inc_ref(v_ver_2078_);
v_op_2079_ = lean_ctor_get_uint8(v_self_2077_, sizeof(void*)*1);
v_includeSuffixes_2080_ = lean_ctor_get_uint8(v_self_2077_, sizeof(void*)*1 + 1);
lean_dec_ref(v_self_2077_);
v___x_2081_ = l_Lake_ComparatorOp_toString(v_op_2079_);
v___x_2082_ = l_Lake_StdVer_toString(v_ver_2078_);
v___x_2083_ = lean_string_append(v___x_2081_, v___x_2082_);
lean_dec_ref(v___x_2082_);
if (v_includeSuffixes_2080_ == 0)
{
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_2085_ = lean_string_append(v___x_2083_, v___x_2084_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_2088_, lean_object* v_x_2089_, lean_object* v_x_2090_){
_start:
{
if (lean_obj_tag(v_x_2090_) == 0)
{
lean_dec(v_x_2088_);
return v_x_2089_;
}
else
{
lean_object* v_head_2091_; lean_object* v_tail_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2102_; 
v_head_2091_ = lean_ctor_get(v_x_2090_, 0);
v_tail_2092_ = lean_ctor_get(v_x_2090_, 1);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_x_2090_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2094_ = v_x_2090_;
v_isShared_2095_ = v_isSharedCheck_2102_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_tail_2092_);
lean_inc(v_head_2091_);
lean_dec(v_x_2090_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2102_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
lean_inc(v_x_2088_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set_tag(v___x_2094_, 5);
lean_ctor_set(v___x_2094_, 1, v_x_2088_);
lean_ctor_set(v___x_2094_, 0, v_x_2089_);
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_x_2089_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_x_2088_);
v___x_2097_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2091_);
v___x_2099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v_x_2089_ = v___x_2099_;
v_x_2090_ = v_tail_2092_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
if (lean_obj_tag(v_x_2105_) == 0)
{
lean_dec(v_x_2103_);
return v_x_2104_;
}
else
{
lean_object* v_head_2106_; lean_object* v_tail_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2117_; 
v_head_2106_ = lean_ctor_get(v_x_2105_, 0);
v_tail_2107_ = lean_ctor_get(v_x_2105_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_x_2105_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2109_ = v_x_2105_;
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_tail_2107_);
lean_inc(v_head_2106_);
lean_dec(v_x_2105_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
lean_inc(v_x_2103_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 5);
lean_ctor_set(v___x_2109_, 1, v_x_2103_);
lean_ctor_set(v___x_2109_, 0, v_x_2104_);
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_x_2104_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_x_2103_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2106_);
v___x_2114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_2103_, v___x_2114_, v_tail_2107_);
return v___x_2115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(lean_object* v_x_2118_, lean_object* v_x_2119_){
_start:
{
if (lean_obj_tag(v_x_2118_) == 0)
{
lean_object* v___x_2120_; 
lean_dec(v_x_2119_);
v___x_2120_ = lean_box(0);
return v___x_2120_;
}
else
{
lean_object* v_tail_2121_; 
v_tail_2121_ = lean_ctor_get(v_x_2118_, 1);
if (lean_obj_tag(v_tail_2121_) == 0)
{
lean_object* v_head_2122_; lean_object* v___x_2123_; 
lean_dec(v_x_2119_);
v_head_2122_ = lean_ctor_get(v_x_2118_, 0);
lean_inc(v_head_2122_);
lean_dec_ref_known(v_x_2118_, 2);
v___x_2123_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2122_);
return v___x_2123_;
}
else
{
lean_object* v_head_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_inc(v_tail_2121_);
v_head_2124_ = lean_ctor_get(v_x_2118_, 0);
lean_inc(v_head_2124_);
lean_dec_ref_known(v_x_2118_, 2);
v___x_2125_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2124_);
v___x_2126_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(v_x_2119_, v___x_2125_, v_tail_2121_);
return v___x_2126_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0));
v___x_2133_ = lean_string_length(v___x_2132_);
return v___x_2133_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3);
v___x_2135_ = lean_nat_to_int(v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(lean_object* v_xs_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2144_ = lean_array_get_size(v_xs_2143_);
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = lean_nat_dec_eq(v___x_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2147_ = lean_array_to_list(v_xs_2143_);
v___x_2148_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2149_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(v___x_2147_, v___x_2148_);
v___x_2150_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2151_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v___x_2149_);
v___x_2153_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2150_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = l_Std_Format_fill(v___x_2155_);
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; 
lean_dec_ref(v_xs_2143_);
v___x_2157_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2157_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(lean_object* v_x_2158_, lean_object* v_x_2159_, lean_object* v_x_2160_){
_start:
{
if (lean_obj_tag(v_x_2160_) == 0)
{
lean_dec(v_x_2158_);
return v_x_2159_;
}
else
{
lean_object* v_head_2161_; lean_object* v_tail_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2172_; 
v_head_2161_ = lean_ctor_get(v_x_2160_, 0);
v_tail_2162_ = lean_ctor_get(v_x_2160_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_x_2160_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2164_ = v_x_2160_;
v_isShared_2165_ = v_isSharedCheck_2172_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_tail_2162_);
lean_inc(v_head_2161_);
lean_dec(v_x_2160_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2172_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
lean_inc(v_x_2158_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set_tag(v___x_2164_, 5);
lean_ctor_set(v___x_2164_, 1, v_x_2158_);
lean_ctor_set(v___x_2164_, 0, v_x_2159_);
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_x_2159_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_x_2158_);
v___x_2167_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2161_);
v___x_2169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v_x_2159_ = v___x_2169_;
v_x_2160_ = v_tail_2162_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
if (lean_obj_tag(v_x_2173_) == 0)
{
lean_object* v___x_2175_; 
lean_dec(v_x_2174_);
v___x_2175_ = lean_box(0);
return v___x_2175_;
}
else
{
lean_object* v_tail_2176_; 
v_tail_2176_ = lean_ctor_get(v_x_2173_, 1);
if (lean_obj_tag(v_tail_2176_) == 0)
{
lean_object* v_head_2177_; lean_object* v___x_2178_; 
lean_dec(v_x_2174_);
v_head_2177_ = lean_ctor_get(v_x_2173_, 0);
lean_inc(v_head_2177_);
lean_dec_ref_known(v_x_2173_, 2);
v___x_2178_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2177_);
return v___x_2178_;
}
else
{
lean_object* v_head_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
lean_inc(v_tail_2176_);
v_head_2179_ = lean_ctor_get(v_x_2173_, 0);
lean_inc(v_head_2179_);
lean_dec_ref_known(v_x_2173_, 2);
v___x_2180_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2179_);
v___x_2181_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(v_x_2174_, v___x_2180_, v_tail_2176_);
return v___x_2181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(lean_object* v_xs_2182_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2183_ = lean_array_get_size(v_xs_2182_);
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = lean_nat_dec_eq(v___x_2183_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2186_ = lean_array_to_list(v_xs_2182_);
v___x_2187_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2188_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(v___x_2186_, v___x_2187_);
v___x_2189_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2190_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v___x_2188_);
v___x_2192_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2189_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = l_Std_Format_fill(v___x_2194_);
return v___x_2195_;
}
else
{
lean_object* v___x_2196_; 
lean_dec_ref(v_xs_2182_);
v___x_2196_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2196_;
}
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = lean_unsigned_to_nat(12u);
v___x_2207_ = lean_nat_to_int(v___x_2206_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_unsigned_to_nat(11u);
v___x_2212_ = lean_nat_to_int(v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object* v_x_2213_){
_start:
{
lean_object* v_toString_2214_; lean_object* v_clauses_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2249_; 
v_toString_2214_ = lean_ctor_get(v_x_2213_, 0);
v_clauses_2215_ = lean_ctor_get(v_x_2213_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_x_2213_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2217_ = v_x_2213_;
v_isShared_2218_ = v_isSharedCheck_2249_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_clauses_2215_);
lean_inc(v_toString_2214_);
lean_dec(v_x_2213_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2249_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2219_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_2220_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__3));
v___x_2221_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__4, &l_Lake_instReprVerRange_repr___redArg___closed__4_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__4);
v___x_2222_ = l_String_quote(v_toString_2214_);
v___x_2223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set_tag(v___x_2217_, 4);
lean_ctor_set(v___x_2217_, 1, v___x_2223_);
lean_ctor_set(v___x_2217_, 0, v___x_2221_);
v___x_2225_ = v___x_2217_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2226_ = 0;
v___x_2227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2227_, 0, v___x_2225_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*1, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2220_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_2230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = lean_box(1);
v___x_2232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2230_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__6));
v___x_2234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v___x_2219_);
v___x_2236_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__7, &l_Lake_instReprVerRange_repr___redArg___closed__7_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__7);
v___x_2237_ = l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(v_clauses_2215_);
v___x_2238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2236_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set_uint8(v___x_2239_, sizeof(void*)*1, v___x_2226_);
v___x_2240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2235_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_2242_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_2243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v___x_2240_);
v___x_2244_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_2245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2241_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*1, v___x_2226_);
return v___x_2247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr(lean_object* v_x_2250_, lean_object* v_prec_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lake_instReprVerRange_repr___redArg(v_x_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___boxed(lean_object* v_x_2253_, lean_object* v_prec_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lake_instReprVerRange_repr(v_x_2253_, v_prec_2254_);
lean_dec(v_prec_2254_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0(lean_object* v_self_2265_){
_start:
{
lean_object* v_toString_2266_; 
v_toString_2266_ = lean_ctor_get(v_self_2265_, 0);
lean_inc_ref(v_toString_2266_);
return v_toString_2266_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0___boxed(lean_object* v_self_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lake_VerRange_instToString___lam__0(v_self_2267_);
lean_dec_ref(v_self_2267_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(lean_object* v_as_2272_, size_t v_i_2273_, size_t v_stop_2274_, lean_object* v_b_2275_){
_start:
{
uint8_t v___x_2276_; 
v___x_2276_ = lean_usize_dec_eq(v_i_2273_, v_stop_2274_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; size_t v___x_2282_; size_t v___x_2283_; 
v___x_2277_ = lean_array_uget_borrowed(v_as_2272_, v_i_2273_);
v___x_2278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0));
v___x_2279_ = lean_string_append(v_b_2275_, v___x_2278_);
lean_inc(v___x_2277_);
v___x_2280_ = l_Lake_VerComparator_toString(v___x_2277_);
v___x_2281_ = lean_string_append(v___x_2279_, v___x_2280_);
lean_dec_ref(v___x_2280_);
v___x_2282_ = ((size_t)1ULL);
v___x_2283_ = lean_usize_add(v_i_2273_, v___x_2282_);
v_i_2273_ = v___x_2283_;
v_b_2275_ = v___x_2281_;
goto _start;
}
else
{
return v_b_2275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___boxed(lean_object* v_as_2285_, lean_object* v_i_2286_, lean_object* v_stop_2287_, lean_object* v_b_2288_){
_start:
{
size_t v_i_boxed_2289_; size_t v_stop_boxed_2290_; lean_object* v_res_2291_; 
v_i_boxed_2289_ = lean_unbox_usize(v_i_2286_);
lean_dec(v_i_2286_);
v_stop_boxed_2290_ = lean_unbox_usize(v_stop_2287_);
lean_dec(v_stop_2287_);
v_res_2291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_as_2285_, v_i_boxed_2289_, v_stop_boxed_2290_, v_b_2288_);
lean_dec_ref(v_as_2285_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(lean_object* v_ands_2293_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2294_ = lean_array_get_size(v_ands_2293_);
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = lean_nat_dec_eq(v___x_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2297_ = lean_array_fget_borrowed(v_ands_2293_, v___x_2295_);
lean_inc(v___x_2297_);
v___x_2298_ = l_Lake_VerComparator_toString(v___x_2297_);
v___x_2299_ = lean_unsigned_to_nat(1u);
v___x_2300_ = lean_nat_dec_lt(v___x_2299_, v___x_2294_);
if (v___x_2300_ == 0)
{
return v___x_2298_;
}
else
{
uint8_t v___x_2301_; 
v___x_2301_ = lean_nat_dec_le(v___x_2294_, v___x_2294_);
if (v___x_2301_ == 0)
{
if (v___x_2300_ == 0)
{
return v___x_2298_;
}
else
{
size_t v___x_2302_; size_t v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = ((size_t)1ULL);
v___x_2303_ = lean_usize_of_nat(v___x_2294_);
v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2293_, v___x_2302_, v___x_2303_, v___x_2298_);
return v___x_2304_;
}
}
else
{
size_t v___x_2305_; size_t v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = ((size_t)1ULL);
v___x_2306_ = lean_usize_of_nat(v___x_2294_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2293_, v___x_2305_, v___x_2306_, v___x_2298_);
return v___x_2307_;
}
}
}
else
{
lean_object* v___x_2308_; 
v___x_2308_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0));
return v___x_2308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___boxed(lean_object* v_ands_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v_ands_2309_);
lean_dec_ref(v_ands_2309_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(lean_object* v_as_2312_, size_t v_i_2313_, size_t v_stop_2314_, lean_object* v_b_2315_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = lean_usize_dec_eq(v_i_2313_, v_stop_2314_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; 
v___x_2317_ = lean_array_uget_borrowed(v_as_2312_, v_i_2313_);
v___x_2318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0));
v___x_2319_ = lean_string_append(v_b_2315_, v___x_2318_);
v___x_2320_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2317_);
v___x_2321_ = lean_string_append(v___x_2319_, v___x_2320_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = ((size_t)1ULL);
v___x_2323_ = lean_usize_add(v_i_2313_, v___x_2322_);
v_i_2313_ = v___x_2323_;
v_b_2315_ = v___x_2321_;
goto _start;
}
else
{
return v_b_2315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___boxed(lean_object* v_as_2325_, lean_object* v_i_2326_, lean_object* v_stop_2327_, lean_object* v_b_2328_){
_start:
{
size_t v_i_boxed_2329_; size_t v_stop_boxed_2330_; lean_object* v_res_2331_; 
v_i_boxed_2329_ = lean_unbox_usize(v_i_2326_);
lean_dec(v_i_2326_);
v_stop_boxed_2330_ = lean_unbox_usize(v_stop_2327_);
lean_dec(v_stop_2327_);
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_as_2325_, v_i_boxed_2329_, v_stop_boxed_2330_, v_b_2328_);
lean_dec_ref(v_as_2325_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(lean_object* v_ors_2332_){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2333_ = lean_array_get_size(v_ors_2332_);
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = lean_nat_dec_eq(v___x_2333_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2336_ = lean_array_fget_borrowed(v_ors_2332_, v___x_2334_);
v___x_2337_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2336_);
v___x_2338_ = lean_unsigned_to_nat(1u);
v___x_2339_ = lean_nat_dec_lt(v___x_2338_, v___x_2333_);
if (v___x_2339_ == 0)
{
return v___x_2337_;
}
else
{
uint8_t v___x_2340_; 
v___x_2340_ = lean_nat_dec_le(v___x_2333_, v___x_2333_);
if (v___x_2340_ == 0)
{
if (v___x_2339_ == 0)
{
return v___x_2337_;
}
else
{
size_t v___x_2341_; size_t v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = ((size_t)1ULL);
v___x_2342_ = lean_usize_of_nat(v___x_2333_);
v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2332_, v___x_2341_, v___x_2342_, v___x_2337_);
return v___x_2343_;
}
}
else
{
size_t v___x_2344_; size_t v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = ((size_t)1ULL);
v___x_2345_ = lean_usize_of_nat(v___x_2333_);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2332_, v___x_2344_, v___x_2345_, v___x_2337_);
return v___x_2346_;
}
}
}
else
{
lean_object* v___x_2347_; 
v___x_2347_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
return v___x_2347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs___boxed(lean_object* v_ors_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_ors_2348_);
lean_dec_ref(v_ors_2348_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_ofClauses(lean_object* v_clauses_2350_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_clauses_2350_);
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set(v___x_2352_, 1, v_clauses_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_appendRange(lean_object* v_ands_2353_, lean_object* v_minVer_2354_, lean_object* v_maxVer_2355_, lean_object* v_specialDescr_2356_){
_start:
{
lean_object* v_minVer_2357_; lean_object* v___x_2358_; lean_object* v_maxVer_2359_; uint8_t v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_minVer_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2357_, 0, v_minVer_2354_);
lean_ctor_set(v_minVer_2357_, 1, v_specialDescr_2356_);
v___x_2358_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2359_, 0, v_maxVer_2355_);
lean_ctor_set(v_maxVer_2359_, 1, v___x_2358_);
v___x_2360_ = 3;
v___x_2361_ = 0;
v___x_2362_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2362_, 0, v_minVer_2357_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*1, v___x_2360_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*1 + 1, v___x_2361_);
v___x_2363_ = lean_array_push(v_ands_2353_, v___x_2362_);
v___x_2364_ = 0;
v___x_2365_ = 1;
v___x_2366_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2366_, 0, v_maxVer_2359_);
lean_ctor_set_uint8(v___x_2366_, sizeof(void*)*1, v___x_2364_);
lean_ctor_set_uint8(v___x_2366_, sizeof(void*)*1 + 1, v___x_2365_);
v___x_2367_ = lean_array_push(v___x_2363_, v___x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(lean_object* v_s_2370_, lean_object* v_ands_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_a_2376_; lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2548_; 
v___x_2373_ = lean_unsigned_to_nat(0u);
v___x_2374_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2372_);
lean_inc_ref(v_s_2370_);
v___x_2375_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2370_, v___x_2374_, v_a_2372_, v_a_2372_);
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_a_2377_ = lean_ctor_get(v___x_2375_, 1);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2379_ = v___x_2375_;
v_isShared_2380_ = v_isSharedCheck_2548_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2548_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; 
v___x_2381_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2370_, v_a_2377_);
lean_dec_ref(v_s_2370_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2538_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_a_2383_ = lean_ctor_get(v___x_2381_, 1);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2385_ = v___x_2381_;
v_isShared_2386_ = v_isSharedCheck_2538_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2538_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2387_ = lean_array_get_size(v_a_2376_);
v___x_2388_ = lean_unsigned_to_nat(1u);
v___x_2389_ = lean_nat_dec_eq(v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = lean_unsigned_to_nat(2u);
v___x_2391_ = lean_nat_dec_eq(v___x_2387_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = lean_unsigned_to_nat(3u);
v___x_2393_ = lean_nat_dec_eq(v___x_2387_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
lean_dec(v_a_2382_);
lean_del_object(v___x_2379_);
lean_dec(v_a_2376_);
lean_dec_ref(v_ands_2371_);
v___x_2394_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0));
v___x_2395_ = l_Nat_reprFast(v___x_2387_);
v___x_2396_ = lean_string_append(v___x_2394_, v___x_2395_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2398_ = lean_string_append(v___x_2396_, v___x_2397_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 1);
lean_ctor_set(v___x_2385_, 0, v___x_2398_);
v___x_2400_ = v___x_2385_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_a_2383_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_array_fget_borrowed(v_a_2376_, v___x_2373_);
v___x_2403_ = l_String_Slice_toNat_x3f(v___x_2402_);
if (lean_obj_tag(v___x_2403_) == 1)
{
lean_object* v_val_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_val_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_val_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = lean_array_fget_borrowed(v_a_2376_, v___x_2388_);
v___x_2406_ = l_String_Slice_toNat_x3f(v___x_2405_);
if (lean_obj_tag(v___x_2406_) == 1)
{
lean_object* v_val_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_val_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_val_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2408_ = lean_array_fget(v_a_2376_, v___x_2390_);
lean_dec(v_a_2376_);
v___x_2409_ = l_String_Slice_toNat_x3f(v___x_2408_);
if (lean_obj_tag(v___x_2409_) == 1)
{
lean_object* v_val_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v_minVer_2415_; 
lean_dec(v___x_2408_);
v_val_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_val_2410_);
lean_dec_ref_known(v___x_2409_, 1);
lean_inc(v_val_2407_);
lean_inc(v_val_2404_);
v___x_2411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2411_, 0, v_val_2404_);
lean_ctor_set(v___x_2411_, 1, v_val_2407_);
lean_ctor_set(v___x_2411_, 2, v_val_2410_);
v___x_2412_ = lean_nat_add(v_val_2407_, v___x_2388_);
lean_dec(v_val_2407_);
v___x_2413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2413_, 0, v_val_2404_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
lean_ctor_set(v___x_2413_, 2, v___x_2373_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v_a_2382_);
lean_ctor_set(v___x_2379_, 0, v___x_2411_);
v_minVer_2415_ = v___x_2379_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_a_2382_);
v_minVer_2415_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; lean_object* v_maxVer_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2425_; 
v___x_2416_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2417_, 0, v___x_2413_);
lean_ctor_set(v_maxVer_2417_, 1, v___x_2416_);
v___x_2418_ = 3;
v___x_2419_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2419_, 0, v_minVer_2415_);
lean_ctor_set_uint8(v___x_2419_, sizeof(void*)*1, v___x_2418_);
lean_ctor_set_uint8(v___x_2419_, sizeof(void*)*1 + 1, v___x_2391_);
v___x_2420_ = lean_array_push(v_ands_2371_, v___x_2419_);
v___x_2421_ = 0;
v___x_2422_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2422_, 0, v_maxVer_2417_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*1, v___x_2421_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*1 + 1, v___x_2393_);
v___x_2423_ = lean_array_push(v___x_2420_, v___x_2422_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2423_);
v___x_2425_ = v___x_2385_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_a_2383_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
else
{
lean_object* v_str_2428_; lean_object* v_startInclusive_2429_; lean_object* v_endExclusive_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_dec(v___x_2409_);
lean_dec(v_val_2407_);
lean_dec(v_val_2404_);
lean_dec(v_a_2382_);
lean_del_object(v___x_2379_);
lean_dec_ref(v_ands_2371_);
v_str_2428_ = lean_ctor_get(v___x_2408_, 0);
lean_inc_ref(v_str_2428_);
v_startInclusive_2429_ = lean_ctor_get(v___x_2408_, 1);
lean_inc(v_startInclusive_2429_);
v_endExclusive_2430_ = lean_ctor_get(v___x_2408_, 2);
lean_inc(v_endExclusive_2430_);
lean_dec(v___x_2408_);
v___x_2431_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2432_ = lean_string_utf8_extract_fast(v_str_2428_, v_startInclusive_2429_, v_endExclusive_2430_);
lean_dec(v_endExclusive_2430_);
lean_dec(v_startInclusive_2429_);
lean_dec_ref(v_str_2428_);
v___x_2433_ = lean_string_append(v___x_2431_, v___x_2432_);
lean_dec_ref(v___x_2432_);
v___x_2434_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2435_ = lean_string_append(v___x_2433_, v___x_2434_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 1);
lean_ctor_set(v___x_2385_, 0, v___x_2435_);
v___x_2437_ = v___x_2385_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_a_2383_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
else
{
lean_object* v_str_2439_; lean_object* v_startInclusive_2440_; lean_object* v_endExclusive_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
lean_inc(v___x_2405_);
lean_dec(v___x_2406_);
lean_dec(v_val_2404_);
lean_dec(v_a_2382_);
lean_del_object(v___x_2379_);
lean_dec(v_a_2376_);
lean_dec_ref(v_ands_2371_);
v_str_2439_ = lean_ctor_get(v___x_2405_, 0);
lean_inc_ref(v_str_2439_);
v_startInclusive_2440_ = lean_ctor_get(v___x_2405_, 1);
lean_inc(v_startInclusive_2440_);
v_endExclusive_2441_ = lean_ctor_get(v___x_2405_, 2);
lean_inc(v_endExclusive_2441_);
lean_dec(v___x_2405_);
v___x_2442_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2443_ = lean_string_utf8_extract_fast(v_str_2439_, v_startInclusive_2440_, v_endExclusive_2441_);
lean_dec(v_endExclusive_2441_);
lean_dec(v_startInclusive_2440_);
lean_dec_ref(v_str_2439_);
v___x_2444_ = lean_string_append(v___x_2442_, v___x_2443_);
lean_dec_ref(v___x_2443_);
v___x_2445_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2446_ = lean_string_append(v___x_2444_, v___x_2445_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 1);
lean_ctor_set(v___x_2385_, 0, v___x_2446_);
v___x_2448_ = v___x_2385_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_a_2383_);
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
lean_inc(v___x_2402_);
lean_dec(v___x_2403_);
lean_dec(v_a_2382_);
lean_del_object(v___x_2379_);
lean_dec(v_a_2376_);
lean_dec_ref(v_ands_2371_);
v_str_2450_ = lean_ctor_get(v___x_2402_, 0);
lean_inc_ref(v_str_2450_);
v_startInclusive_2451_ = lean_ctor_get(v___x_2402_, 1);
lean_inc(v_startInclusive_2451_);
v_endExclusive_2452_ = lean_ctor_get(v___x_2402_, 2);
lean_inc(v_endExclusive_2452_);
lean_dec(v___x_2402_);
v___x_2453_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2454_ = lean_string_utf8_extract_fast(v_str_2450_, v_startInclusive_2451_, v_endExclusive_2452_);
lean_dec(v_endExclusive_2452_);
lean_dec(v_startInclusive_2451_);
lean_dec_ref(v_str_2450_);
v___x_2455_ = lean_string_append(v___x_2453_, v___x_2454_);
lean_dec_ref(v___x_2454_);
v___x_2456_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2457_ = lean_string_append(v___x_2455_, v___x_2456_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 1);
lean_ctor_set(v___x_2385_, 0, v___x_2457_);
v___x_2459_ = v___x_2385_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_a_2383_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_array_fget_borrowed(v_a_2376_, v___x_2373_);
v___x_2462_ = l_String_Slice_toNat_x3f(v___x_2461_);
if (lean_obj_tag(v___x_2462_) == 1)
{
lean_object* v_val_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_val_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_val_2463_);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2464_ = lean_array_fget(v_a_2376_, v___x_2388_);
lean_dec(v_a_2376_);
v___x_2465_ = l_String_Slice_toNat_x3f(v___x_2464_);
if (lean_obj_tag(v___x_2465_) == 1)
{
lean_object* v_val_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_minVer_2471_; 
lean_dec(v___x_2464_);
v_val_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc_n(v_val_2466_, 2);
lean_dec_ref_known(v___x_2465_, 1);
lean_inc(v_val_2463_);
v___x_2467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2467_, 0, v_val_2463_);
lean_ctor_set(v___x_2467_, 1, v_val_2466_);
lean_ctor_set(v___x_2467_, 2, v___x_2373_);
v___x_2468_ = lean_nat_add(v_val_2466_, v___x_2388_);
lean_dec(v_val_2466_);
v___x_2469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2469_, 0, v_val_2463_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
lean_ctor_set(v___x_2469_, 2, v___x_2373_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v_a_2382_);
lean_ctor_set(v___x_2379_, 0, v___x_2467_);
v_minVer_2471_ = v___x_2379_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_a_2382_);
v_minVer_2471_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v_maxVer_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2472_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2473_, 0, v___x_2469_);
lean_ctor_set(v_maxVer_2473_, 1, v___x_2472_);
v___x_2474_ = 3;
v___x_2475_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2475_, 0, v_minVer_2471_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*1, v___x_2474_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*1 + 1, v___x_2389_);
v___x_2476_ = lean_array_push(v_ands_2371_, v___x_2475_);
v___x_2477_ = 0;
v___x_2478_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2478_, 0, v_maxVer_2473_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*1, v___x_2477_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*1 + 1, v___x_2391_);
v___x_2479_ = lean_array_push(v___x_2476_, v___x_2478_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2479_);
v___x_2481_ = v___x_2385_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_a_2383_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
else
{
lean_object* v_str_2484_; lean_object* v_startInclusive_2485_; lean_object* v_endExclusive_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_dec(v___x_2465_);
lean_dec(v_val_2463_);
lean_dec(v_a_2382_);
lean_del_object(v___x_2379_);
lean_dec_ref(v_ands_2371_);
v_str_2484_ = lean_ctor_get(v___x_2464_, 0);
lean_inc_ref(v_str_2484_);
v_startInclusive_2485_ = lean_ctor_get(v___x_2464_, 1);
lean_inc(v_startInclusive_2485_);
v_endExclusive_2486_ = lean_ctor_get(v___x_2464_, 2);
lean_inc(v_endExclusive_2486_);
lean_dec(v___x_2464_);
v___x_2487_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2488_ = lean_string_utf8_extract_fast(v_str_2484_, v_startInclusive_2485_, v_endExclusive_2486_);
lean_dec(v_endExclusive_2486_);
lean_dec(v_startInclusive_2485_);
lean_dec_ref(v_str_2484_);
v___x_2489_ = lean_string_append(v___x_2487_, v___x_2488_);
lean_dec_ref(v___x_2488_);
v___x_2490_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2491_ = lean_string_append(v___x_2489_, v___x_2490_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 1);
lean_ctor_set(v___x_2385_, 0, v___x_2491_);
v___x_2493_ = v___x_2385_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_a_2383_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
else
{
lean_object* v_str_2495_; lean_object* v_startInclusive_2496_; lean_object* v_endExclusive_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
lean_inc(v___x_2461_);
lean_dec(v___x_2462_);
lean_dec(v_a_2382_);
lean_del_object(v___x_2379_);
lean_dec(v_a_2376_);
lean_dec_ref(v_ands_2371_);
v_str_2495_ = lean_ctor_get(v___x_2461_, 0);
lean_inc_ref(v_str_2495_);
v_startInclusive_2496_ = lean_ctor_get(v___x_2461_, 1);
lean_inc(v_startInclusive_2496_);
v_endExclusive_2497_ = lean_ctor_get(v___x_2461_, 2);
lean_inc(v_endExclusive_2497_);
lean_dec(v___x_2461_);
v___x_2498_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2499_ = lean_string_utf8_extract_fast(v_str_2495_, v_startInclusive_2496_, v_endExclusive_2497_);
lean_dec(v_endExclusive_2497_);
lean_dec(v_startInclusive_2496_);
lean_dec_ref(v_str_2495_);
v___x_2500_ = lean_string_append(v___x_2498_, v___x_2499_);
lean_dec_ref(v___x_2499_);
v___x_2501_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2502_ = lean_string_append(v___x_2500_, v___x_2501_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 1);
lean_ctor_set(v___x_2385_, 0, v___x_2502_);
v___x_2504_ = v___x_2385_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_a_2383_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = lean_array_fget(v_a_2376_, v___x_2373_);
lean_dec(v_a_2376_);
v___x_2507_ = l_String_Slice_toNat_x3f(v___x_2506_);
if (lean_obj_tag(v___x_2507_) == 1)
{
lean_object* v_val_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v_minVer_2513_; 
lean_dec(v___x_2506_);
v_val_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc_n(v_val_2508_, 2);
lean_dec_ref_known(v___x_2507_, 1);
v___x_2509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2509_, 0, v_val_2508_);
lean_ctor_set(v___x_2509_, 1, v___x_2373_);
lean_ctor_set(v___x_2509_, 2, v___x_2373_);
v___x_2510_ = lean_nat_add(v_val_2508_, v___x_2388_);
lean_dec(v_val_2508_);
v___x_2511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2373_);
lean_ctor_set(v___x_2511_, 2, v___x_2373_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v_a_2382_);
lean_ctor_set(v___x_2379_, 0, v___x_2509_);
v_minVer_2513_ = v___x_2379_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_a_2382_);
v_minVer_2513_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2514_; lean_object* v_maxVer_2515_; uint8_t v___x_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2514_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2515_, 0, v___x_2511_);
lean_ctor_set(v_maxVer_2515_, 1, v___x_2514_);
v___x_2516_ = 3;
v___x_2517_ = 0;
v___x_2518_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2518_, 0, v_minVer_2513_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*1, v___x_2516_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*1 + 1, v___x_2517_);
v___x_2519_ = lean_array_push(v_ands_2371_, v___x_2518_);
v___x_2520_ = 0;
v___x_2521_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2521_, 0, v_maxVer_2515_);
lean_ctor_set_uint8(v___x_2521_, sizeof(void*)*1, v___x_2520_);
lean_ctor_set_uint8(v___x_2521_, sizeof(void*)*1 + 1, v___x_2389_);
v___x_2522_ = lean_array_push(v___x_2519_, v___x_2521_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2522_);
v___x_2524_ = v___x_2385_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_a_2383_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
else
{
lean_object* v_str_2527_; lean_object* v_startInclusive_2528_; lean_object* v_endExclusive_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
lean_dec(v___x_2507_);
lean_dec(v_a_2382_);
lean_del_object(v___x_2379_);
lean_dec_ref(v_ands_2371_);
v_str_2527_ = lean_ctor_get(v___x_2506_, 0);
lean_inc_ref(v_str_2527_);
v_startInclusive_2528_ = lean_ctor_get(v___x_2506_, 1);
lean_inc(v_startInclusive_2528_);
v_endExclusive_2529_ = lean_ctor_get(v___x_2506_, 2);
lean_inc(v_endExclusive_2529_);
lean_dec(v___x_2506_);
v___x_2530_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2531_ = lean_string_utf8_extract_fast(v_str_2527_, v_startInclusive_2528_, v_endExclusive_2529_);
lean_dec(v_endExclusive_2529_);
lean_dec(v_startInclusive_2528_);
lean_dec_ref(v_str_2527_);
v___x_2532_ = lean_string_append(v___x_2530_, v___x_2531_);
lean_dec_ref(v___x_2531_);
v___x_2533_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2534_ = lean_string_append(v___x_2532_, v___x_2533_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 1);
lean_ctor_set(v___x_2385_, 0, v___x_2534_);
v___x_2536_ = v___x_2385_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_a_2383_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_del_object(v___x_2379_);
lean_dec(v_a_2376_);
lean_dec_ref(v_ands_2371_);
v_a_2539_ = lean_ctor_get(v___x_2381_, 0);
v_a_2540_ = lean_ctor_get(v___x_2381_, 1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2381_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_inc(v_a_2539_);
lean_dec(v___x_2381_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2539_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(lean_object* v_s_2551_, lean_object* v_ands_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v_a_2557_; lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2780_; 
v___x_2554_ = lean_unsigned_to_nat(0u);
v___x_2555_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2553_);
lean_inc_ref(v_s_2551_);
v___x_2556_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2551_, v___x_2555_, v_a_2553_, v_a_2553_);
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_a_2558_ = lean_ctor_get(v___x_2556_, 1);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2560_ = v___x_2556_;
v_isShared_2561_ = v_isSharedCheck_2780_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2780_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; 
v___x_2562_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2551_, v_a_2558_);
lean_dec_ref(v_s_2551_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2770_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_a_2564_ = lean_ctor_get(v___x_2562_, 1);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2566_ = v___x_2562_;
v_isShared_2567_ = v_isSharedCheck_2770_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2770_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2568_ = lean_array_get_size(v_a_2557_);
v___x_2569_ = lean_unsigned_to_nat(1u);
v___x_2570_ = lean_nat_dec_eq(v___x_2568_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = lean_unsigned_to_nat(2u);
v___x_2572_ = lean_nat_dec_eq(v___x_2568_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2573_ = lean_unsigned_to_nat(3u);
v___x_2574_ = lean_nat_dec_eq(v___x_2568_, v___x_2573_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
lean_dec(v_a_2563_);
lean_del_object(v___x_2560_);
lean_dec(v_a_2557_);
lean_dec_ref(v_ands_2552_);
v___x_2575_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0));
v___x_2576_ = l_Nat_reprFast(v___x_2568_);
v___x_2577_ = lean_string_append(v___x_2575_, v___x_2576_);
lean_dec_ref(v___x_2576_);
v___x_2578_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2579_ = lean_string_append(v___x_2577_, v___x_2578_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 1);
lean_ctor_set(v___x_2566_, 0, v___x_2579_);
v___x_2581_ = v___x_2566_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_a_2564_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_array_fget_borrowed(v_a_2557_, v___x_2554_);
v___x_2584_ = l_String_Slice_toNat_x3f(v___x_2583_);
if (lean_obj_tag(v___x_2584_) == 1)
{
lean_object* v_val_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v_val_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2586_ = lean_array_fget_borrowed(v_a_2557_, v___x_2569_);
v___x_2587_ = l_String_Slice_toNat_x3f(v___x_2586_);
if (lean_obj_tag(v___x_2587_) == 1)
{
lean_object* v_val_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_val_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_val_2588_);
lean_dec_ref_known(v___x_2587_, 1);
v___x_2589_ = lean_array_fget(v_a_2557_, v___x_2571_);
lean_dec(v_a_2557_);
v___x_2590_ = l_String_Slice_toNat_x3f(v___x_2589_);
if (lean_obj_tag(v___x_2590_) == 1)
{
lean_object* v_val_2591_; uint8_t v___x_2592_; 
lean_dec(v___x_2589_);
v_val_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_val_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2592_ = lean_nat_dec_eq(v_val_2585_, v___x_2554_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v_minVer_2596_; lean_object* v___x_2597_; lean_object* v_maxVer_2598_; uint8_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
lean_del_object(v___x_2560_);
lean_inc(v_val_2585_);
v___x_2593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2593_, 0, v_val_2585_);
lean_ctor_set(v___x_2593_, 1, v_val_2588_);
lean_ctor_set(v___x_2593_, 2, v_val_2591_);
v___x_2594_ = lean_nat_add(v_val_2585_, v___x_2569_);
lean_dec(v_val_2585_);
v___x_2595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v___x_2554_);
lean_ctor_set(v___x_2595_, 2, v___x_2554_);
v_minVer_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2596_, 0, v___x_2593_);
lean_ctor_set(v_minVer_2596_, 1, v_a_2563_);
v___x_2597_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2598_, 0, v___x_2595_);
lean_ctor_set(v_maxVer_2598_, 1, v___x_2597_);
v___x_2599_ = 3;
v___x_2600_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2600_, 0, v_minVer_2596_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*1, v___x_2599_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*1 + 1, v___x_2592_);
v___x_2601_ = lean_array_push(v_ands_2552_, v___x_2600_);
v___x_2602_ = 0;
v___x_2603_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2603_, 0, v_maxVer_2598_);
lean_ctor_set_uint8(v___x_2603_, sizeof(void*)*1, v___x_2602_);
lean_ctor_set_uint8(v___x_2603_, sizeof(void*)*1 + 1, v___x_2574_);
v___x_2604_ = lean_array_push(v___x_2601_, v___x_2603_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2604_);
v___x_2606_ = v___x_2566_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_a_2564_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
else
{
uint8_t v___x_2608_; uint8_t v___y_2610_; 
v___x_2608_ = lean_nat_dec_eq(v_val_2588_, v___x_2554_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v_minVer_2629_; lean_object* v___x_2630_; lean_object* v_maxVer_2631_; uint8_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_del_object(v___x_2566_);
lean_inc(v_val_2588_);
lean_inc(v_val_2585_);
v___x_2626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2626_, 0, v_val_2585_);
lean_ctor_set(v___x_2626_, 1, v_val_2588_);
lean_ctor_set(v___x_2626_, 2, v_val_2591_);
v___x_2627_ = lean_nat_add(v_val_2588_, v___x_2569_);
lean_dec(v_val_2588_);
v___x_2628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2628_, 0, v_val_2585_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
lean_ctor_set(v___x_2628_, 2, v___x_2554_);
v_minVer_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2629_, 0, v___x_2626_);
lean_ctor_set(v_minVer_2629_, 1, v_a_2563_);
v___x_2630_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2631_, 0, v___x_2628_);
lean_ctor_set(v_maxVer_2631_, 1, v___x_2630_);
v___x_2632_ = 3;
v___x_2633_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2633_, 0, v_minVer_2629_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*1, v___x_2632_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*1 + 1, v___x_2608_);
v___x_2634_ = lean_array_push(v_ands_2552_, v___x_2633_);
v___x_2635_ = 0;
v___x_2636_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2636_, 0, v_maxVer_2631_);
lean_ctor_set_uint8(v___x_2636_, sizeof(void*)*1, v___x_2635_);
lean_ctor_set_uint8(v___x_2636_, sizeof(void*)*1 + 1, v___x_2592_);
v___x_2637_ = lean_array_push(v___x_2634_, v___x_2636_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 1, v_a_2564_);
lean_ctor_set(v___x_2560_, 0, v___x_2637_);
v___x_2639_ = v___x_2560_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_a_2564_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
else
{
uint8_t v___x_2641_; 
v___x_2641_ = lean_nat_dec_eq(v_val_2591_, v___x_2554_);
if (v___x_2641_ == 0)
{
lean_del_object(v___x_2560_);
v___y_2610_ = v___x_2572_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2642_ = lean_string_utf8_byte_size(v_a_2563_);
v___x_2643_ = lean_nat_dec_eq(v___x_2642_, v___x_2554_);
if (v___x_2643_ == 0)
{
lean_del_object(v___x_2560_);
v___y_2610_ = v___x_2643_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
lean_dec(v_val_2591_);
lean_dec(v_val_2588_);
lean_dec(v_val_2585_);
lean_del_object(v___x_2566_);
lean_dec(v_a_2563_);
lean_dec_ref(v_ands_2552_);
v___x_2644_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1));
if (v_isShared_2561_ == 0)
{
lean_ctor_set_tag(v___x_2560_, 1);
lean_ctor_set(v___x_2560_, 1, v_a_2564_);
lean_ctor_set(v___x_2560_, 0, v___x_2644_);
v___x_2646_ = v___x_2560_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_a_2564_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
v___jp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v_minVer_2614_; lean_object* v___x_2615_; lean_object* v_maxVer_2616_; uint8_t v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
lean_inc(v_val_2591_);
lean_inc(v_val_2588_);
lean_inc(v_val_2585_);
v___x_2611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2611_, 0, v_val_2585_);
lean_ctor_set(v___x_2611_, 1, v_val_2588_);
lean_ctor_set(v___x_2611_, 2, v_val_2591_);
v___x_2612_ = lean_nat_add(v_val_2591_, v___x_2569_);
lean_dec(v_val_2591_);
v___x_2613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2613_, 0, v_val_2585_);
lean_ctor_set(v___x_2613_, 1, v_val_2588_);
lean_ctor_set(v___x_2613_, 2, v___x_2612_);
v_minVer_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2614_, 0, v___x_2611_);
lean_ctor_set(v_minVer_2614_, 1, v_a_2563_);
v___x_2615_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2616_, 0, v___x_2613_);
lean_ctor_set(v_maxVer_2616_, 1, v___x_2615_);
v___x_2617_ = 3;
v___x_2618_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2618_, 0, v_minVer_2614_);
lean_ctor_set_uint8(v___x_2618_, sizeof(void*)*1, v___x_2617_);
lean_ctor_set_uint8(v___x_2618_, sizeof(void*)*1 + 1, v___y_2610_);
v___x_2619_ = lean_array_push(v_ands_2552_, v___x_2618_);
v___x_2620_ = 0;
v___x_2621_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2621_, 0, v_maxVer_2616_);
lean_ctor_set_uint8(v___x_2621_, sizeof(void*)*1, v___x_2620_);
lean_ctor_set_uint8(v___x_2621_, sizeof(void*)*1 + 1, v___x_2608_);
v___x_2622_ = lean_array_push(v___x_2619_, v___x_2621_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2622_);
v___x_2624_ = v___x_2566_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_a_2564_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_str_2648_; lean_object* v_startInclusive_2649_; lean_object* v_endExclusive_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2657_; 
lean_dec(v___x_2590_);
lean_dec(v_val_2588_);
lean_dec(v_val_2585_);
lean_dec(v_a_2563_);
lean_del_object(v___x_2560_);
lean_dec_ref(v_ands_2552_);
v_str_2648_ = lean_ctor_get(v___x_2589_, 0);
lean_inc_ref(v_str_2648_);
v_startInclusive_2649_ = lean_ctor_get(v___x_2589_, 1);
lean_inc(v_startInclusive_2649_);
v_endExclusive_2650_ = lean_ctor_get(v___x_2589_, 2);
lean_inc(v_endExclusive_2650_);
lean_dec(v___x_2589_);
v___x_2651_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2652_ = lean_string_utf8_extract_fast(v_str_2648_, v_startInclusive_2649_, v_endExclusive_2650_);
lean_dec(v_endExclusive_2650_);
lean_dec(v_startInclusive_2649_);
lean_dec_ref(v_str_2648_);
v___x_2653_ = lean_string_append(v___x_2651_, v___x_2652_);
lean_dec_ref(v___x_2652_);
v___x_2654_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2655_ = lean_string_append(v___x_2653_, v___x_2654_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 1);
lean_ctor_set(v___x_2566_, 0, v___x_2655_);
v___x_2657_ = v___x_2566_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_a_2564_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
else
{
lean_object* v_str_2659_; lean_object* v_startInclusive_2660_; lean_object* v_endExclusive_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
lean_inc(v___x_2586_);
lean_dec(v___x_2587_);
lean_dec(v_val_2585_);
lean_dec(v_a_2563_);
lean_del_object(v___x_2560_);
lean_dec(v_a_2557_);
lean_dec_ref(v_ands_2552_);
v_str_2659_ = lean_ctor_get(v___x_2586_, 0);
lean_inc_ref(v_str_2659_);
v_startInclusive_2660_ = lean_ctor_get(v___x_2586_, 1);
lean_inc(v_startInclusive_2660_);
v_endExclusive_2661_ = lean_ctor_get(v___x_2586_, 2);
lean_inc(v_endExclusive_2661_);
lean_dec(v___x_2586_);
v___x_2662_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2663_ = lean_string_utf8_extract_fast(v_str_2659_, v_startInclusive_2660_, v_endExclusive_2661_);
lean_dec(v_endExclusive_2661_);
lean_dec(v_startInclusive_2660_);
lean_dec_ref(v_str_2659_);
v___x_2664_ = lean_string_append(v___x_2662_, v___x_2663_);
lean_dec_ref(v___x_2663_);
v___x_2665_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2666_ = lean_string_append(v___x_2664_, v___x_2665_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 1);
lean_ctor_set(v___x_2566_, 0, v___x_2666_);
v___x_2668_ = v___x_2566_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_a_2564_);
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
lean_inc(v___x_2583_);
lean_dec(v___x_2584_);
lean_dec(v_a_2563_);
lean_del_object(v___x_2560_);
lean_dec(v_a_2557_);
lean_dec_ref(v_ands_2552_);
v_str_2670_ = lean_ctor_get(v___x_2583_, 0);
lean_inc_ref(v_str_2670_);
v_startInclusive_2671_ = lean_ctor_get(v___x_2583_, 1);
lean_inc(v_startInclusive_2671_);
v_endExclusive_2672_ = lean_ctor_get(v___x_2583_, 2);
lean_inc(v_endExclusive_2672_);
lean_dec(v___x_2583_);
v___x_2673_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2674_ = lean_string_utf8_extract_fast(v_str_2670_, v_startInclusive_2671_, v_endExclusive_2672_);
lean_dec(v_endExclusive_2672_);
lean_dec(v_startInclusive_2671_);
lean_dec_ref(v_str_2670_);
v___x_2675_ = lean_string_append(v___x_2673_, v___x_2674_);
lean_dec_ref(v___x_2674_);
v___x_2676_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2677_ = lean_string_append(v___x_2675_, v___x_2676_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 1);
lean_ctor_set(v___x_2566_, 0, v___x_2677_);
v___x_2679_ = v___x_2566_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_a_2564_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
lean_del_object(v___x_2560_);
v___x_2681_ = lean_array_fget_borrowed(v_a_2557_, v___x_2554_);
v___x_2682_ = l_String_Slice_toNat_x3f(v___x_2681_);
if (lean_obj_tag(v___x_2682_) == 1)
{
lean_object* v_val_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_val_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_val_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = lean_array_fget(v_a_2557_, v___x_2569_);
lean_dec(v_a_2557_);
v___x_2685_ = l_String_Slice_toNat_x3f(v___x_2684_);
if (lean_obj_tag(v___x_2685_) == 1)
{
lean_object* v_val_2686_; uint8_t v___x_2687_; 
lean_dec(v___x_2684_);
v_val_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_val_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = lean_nat_dec_eq(v_val_2683_, v___x_2554_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v_minVer_2691_; lean_object* v___x_2692_; lean_object* v_maxVer_2693_; uint8_t v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_inc(v_val_2683_);
v___x_2688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2688_, 0, v_val_2683_);
lean_ctor_set(v___x_2688_, 1, v_val_2686_);
lean_ctor_set(v___x_2688_, 2, v___x_2554_);
v___x_2689_ = lean_nat_add(v_val_2683_, v___x_2569_);
lean_dec(v_val_2683_);
v___x_2690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v___x_2554_);
lean_ctor_set(v___x_2690_, 2, v___x_2554_);
v_minVer_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2691_, 0, v___x_2688_);
lean_ctor_set(v_minVer_2691_, 1, v_a_2563_);
v___x_2692_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2693_, 0, v___x_2690_);
lean_ctor_set(v_maxVer_2693_, 1, v___x_2692_);
v___x_2694_ = 3;
v___x_2695_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2695_, 0, v_minVer_2691_);
lean_ctor_set_uint8(v___x_2695_, sizeof(void*)*1, v___x_2694_);
lean_ctor_set_uint8(v___x_2695_, sizeof(void*)*1 + 1, v___x_2687_);
v___x_2696_ = lean_array_push(v_ands_2552_, v___x_2695_);
v___x_2697_ = 0;
v___x_2698_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2698_, 0, v_maxVer_2693_);
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*1, v___x_2697_);
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*1 + 1, v___x_2572_);
v___x_2699_ = lean_array_push(v___x_2696_, v___x_2698_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2699_);
v___x_2701_ = v___x_2566_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_a_2564_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
else
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v_minVer_2706_; lean_object* v___x_2707_; lean_object* v_maxVer_2708_; uint8_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
lean_inc(v_val_2686_);
lean_inc(v_val_2683_);
v___x_2703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2703_, 0, v_val_2683_);
lean_ctor_set(v___x_2703_, 1, v_val_2686_);
lean_ctor_set(v___x_2703_, 2, v___x_2554_);
v___x_2704_ = lean_nat_add(v_val_2686_, v___x_2569_);
lean_dec(v_val_2686_);
v___x_2705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2705_, 0, v_val_2683_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
lean_ctor_set(v___x_2705_, 2, v___x_2554_);
v_minVer_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2706_, 0, v___x_2703_);
lean_ctor_set(v_minVer_2706_, 1, v_a_2563_);
v___x_2707_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2708_, 0, v___x_2705_);
lean_ctor_set(v_maxVer_2708_, 1, v___x_2707_);
v___x_2709_ = 3;
v___x_2710_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2710_, 0, v_minVer_2706_);
lean_ctor_set_uint8(v___x_2710_, sizeof(void*)*1, v___x_2709_);
lean_ctor_set_uint8(v___x_2710_, sizeof(void*)*1 + 1, v___x_2570_);
v___x_2711_ = lean_array_push(v_ands_2552_, v___x_2710_);
v___x_2712_ = 0;
v___x_2713_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2713_, 0, v_maxVer_2708_);
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*1, v___x_2712_);
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*1 + 1, v___x_2687_);
v___x_2714_ = lean_array_push(v___x_2711_, v___x_2713_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2714_);
v___x_2716_ = v___x_2566_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_a_2564_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
else
{
lean_object* v_str_2718_; lean_object* v_startInclusive_2719_; lean_object* v_endExclusive_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_dec(v___x_2685_);
lean_dec(v_val_2683_);
lean_dec(v_a_2563_);
lean_dec_ref(v_ands_2552_);
v_str_2718_ = lean_ctor_get(v___x_2684_, 0);
lean_inc_ref(v_str_2718_);
v_startInclusive_2719_ = lean_ctor_get(v___x_2684_, 1);
lean_inc(v_startInclusive_2719_);
v_endExclusive_2720_ = lean_ctor_get(v___x_2684_, 2);
lean_inc(v_endExclusive_2720_);
lean_dec(v___x_2684_);
v___x_2721_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2722_ = lean_string_utf8_extract_fast(v_str_2718_, v_startInclusive_2719_, v_endExclusive_2720_);
lean_dec(v_endExclusive_2720_);
lean_dec(v_startInclusive_2719_);
lean_dec_ref(v_str_2718_);
v___x_2723_ = lean_string_append(v___x_2721_, v___x_2722_);
lean_dec_ref(v___x_2722_);
v___x_2724_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2725_ = lean_string_append(v___x_2723_, v___x_2724_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 1);
lean_ctor_set(v___x_2566_, 0, v___x_2725_);
v___x_2727_ = v___x_2566_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_a_2564_);
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
lean_inc(v___x_2681_);
lean_dec(v___x_2682_);
lean_dec(v_a_2563_);
lean_dec(v_a_2557_);
lean_dec_ref(v_ands_2552_);
v_str_2729_ = lean_ctor_get(v___x_2681_, 0);
lean_inc_ref(v_str_2729_);
v_startInclusive_2730_ = lean_ctor_get(v___x_2681_, 1);
lean_inc(v_startInclusive_2730_);
v_endExclusive_2731_ = lean_ctor_get(v___x_2681_, 2);
lean_inc(v_endExclusive_2731_);
lean_dec(v___x_2681_);
v___x_2732_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2733_ = lean_string_utf8_extract_fast(v_str_2729_, v_startInclusive_2730_, v_endExclusive_2731_);
lean_dec(v_endExclusive_2731_);
lean_dec(v_startInclusive_2730_);
lean_dec_ref(v_str_2729_);
v___x_2734_ = lean_string_append(v___x_2732_, v___x_2733_);
lean_dec_ref(v___x_2733_);
v___x_2735_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2736_ = lean_string_append(v___x_2734_, v___x_2735_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 1);
lean_ctor_set(v___x_2566_, 0, v___x_2736_);
v___x_2738_ = v___x_2566_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_a_2564_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_del_object(v___x_2560_);
v___x_2740_ = lean_array_fget(v_a_2557_, v___x_2554_);
lean_dec(v_a_2557_);
v___x_2741_ = l_String_Slice_toNat_x3f(v___x_2740_);
if (lean_obj_tag(v___x_2741_) == 1)
{
lean_object* v_val_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v_minVer_2746_; lean_object* v___x_2747_; lean_object* v_maxVer_2748_; uint8_t v___x_2749_; uint8_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
lean_dec(v___x_2740_);
v_val_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc_n(v_val_2742_, 2);
lean_dec_ref_known(v___x_2741_, 1);
v___x_2743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2743_, 0, v_val_2742_);
lean_ctor_set(v___x_2743_, 1, v___x_2554_);
lean_ctor_set(v___x_2743_, 2, v___x_2554_);
v___x_2744_ = lean_nat_add(v_val_2742_, v___x_2569_);
lean_dec(v_val_2742_);
v___x_2745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
lean_ctor_set(v___x_2745_, 1, v___x_2554_);
lean_ctor_set(v___x_2745_, 2, v___x_2554_);
v_minVer_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2746_, 0, v___x_2743_);
lean_ctor_set(v_minVer_2746_, 1, v_a_2563_);
v___x_2747_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2748_, 0, v___x_2745_);
lean_ctor_set(v_maxVer_2748_, 1, v___x_2747_);
v___x_2749_ = 3;
v___x_2750_ = 0;
v___x_2751_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2751_, 0, v_minVer_2746_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*1, v___x_2749_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*1 + 1, v___x_2750_);
v___x_2752_ = lean_array_push(v_ands_2552_, v___x_2751_);
v___x_2753_ = 0;
v___x_2754_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2754_, 0, v_maxVer_2748_);
lean_ctor_set_uint8(v___x_2754_, sizeof(void*)*1, v___x_2753_);
lean_ctor_set_uint8(v___x_2754_, sizeof(void*)*1 + 1, v___x_2570_);
v___x_2755_ = lean_array_push(v___x_2752_, v___x_2754_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2755_);
v___x_2757_ = v___x_2566_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_a_2564_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
else
{
lean_object* v_str_2759_; lean_object* v_startInclusive_2760_; lean_object* v_endExclusive_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_dec(v___x_2741_);
lean_dec(v_a_2563_);
lean_dec_ref(v_ands_2552_);
v_str_2759_ = lean_ctor_get(v___x_2740_, 0);
lean_inc_ref(v_str_2759_);
v_startInclusive_2760_ = lean_ctor_get(v___x_2740_, 1);
lean_inc(v_startInclusive_2760_);
v_endExclusive_2761_ = lean_ctor_get(v___x_2740_, 2);
lean_inc(v_endExclusive_2761_);
lean_dec(v___x_2740_);
v___x_2762_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2763_ = lean_string_utf8_extract_fast(v_str_2759_, v_startInclusive_2760_, v_endExclusive_2761_);
lean_dec(v_endExclusive_2761_);
lean_dec(v_startInclusive_2760_);
lean_dec_ref(v_str_2759_);
v___x_2764_ = lean_string_append(v___x_2762_, v___x_2763_);
lean_dec_ref(v___x_2763_);
v___x_2765_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2766_ = lean_string_append(v___x_2764_, v___x_2765_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 1);
lean_ctor_set(v___x_2566_, 0, v___x_2766_);
v___x_2768_ = v___x_2566_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v_a_2564_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_del_object(v___x_2560_);
lean_dec(v_a_2557_);
lean_dec_ref(v_ands_2552_);
v_a_2771_ = lean_ctor_get(v___x_2562_, 0);
v_a_2772_ = lean_ctor_get(v___x_2562_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2562_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_inc(v_a_2771_);
lean_dec(v___x_2562_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2771_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(lean_object* v_s_2786_, lean_object* v_ands_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___y_2790_; lean_object* v___y_2794_; lean_object* v___y_2799_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v_a_2805_; lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2952_; 
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2788_);
lean_inc_ref(v_s_2786_);
v___x_2804_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2786_, v___x_2803_, v_a_2788_, v_a_2788_);
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_a_2806_ = lean_ctor_get(v___x_2804_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2808_ = v___x_2804_;
v_isShared_2809_ = v_isSharedCheck_2952_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2952_;
goto v_resetjp_2807_;
}
v___jp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0));
v___x_2792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v___y_2790_);
return v___x_2792_;
}
v___jp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2795_ = ((lean_object*)(l_Lake_VerComparator_wild));
v___x_2796_ = lean_array_push(v_ands_2787_, v___x_2795_);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set(v___x_2797_, 1, v___y_2794_);
return v___x_2797_;
}
v___jp_2798_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1));
v___x_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v___y_2799_);
return v___x_2801_;
}
v_resetjp_2807_:
{
lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___x_2925_; lean_object* v___y_2927_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v___x_2925_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__1));
v___x_2947_ = lean_array_get_size(v_a_2805_);
v___x_2948_ = lean_nat_dec_lt(v___x_2802_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_box(0);
v___y_2927_ = v___x_2949_;
goto v___jp_2926_;
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_array_fget_borrowed(v_a_2805_, v___x_2802_);
lean_inc(v___x_2950_);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
v___y_2927_ = v___x_2951_;
goto v___jp_2926_;
}
v___jp_2810_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2816_ = lean_unsigned_to_nat(3u);
v___x_2817_ = lean_array_get_size(v_a_2805_);
lean_dec(v_a_2805_);
v___x_2818_ = lean_nat_dec_lt(v___x_2816_, v___x_2817_);
if (v___x_2818_ == 0)
{
switch(lean_obj_tag(v___y_2811_))
{
case 2:
{
switch(lean_obj_tag(v___y_2812_))
{
case 2:
{
if (lean_obj_tag(v___y_2813_) == 1)
{
lean_object* v_n_2819_; lean_object* v_n_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v_minVer_2825_; lean_object* v_maxVer_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v_n_2819_ = lean_ctor_get(v___y_2811_, 0);
lean_inc_n(v_n_2819_, 2);
lean_dec_ref_known(v___y_2811_, 1);
v_n_2820_ = lean_ctor_get(v___y_2812_, 0);
lean_inc_n(v_n_2820_, 2);
lean_dec_ref_known(v___y_2812_, 1);
v___x_2821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2821_, 0, v_n_2819_);
lean_ctor_set(v___x_2821_, 1, v_n_2820_);
lean_ctor_set(v___x_2821_, 2, v___x_2802_);
v___x_2822_ = lean_nat_add(v_n_2820_, v___y_2814_);
lean_dec(v_n_2820_);
v___x_2823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2823_, 0, v_n_2819_);
lean_ctor_set(v___x_2823_, 1, v___x_2822_);
lean_ctor_set(v___x_2823_, 2, v___x_2802_);
v___x_2824_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2825_, 0, v___x_2821_);
lean_ctor_set(v_minVer_2825_, 1, v___x_2824_);
v_maxVer_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2826_, 0, v___x_2823_);
lean_ctor_set(v_maxVer_2826_, 1, v___x_2824_);
v___x_2827_ = 3;
v___x_2828_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2828_, 0, v_minVer_2825_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*1, v___x_2827_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*1 + 1, v___x_2818_);
v___x_2829_ = lean_array_push(v_ands_2787_, v___x_2828_);
v___x_2830_ = 0;
v___x_2831_ = 1;
v___x_2832_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2832_, 0, v_maxVer_2826_);
lean_ctor_set_uint8(v___x_2832_, sizeof(void*)*1, v___x_2830_);
lean_ctor_set_uint8(v___x_2832_, sizeof(void*)*1 + 1, v___x_2831_);
v___x_2833_ = lean_array_push(v___x_2829_, v___x_2832_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 1, v___y_2815_);
lean_ctor_set(v___x_2808_, 0, v___x_2833_);
v___x_2835_ = v___x_2808_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v___y_2815_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
else
{
lean_dec_ref_known(v___y_2812_, 1);
lean_dec_ref_known(v___y_2811_, 1);
lean_dec(v___y_2813_);
lean_del_object(v___x_2808_);
lean_dec_ref(v_ands_2787_);
v___y_2799_ = v___y_2815_;
goto v___jp_2798_;
}
}
case 1:
{
if (lean_obj_tag(v___y_2813_) == 2)
{
lean_dec_ref_known(v___y_2813_, 1);
lean_dec_ref_known(v___y_2811_, 1);
lean_del_object(v___x_2808_);
lean_dec_ref(v_ands_2787_);
v___y_2790_ = v___y_2815_;
goto v___jp_2789_;
}
else
{
lean_object* v_n_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v_minVer_2842_; lean_object* v_maxVer_2843_; uint8_t v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; uint8_t v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
lean_dec(v___y_2813_);
v_n_2837_ = lean_ctor_get(v___y_2811_, 0);
lean_inc_n(v_n_2837_, 2);
lean_dec_ref_known(v___y_2811_, 1);
v___x_2838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2838_, 0, v_n_2837_);
lean_ctor_set(v___x_2838_, 1, v___x_2802_);
lean_ctor_set(v___x_2838_, 2, v___x_2802_);
v___x_2839_ = lean_nat_add(v_n_2837_, v___y_2814_);
lean_dec(v_n_2837_);
v___x_2840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v___x_2802_);
lean_ctor_set(v___x_2840_, 2, v___x_2802_);
v___x_2841_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2842_, 0, v___x_2838_);
lean_ctor_set(v_minVer_2842_, 1, v___x_2841_);
v_maxVer_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2843_, 0, v___x_2840_);
lean_ctor_set(v_maxVer_2843_, 1, v___x_2841_);
v___x_2844_ = 3;
v___x_2845_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2845_, 0, v_minVer_2842_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*1, v___x_2844_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*1 + 1, v___x_2818_);
v___x_2846_ = lean_array_push(v_ands_2787_, v___x_2845_);
v___x_2847_ = 0;
v___x_2848_ = 1;
v___x_2849_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2849_, 0, v_maxVer_2843_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*1, v___x_2847_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*1 + 1, v___x_2848_);
v___x_2850_ = lean_array_push(v___x_2846_, v___x_2849_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 1, v___y_2815_);
lean_ctor_set(v___x_2808_, 0, v___x_2850_);
v___x_2852_ = v___x_2808_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___y_2815_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
default: 
{
lean_dec_ref_known(v___y_2811_, 1);
lean_dec(v___y_2813_);
lean_dec(v___y_2812_);
lean_del_object(v___x_2808_);
lean_dec_ref(v_ands_2787_);
v___y_2799_ = v___y_2815_;
goto v___jp_2798_;
}
}
}
case 1:
{
if (lean_obj_tag(v___y_2813_) == 2)
{
lean_dec_ref_known(v___y_2813_, 1);
lean_dec(v___y_2812_);
lean_del_object(v___x_2808_);
lean_dec_ref(v_ands_2787_);
v___y_2790_ = v___y_2815_;
goto v___jp_2789_;
}
else
{
lean_dec(v___y_2813_);
if (lean_obj_tag(v___y_2812_) == 2)
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
lean_dec_ref_known(v___y_2812_, 1);
lean_dec_ref(v_ands_2787_);
v___x_2854_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2));
if (v_isShared_2809_ == 0)
{
lean_ctor_set_tag(v___x_2808_, 1);
lean_ctor_set(v___x_2808_, 1, v___y_2815_);
lean_ctor_set(v___x_2808_, 0, v___x_2854_);
v___x_2856_ = v___x_2808_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v___y_2815_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
else
{
lean_dec(v___y_2812_);
lean_del_object(v___x_2808_);
v___y_2794_ = v___y_2815_;
goto v___jp_2793_;
}
}
}
default: 
{
lean_dec(v___y_2811_);
lean_del_object(v___x_2808_);
if (lean_obj_tag(v___y_2812_) == 1)
{
if (lean_obj_tag(v___y_2813_) == 2)
{
lean_dec_ref_known(v___y_2813_, 1);
lean_dec_ref(v_ands_2787_);
v___y_2790_ = v___y_2815_;
goto v___jp_2789_;
}
else
{
lean_dec(v___y_2813_);
v___y_2794_ = v___y_2815_;
goto v___jp_2793_;
}
}
else
{
lean_dec(v___y_2813_);
lean_dec(v___y_2812_);
v___y_2794_ = v___y_2815_;
goto v___jp_2793_;
}
}
}
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
lean_dec(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v_ands_2787_);
v___x_2858_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3));
v___x_2859_ = l_Nat_reprFast(v___x_2817_);
v___x_2860_ = lean_string_append(v___x_2858_, v___x_2859_);
lean_dec_ref(v___x_2859_);
v___x_2861_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2862_ = lean_string_append(v___x_2860_, v___x_2861_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set_tag(v___x_2808_, 1);
lean_ctor_set(v___x_2808_, 1, v___y_2815_);
lean_ctor_set(v___x_2808_, 0, v___x_2862_);
v___x_2864_ = v___x_2808_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v___y_2815_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
v___jp_2866_:
{
lean_object* v___x_2873_; 
v___x_2873_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2870_, v___y_2872_, v___y_2871_);
lean_dec(v___y_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2890_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_a_2875_ = lean_ctor_get(v___x_2873_, 1);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2877_ = v___x_2873_;
v_isShared_2878_ = v_isSharedCheck_2890_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2890_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2879_ = lean_string_utf8_byte_size(v_s_2786_);
v___x_2880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2880_, 0, v_s_2786_);
lean_ctor_set(v___x_2880_, 1, v___x_2802_);
lean_ctor_set(v___x_2880_, 2, v___x_2879_);
v___x_2881_ = l_String_Slice_Pos_get_x3f(v___x_2880_, v_a_2875_);
lean_dec_ref_known(v___x_2880_, 3);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_del_object(v___x_2877_);
v___y_2811_ = v___y_2867_;
v___y_2812_ = v___y_2868_;
v___y_2813_ = v_a_2874_;
v___y_2814_ = v___y_2869_;
v___y_2815_ = v_a_2875_;
goto v___jp_2810_;
}
else
{
lean_object* v_val_2882_; uint32_t v___x_2883_; uint32_t v___x_2884_; uint8_t v___x_2885_; 
v_val_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_val_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2883_ = 45;
v___x_2884_ = lean_unbox_uint32(v_val_2882_);
lean_dec(v_val_2882_);
v___x_2885_ = lean_uint32_dec_eq(v___x_2884_, v___x_2883_);
if (v___x_2885_ == 0)
{
lean_del_object(v___x_2877_);
v___y_2811_ = v___y_2867_;
v___y_2812_ = v___y_2868_;
v___y_2813_ = v_a_2874_;
v___y_2814_ = v___y_2869_;
v___y_2815_ = v_a_2875_;
goto v___jp_2810_;
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
lean_dec(v_a_2874_);
lean_dec(v___y_2868_);
lean_dec(v___y_2867_);
lean_del_object(v___x_2808_);
lean_dec(v_a_2805_);
lean_dec_ref(v_ands_2787_);
v___x_2886_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4));
if (v_isShared_2878_ == 0)
{
lean_ctor_set_tag(v___x_2877_, 1);
lean_ctor_set(v___x_2877_, 0, v___x_2886_);
v___x_2888_ = v___x_2877_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_a_2875_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v___y_2868_);
lean_dec(v___y_2867_);
lean_del_object(v___x_2808_);
lean_dec(v_a_2805_);
lean_dec_ref(v_ands_2787_);
lean_dec_ref(v_s_2786_);
v_a_2891_ = lean_ctor_get(v___x_2873_, 0);
v_a_2892_ = lean_ctor_get(v___x_2873_, 1);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2873_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_inc(v_a_2891_);
lean_dec(v___x_2873_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2891_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
v___jp_2900_:
{
lean_object* v___x_2906_; 
v___x_2906_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2904_, v___y_2905_, v___y_2902_);
lean_dec(v___y_2905_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v_a_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; uint8_t v___x_2912_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
v_a_2908_ = lean_ctor_get(v___x_2906_, 1);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2906_, 2);
v___x_2909_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__12));
v___x_2910_ = lean_unsigned_to_nat(2u);
v___x_2911_ = lean_array_get_size(v_a_2805_);
v___x_2912_ = lean_nat_dec_lt(v___x_2910_, v___x_2911_);
if (v___x_2912_ == 0)
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_box(0);
v___y_2867_ = v___y_2901_;
v___y_2868_ = v_a_2907_;
v___y_2869_ = v___y_2903_;
v___y_2870_ = v___x_2909_;
v___y_2871_ = v_a_2908_;
v___y_2872_ = v___x_2913_;
goto v___jp_2866_;
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = lean_array_fget_borrowed(v_a_2805_, v___x_2910_);
lean_inc(v___x_2914_);
v___x_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
v___y_2867_ = v___y_2901_;
v___y_2868_ = v_a_2907_;
v___y_2869_ = v___y_2903_;
v___y_2870_ = v___x_2909_;
v___y_2871_ = v_a_2908_;
v___y_2872_ = v___x_2915_;
goto v___jp_2866_;
}
}
else
{
lean_object* v_a_2916_; lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v___y_2901_);
lean_del_object(v___x_2808_);
lean_dec(v_a_2805_);
lean_dec_ref(v_ands_2787_);
lean_dec_ref(v_s_2786_);
v_a_2916_ = lean_ctor_get(v___x_2906_, 0);
v_a_2917_ = lean_ctor_get(v___x_2906_, 1);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2906_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_inc(v_a_2916_);
lean_dec(v___x_2906_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2916_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
v___jp_2926_:
{
lean_object* v___x_2928_; 
v___x_2928_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___x_2925_, v___y_2927_, v_a_2806_);
lean_dec(v___y_2927_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v_a_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
v_a_2930_ = lean_ctor_get(v___x_2928_, 1);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2928_, 2);
v___x_2931_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__10));
v___x_2932_ = lean_unsigned_to_nat(1u);
v___x_2933_ = lean_array_get_size(v_a_2805_);
v___x_2934_ = lean_nat_dec_lt(v___x_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_box(0);
v___y_2901_ = v_a_2929_;
v___y_2902_ = v_a_2930_;
v___y_2903_ = v___x_2932_;
v___y_2904_ = v___x_2931_;
v___y_2905_ = v___x_2935_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_array_fget_borrowed(v_a_2805_, v___x_2932_);
lean_inc(v___x_2936_);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
v___y_2901_ = v_a_2929_;
v___y_2902_ = v_a_2930_;
v___y_2903_ = v___x_2932_;
v___y_2904_ = v___x_2931_;
v___y_2905_ = v___x_2937_;
goto v___jp_2900_;
}
}
else
{
lean_object* v_a_2938_; lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_del_object(v___x_2808_);
lean_dec(v_a_2805_);
lean_dec_ref(v_ands_2787_);
lean_dec_ref(v_s_2786_);
v_a_2938_ = lean_ctor_get(v___x_2928_, 0);
v_a_2939_ = lean_ctor_get(v___x_2928_, 1);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2928_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_inc(v_a_2938_);
lean_dec(v___x_2928_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2938_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(lean_object* v_s_2959_, uint8_t v_needsRange_2960_, lean_object* v_ors_2961_, lean_object* v_ands_2962_, lean_object* v_p_2963_){
_start:
{
lean_object* v___x_2970_; uint8_t v_decide_2971_; 
v___x_2970_ = lean_string_utf8_byte_size(v_s_2959_);
v_decide_2971_ = lean_nat_dec_eq(v_p_2963_, v___x_2970_);
if (v_decide_2971_ == 0)
{
uint32_t v_c_2986_; uint8_t v___y_3082_; uint32_t v___x_3087_; uint8_t v___x_3088_; 
v_c_2986_ = lean_string_utf8_get_fast(v_s_2959_, v_p_2963_);
v___x_3087_ = 65;
v___x_3088_ = lean_uint32_dec_le(v___x_3087_, v_c_2986_);
if (v___x_3088_ == 0)
{
v___y_3082_ = v___x_3088_;
goto v___jp_3081_;
}
else
{
uint32_t v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = 90;
v___x_3090_ = lean_uint32_dec_le(v_c_2986_, v___x_3089_);
v___y_3082_ = v___x_3090_;
goto v___jp_3081_;
}
v___jp_2987_:
{
uint32_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2988_ = 42;
v___x_2989_ = lean_uint32_dec_eq(v_c_2986_, v___x_2988_);
if (v___x_2989_ == 0)
{
uint32_t v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = 94;
v___x_2991_ = lean_uint32_dec_eq(v_c_2986_, v___x_2990_);
if (v___x_2991_ == 0)
{
uint32_t v___x_2992_; uint8_t v___x_2993_; 
v___x_2992_ = 126;
v___x_2993_ = lean_uint32_dec_eq(v_c_2986_, v___x_2992_);
if (v___x_2993_ == 0)
{
uint32_t v___x_2994_; uint8_t v___x_2995_; 
v___x_2994_ = 32;
v___x_2995_ = lean_uint32_dec_eq(v_c_2986_, v___x_2994_);
if (v___x_2995_ == 0)
{
uint32_t v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = 9;
v___x_2997_ = lean_uint32_dec_eq(v_c_2986_, v___x_2996_);
if (v___x_2997_ == 0)
{
uint32_t v___x_2998_; uint8_t v___x_2999_; 
v___x_2998_ = 13;
v___x_2999_ = lean_uint32_dec_eq(v_c_2986_, v___x_2998_);
if (v___x_2999_ == 0)
{
uint32_t v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = 10;
v___x_3001_ = lean_uint32_dec_eq(v_c_2986_, v___x_3000_);
if (v___x_3001_ == 0)
{
uint8_t v___x_3002_; uint32_t v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = 1;
v___x_3003_ = 44;
v___x_3004_ = lean_uint32_dec_eq(v_c_2986_, v___x_3003_);
if (v___x_3004_ == 0)
{
uint32_t v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = 124;
v___x_3006_ = lean_uint32_dec_eq(v_c_2986_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
lean_inc_ref(v_s_2959_);
v___x_3007_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_2959_, v_p_2963_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v_a_3009_; lean_object* v___x_3010_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
v_a_3009_ = lean_ctor_get(v___x_3007_, 1);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3007_, 2);
v___x_3010_ = lean_array_push(v_ands_2962_, v_a_3008_);
v_needsRange_2960_ = v___x_3006_;
v_ands_2962_ = v___x_3010_;
v_p_2963_ = v_a_3009_;
goto _start;
}
else
{
lean_object* v_a_3012_; lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref(v_ands_2962_);
lean_dec_ref(v_ors_2961_);
lean_dec_ref(v_s_2959_);
v_a_3012_ = lean_ctor_get(v___x_3007_, 0);
v_a_3013_ = lean_ctor_get(v___x_3007_, 1);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_3007_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_inc(v_a_3012_);
lean_dec(v___x_3007_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3012_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
else
{
lean_object* v_p_3021_; uint8_t v_decide_3022_; 
v_p_3021_ = lean_string_utf8_next_fast(v_s_2959_, v_p_2963_);
lean_dec(v_p_2963_);
v_decide_3022_ = lean_nat_dec_eq(v_p_3021_, v___x_2970_);
if (v_decide_3022_ == 0)
{
uint32_t v___x_3023_; uint8_t v___x_3024_; 
v___x_3023_ = lean_string_utf8_get_fast(v_s_2959_, v_p_3021_);
v___x_3024_ = lean_uint32_dec_eq(v___x_3023_, v___x_3005_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_dec_ref(v_ands_2962_);
lean_dec_ref(v_ors_2961_);
lean_dec_ref(v_s_2959_);
v___x_3025_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v_p_3021_);
return v___x_3026_;
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; 
v___x_3027_ = lean_array_get_size(v_ands_2962_);
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = lean_nat_dec_eq(v___x_3027_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = lean_array_push(v_ors_2961_, v_ands_2962_);
v___x_3031_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2));
v___x_3032_ = lean_string_utf8_next_fast(v_s_2959_, v_p_3021_);
v_needsRange_2960_ = v___x_3002_;
v_ors_2961_ = v___x_3030_;
v_ands_2962_ = v___x_3031_;
v_p_2963_ = v___x_3032_;
goto _start;
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_dec_ref(v_ands_2962_);
lean_dec_ref(v_ors_2961_);
lean_dec_ref(v_s_2959_);
v___x_3034_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v_p_3021_);
return v___x_3035_;
}
}
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_dec_ref(v_ands_2962_);
lean_dec_ref(v_ors_2961_);
lean_dec_ref(v_s_2959_);
v___x_3036_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v_p_3021_);
return v___x_3037_;
}
}
}
else
{
if (v_needsRange_2960_ == 0)
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_string_utf8_next_fast(v_s_2959_, v_p_2963_);
lean_dec(v_p_2963_);
v_needsRange_2960_ = v___x_3002_;
v_p_2963_ = v___x_3038_;
goto _start;
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_dec_ref(v_ands_2962_);
lean_dec_ref(v_ors_2961_);
lean_dec_ref(v_s_2959_);
v___x_3040_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
lean_ctor_set(v___x_3041_, 1, v_p_2963_);
return v___x_3041_;
}
}
}
else
{
goto v___jp_2967_;
}
}
else
{
goto v___jp_2967_;
}
}
else
{
goto v___jp_2967_;
}
}
else
{
goto v___jp_2967_;
}
}
else
{
lean_object* v_p_3042_; uint8_t v_decide_3043_; 
v_p_3042_ = lean_string_utf8_next_fast(v_s_2959_, v_p_2963_);
lean_dec(v_p_2963_);
v_decide_3043_ = lean_nat_dec_eq(v_p_3042_, v___x_2970_);
if (v_decide_3043_ == 0)
{
lean_object* v___x_3044_; 
lean_inc_ref(v_s_2959_);
v___x_3044_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(v_s_2959_, v_ands_2962_, v_p_3042_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v_a_3046_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
v_a_3046_ = lean_ctor_get(v___x_3044_, 1);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3044_, 2);
v_needsRange_2960_ = v_decide_3043_;
v_ands_2962_ = v_a_3045_;
v_p_2963_ = v_a_3046_;
goto _start;
}
else
{
lean_object* v_a_3048_; lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v_ors_2961_);
lean_dec_ref(v_s_2959_);
v_a_3048_ = lean_ctor_get(v___x_3044_, 0);
v_a_3049_ = lean_ctor_get(v___x_3044_, 1);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3044_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_inc(v_a_3048_);
lean_dec(v___x_3044_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3048_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref(v_ands_2962_);
lean_dec_ref(v_ors_2961_);
lean_dec_ref(v_s_2959_);
v___x_3057_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3));
v___x_3058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v_p_3042_);
return v___x_3058_;
}
}
}
else
{
lean_object* v_p_3059_; uint8_t v_decide_3060_; 
v_p_3059_ = lean_string_utf8_next_fast(v_s_2959_, v_p_2963_);
lean_dec(v_p_2963_);
v_decide_3060_ = lean_nat_dec_eq(v_p_3059_, v___x_2970_);
if (v_decide_3060_ == 0)
{
lean_object* v___x_3061_; 
lean_inc_ref(v_s_2959_);
v___x_3061_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(v_s_2959_, v_ands_2962_, v_p_3059_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v_a_3063_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_a_3062_);
v_a_3063_ = lean_ctor_get(v___x_3061_, 1);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3061_, 2);
v_needsRange_2960_ = v_decide_3060_;
v_ands_2962_ = v_a_3062_;
v_p_2963_ = v_a_3063_;
goto _start;
}
else
{
lean_object* v_a_3065_; lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v_ors_2961_);
lean_dec_ref(v_s_2959_);
v_a_3065_ = lean_ctor_get(v___x_3061_, 0);
v_a_3066_ = lean_ctor_get(v___x_3061_, 1);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3061_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_inc(v_a_3065_);
lean_dec(v___x_3061_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3065_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec_ref(v_ands_2962_);
lean_dec_ref(v_ors_2961_);
lean_dec_ref(v_s_2959_);
v___x_3074_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4));
v___x_3075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v_p_3059_);
return v___x_3075_;
}
}
}
else
{
goto v___jp_2972_;
}
}
v___jp_3076_:
{
uint32_t v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = 48;
v___x_3078_ = lean_uint32_dec_le(v___x_3077_, v_c_2986_);
if (v___x_3078_ == 0)
{
goto v___jp_2987_;
}
else
{
uint32_t v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = 57;
v___x_3080_ = lean_uint32_dec_le(v_c_2986_, v___x_3079_);
if (v___x_3080_ == 0)
{
goto v___jp_2987_;
}
else
{
goto v___jp_2972_;
}
}
}
v___jp_3081_:
{
if (v___y_3082_ == 0)
{
uint32_t v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = 97;
v___x_3084_ = lean_uint32_dec_le(v___x_3083_, v_c_2986_);
if (v___x_3084_ == 0)
{
goto v___jp_3076_;
}
else
{
uint32_t v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = 122;
v___x_3086_ = lean_uint32_dec_le(v_c_2986_, v___x_3085_);
if (v___x_3086_ == 0)
{
goto v___jp_3076_;
}
else
{
goto v___jp_2972_;
}
}
}
else
{
goto v___jp_2972_;
}
}
}
else
{
lean_dec_ref(v_s_2959_);
if (v_needsRange_2960_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3091_ = lean_array_get_size(v_ands_2962_);
v___x_3092_ = lean_unsigned_to_nat(0u);
v___x_3093_ = lean_nat_dec_eq(v___x_3091_, v___x_3092_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = lean_array_push(v_ors_2961_, v_ands_2962_);
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v_p_2963_);
return v___x_3095_;
}
else
{
lean_dec_ref(v_ands_2962_);
lean_dec_ref(v_ors_2961_);
goto v___jp_2964_;
}
}
else
{
lean_dec_ref(v_ands_2962_);
lean_dec_ref(v_ors_2961_);
goto v___jp_2964_;
}
}
v___jp_2964_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_2966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v_p_2963_);
return v___x_2966_;
}
v___jp_2967_:
{
lean_object* v___x_2968_; 
v___x_2968_ = lean_string_utf8_next_fast(v_s_2959_, v_p_2963_);
lean_dec(v_p_2963_);
v_p_2963_ = v___x_2968_;
goto _start;
}
v___jp_2972_:
{
lean_object* v___x_2973_; 
lean_inc_ref(v_s_2959_);
v___x_2973_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(v_s_2959_, v_ands_2962_, v_p_2963_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v_a_2975_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
v_a_2975_ = lean_ctor_get(v___x_2973_, 1);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2973_, 2);
v_needsRange_2960_ = v_decide_2971_;
v_ands_2962_ = v_a_2974_;
v_p_2963_ = v_a_2975_;
goto _start;
}
else
{
lean_object* v_a_2977_; lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec_ref(v_ors_2961_);
lean_dec_ref(v_s_2959_);
v_a_2977_ = lean_ctor_get(v___x_2973_, 0);
v_a_2978_ = lean_ctor_get(v___x_2973_, 1);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2973_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_inc(v_a_2977_);
lean_dec(v___x_2973_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2977_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(lean_object* v_s_3096_, lean_object* v_needsRange_3097_, lean_object* v_ors_3098_, lean_object* v_ands_3099_, lean_object* v_p_3100_){
_start:
{
uint8_t v_needsRange_boxed_3101_; lean_object* v_res_3102_; 
v_needsRange_boxed_3101_ = lean_unbox(v_needsRange_3097_);
v_res_3102_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3096_, v_needsRange_boxed_3101_, v_ors_3098_, v_ands_3099_, v_p_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object* v_s_3105_, lean_object* v_a_3106_){
_start:
{
uint8_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = 1;
v___x_3108_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3105_);
v___x_3109_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3105_, v___x_3107_, v___x_3108_, v___x_3108_, v_a_3106_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3119_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_a_3111_ = lean_ctor_get(v___x_3109_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3113_ = v___x_3109_;
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3115_, 0, v_s_3105_);
lean_ctor_set(v___x_3115_, 1, v_a_3110_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_a_3111_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec_ref(v_s_3105_);
v_a_3120_ = lean_ctor_get(v___x_3109_, 0);
v_a_3121_ = lean_ctor_get(v___x_3109_, 1);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3109_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_inc(v_a_3120_);
lean_dec(v___x_3109_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3120_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_parse(lean_object* v_s_3129_){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3130_ = lean_unsigned_to_nat(0u);
v___x_3131_ = lean_string_utf8_byte_size(v_s_3129_);
v___x_3132_ = 1;
v___x_3133_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3129_);
v___x_3134_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3129_, v___x_3132_, v___x_3133_, v___x_3133_, v___x_3130_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3149_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
v_a_3136_ = lean_ctor_get(v___x_3134_, 1);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3138_ = v___x_3134_;
v_isShared_3139_ = v_isSharedCheck_3149_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_inc(v_a_3135_);
lean_dec(v___x_3134_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3149_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
uint8_t v_decide_3140_; 
v_decide_3140_ = lean_nat_dec_eq(v_a_3136_, v___x_3131_);
if (v_decide_3140_ == 0)
{
lean_object* v_tail_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
lean_del_object(v___x_3138_);
lean_dec(v_a_3135_);
v_tail_3141_ = lean_string_utf8_extract(v_s_3129_, v_a_3136_, v___x_3131_);
lean_dec(v_a_3136_);
lean_dec_ref(v_s_3129_);
v___x_3142_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_3143_ = lean_string_append(v___x_3142_, v_tail_3141_);
lean_dec_ref(v_tail_3141_);
v___x_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
return v___x_3144_;
}
else
{
lean_object* v___x_3146_; 
lean_dec(v_a_3136_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 1, v_a_3135_);
lean_ctor_set(v___x_3138_, 0, v_s_3129_);
v___x_3146_ = v___x_3138_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_s_3129_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_a_3135_);
v___x_3146_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3151_; 
lean_dec_ref(v_s_3129_);
v_a_3150_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3150_);
lean_dec_ref_known(v___x_3134_, 2);
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v_a_3150_);
return v___x_3151_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(lean_object* v_ver_3154_, lean_object* v_as_3155_, size_t v_i_3156_, size_t v_stop_3157_){
_start:
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_usize_dec_eq(v_i_3156_, v_stop_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3159_ = lean_array_uget_borrowed(v_as_3155_, v_i_3156_);
v___x_3160_ = l_Lake_VerComparator_test(v___x_3159_, v_ver_3154_);
if (v___x_3160_ == 0)
{
uint8_t v___x_3161_; 
v___x_3161_ = 1;
return v___x_3161_;
}
else
{
size_t v___x_3162_; size_t v___x_3163_; 
v___x_3162_ = ((size_t)1ULL);
v___x_3163_ = lean_usize_add(v_i_3156_, v___x_3162_);
v_i_3156_ = v___x_3163_;
goto _start;
}
}
else
{
uint8_t v___x_3165_; 
v___x_3165_ = 0;
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0___boxed(lean_object* v_ver_3166_, lean_object* v_as_3167_, lean_object* v_i_3168_, lean_object* v_stop_3169_){
_start:
{
size_t v_i_boxed_3170_; size_t v_stop_boxed_3171_; uint8_t v_res_3172_; lean_object* v_r_3173_; 
v_i_boxed_3170_ = lean_unbox_usize(v_i_3168_);
lean_dec(v_i_3168_);
v_stop_boxed_3171_ = lean_unbox_usize(v_stop_3169_);
lean_dec(v_stop_3169_);
v_res_3172_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3166_, v_as_3167_, v_i_boxed_3170_, v_stop_boxed_3171_);
lean_dec_ref(v_as_3167_);
lean_dec_ref(v_ver_3166_);
v_r_3173_ = lean_box(v_res_3172_);
return v_r_3173_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(lean_object* v_ver_3174_, lean_object* v_as_3175_, size_t v_i_3176_, size_t v_stop_3177_){
_start:
{
uint8_t v___x_3178_; 
v___x_3178_ = lean_usize_dec_eq(v_i_3176_, v_stop_3177_);
if (v___x_3178_ == 0)
{
uint8_t v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3179_ = 1;
v___x_3180_ = lean_array_uget_borrowed(v_as_3175_, v_i_3176_);
v___x_3181_ = lean_unsigned_to_nat(0u);
v___x_3182_ = lean_array_get_size(v___x_3180_);
v___x_3183_ = lean_nat_dec_lt(v___x_3181_, v___x_3182_);
if (v___x_3183_ == 0)
{
return v___x_3179_;
}
else
{
if (v___x_3183_ == 0)
{
return v___x_3179_;
}
else
{
size_t v___x_3184_; size_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3184_ = ((size_t)0ULL);
v___x_3185_ = lean_usize_of_nat(v___x_3182_);
v___x_3186_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3174_, v___x_3180_, v___x_3184_, v___x_3185_);
if (v___x_3186_ == 0)
{
return v___x_3179_;
}
else
{
size_t v___x_3187_; size_t v___x_3188_; 
v___x_3187_ = ((size_t)1ULL);
v___x_3188_ = lean_usize_add(v_i_3176_, v___x_3187_);
v_i_3176_ = v___x_3188_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3190_; 
v___x_3190_ = 0;
return v___x_3190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1___boxed(lean_object* v_ver_3191_, lean_object* v_as_3192_, lean_object* v_i_3193_, lean_object* v_stop_3194_){
_start:
{
size_t v_i_boxed_3195_; size_t v_stop_boxed_3196_; uint8_t v_res_3197_; lean_object* v_r_3198_; 
v_i_boxed_3195_ = lean_unbox_usize(v_i_3193_);
lean_dec(v_i_3193_);
v_stop_boxed_3196_ = lean_unbox_usize(v_stop_3194_);
lean_dec(v_stop_3194_);
v_res_3197_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3191_, v_as_3192_, v_i_boxed_3195_, v_stop_boxed_3196_);
lean_dec_ref(v_as_3192_);
lean_dec_ref(v_ver_3191_);
v_r_3198_ = lean_box(v_res_3197_);
return v_r_3198_;
}
}
LEAN_EXPORT uint8_t l_Lake_VerRange_test(lean_object* v_self_3199_, lean_object* v_ver_3200_){
_start:
{
lean_object* v_clauses_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v_clauses_3201_ = lean_ctor_get(v_self_3199_, 1);
v___x_3202_ = lean_unsigned_to_nat(0u);
v___x_3203_ = lean_array_get_size(v_clauses_3201_);
v___x_3204_ = lean_nat_dec_lt(v___x_3202_, v___x_3203_);
if (v___x_3204_ == 0)
{
return v___x_3204_;
}
else
{
if (v___x_3204_ == 0)
{
return v___x_3204_;
}
else
{
size_t v___x_3205_; size_t v___x_3206_; uint8_t v___x_3207_; 
v___x_3205_ = ((size_t)0ULL);
v___x_3206_ = lean_usize_of_nat(v___x_3203_);
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3200_, v_clauses_3201_, v___x_3205_, v___x_3206_);
return v___x_3207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_test___boxed(lean_object* v_self_3208_, lean_object* v_ver_3209_){
_start:
{
uint8_t v_res_3210_; lean_object* v_r_3211_; 
v_res_3210_ = l_Lake_VerRange_test(v_self_3208_, v_ver_3209_);
lean_dec_ref(v_ver_3209_);
lean_dec_ref(v_self_3208_);
v_r_3211_ = lean_box(v_res_3210_);
return v_r_3211_;
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
