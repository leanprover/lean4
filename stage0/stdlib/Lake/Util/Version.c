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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___impl___boxed(lean_object*);
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
uint32_t v_c_10_; uint32_t v___x_27_; uint8_t v___x_28_; 
v_c_10_ = lean_string_utf8_get_fast(v_s_1_, v_p_4_);
v___x_27_ = 46;
v___x_28_ = lean_uint32_dec_eq(v_c_10_, v___x_27_);
if (v___x_28_ == 0)
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 65;
v___x_30_ = lean_uint32_dec_le(v___x_29_, v_c_10_);
if (v___x_30_ == 0)
{
goto v___jp_22_;
}
else
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 90;
v___x_32_ = lean_uint32_dec_le(v_c_10_, v___x_31_);
if (v___x_32_ == 0)
{
goto v___jp_22_;
}
else
{
goto v___jp_5_;
}
}
}
else
{
lean_object* v_c_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
lean_inc(v_p_4_);
lean_inc_ref(v_s_1_);
v_c_33_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_33_, 0, v_s_1_);
lean_ctor_set(v_c_33_, 1, v_iniPos_3_);
lean_ctor_set(v_c_33_, 2, v_p_4_);
v___x_34_ = lean_array_push(v_cs_2_, v_c_33_);
v___x_35_ = lean_string_utf8_next_fast(v_s_1_, v_p_4_);
lean_dec(v_p_4_);
v_cs_2_ = v___x_34_;
v_iniPos_3_ = v___x_35_;
v_p_4_ = v___x_35_;
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
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 97;
v___x_24_ = lean_uint32_dec_le(v___x_23_, v_c_10_);
if (v___x_24_ == 0)
{
goto v___jp_17_;
}
else
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 122;
v___x_26_ = lean_uint32_dec_le(v_c_10_, v___x_25_);
if (v___x_26_ == 0)
{
goto v___jp_17_;
}
else
{
goto v___jp_5_;
}
}
}
}
else
{
lean_object* v_c_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
lean_inc(v_p_4_);
v_c_37_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_37_, 0, v_s_1_);
lean_ctor_set(v_c_37_, 1, v_iniPos_3_);
lean_ctor_set(v_c_37_, 2, v_p_4_);
v___x_38_ = lean_array_push(v_cs_2_, v_c_37_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v_p_4_);
return v___x_39_;
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents_go(lean_object* v_s_40_, lean_object* v_cs_41_, lean_object* v_iniPos_42_, lean_object* v_p_43_, lean_object* v_iniPos__le_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_40_, v_cs_41_, v_iniPos_42_, v_p_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents(lean_object* v_s_48_, lean_object* v_p_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_p_49_);
v___x_51_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_48_, v___x_50_, v_p_49_, v_p_49_);
return v___x_51_;
}
}
uint8_t l___private_Lake_Util_Version_0__Lake_isWildVer(lean_object* v_s_52_){
_start:
{
lean_object* v_str_53_; lean_object* v_startInclusive_54_; lean_object* v_endExclusive_55_; lean_object* v_p_56_; lean_object* v___x_57_; uint8_t v_decide_58_; 
v_str_53_ = lean_ctor_get(v_s_52_, 0);
v_startInclusive_54_ = lean_ctor_get(v_s_52_, 1);
v_endExclusive_55_ = lean_ctor_get(v_s_52_, 2);
v_p_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_nat_sub(v_endExclusive_55_, v_startInclusive_54_);
v_decide_58_ = lean_nat_dec_eq(v_p_56_, v___x_57_);
if (v_decide_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v_decide_61_; 
v___x_59_ = lean_string_utf8_next_fast(v_str_53_, v_startInclusive_54_);
v___x_60_ = lean_nat_sub(v___x_59_, v_startInclusive_54_);
v_decide_61_ = lean_nat_dec_eq(v___x_60_, v___x_57_);
lean_dec(v___x_57_);
lean_dec(v___x_60_);
if (v_decide_61_ == 0)
{
return v_decide_61_;
}
else
{
uint32_t v_c_62_; uint32_t v___x_63_; uint8_t v___x_64_; 
v_c_62_ = lean_string_utf8_get_fast(v_str_53_, v_startInclusive_54_);
v___x_63_ = 120;
v___x_64_ = lean_uint32_dec_eq(v_c_62_, v___x_63_);
if (v___x_64_ == 0)
{
uint32_t v___x_65_; uint8_t v___x_66_; 
v___x_65_ = 88;
v___x_66_ = lean_uint32_dec_eq(v_c_62_, v___x_65_);
if (v___x_66_ == 0)
{
uint32_t v___x_67_; uint8_t v___x_68_; 
v___x_67_ = 42;
v___x_68_ = lean_uint32_dec_eq(v_c_62_, v___x_67_);
return v___x_68_;
}
else
{
return v_decide_61_;
}
}
else
{
return v_decide_61_;
}
}
}
else
{
uint8_t v___x_69_; 
lean_dec(v___x_57_);
v___x_69_ = 0;
return v___x_69_;
}
}
}
LEAN_EXPORT void l___private_Lake_Util_Version_0__Lake_isWildVer_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_52_ = stack[0].m_obj;
uint8_t v_res_70_;
v_res_70_ = l___private_Lake_Util_Version_0__Lake_isWildVer(v_s_52_);
stack->m_num = v_res_70_;
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___impl(lean_object* v_x_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_tag_nat(v_x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___impl___boxed(lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___impl(v_x_125_);
lean_dec(v_x_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(lean_object* v_t_127_, lean_object* v_k_128_){
_start:
{
if (lean_obj_tag(v_t_127_) == 2)
{
lean_object* v_n_129_; lean_object* v___x_130_; 
v_n_129_ = lean_ctor_get(v_t_127_, 0);
lean_inc(v_n_129_);
lean_dec_ref_known(v_t_127_, 1);
v___x_130_ = lean_apply_1(v_k_128_, v_n_129_);
return v___x_130_;
}
else
{
lean_dec(v_t_127_);
return v_k_128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(lean_object* v_motive_131_, lean_object* v_ctorIdx_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_k_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_133_, v_k_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___boxed(lean_object* v_motive_137_, lean_object* v_ctorIdx_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_k_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(v_motive_137_, v_ctorIdx_138_, v_t_139_, v_h_140_, v_k_141_);
lean_dec(v_ctorIdx_138_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim___redArg(lean_object* v_t_143_, lean_object* v_none_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_143_, v_none_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim(lean_object* v_motive_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_none_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_147_, v_none_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim___redArg(lean_object* v_t_151_, lean_object* v_wild_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_151_, v_wild_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim(lean_object* v_motive_154_, lean_object* v_t_155_, lean_object* v_h_156_, lean_object* v_wild_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_155_, v_wild_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim___redArg(lean_object* v_t_159_, lean_object* v_nat_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_159_, v_nat_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim(lean_object* v_motive_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_nat_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_163_, v_nat_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(lean_object* v_what_168_, lean_object* v_s_x3f_169_, lean_object* v_a_170_){
_start:
{
if (lean_obj_tag(v_s_x3f_169_) == 1)
{
lean_object* v_val_171_; uint8_t v___x_172_; 
v_val_171_ = lean_ctor_get(v_s_x3f_169_, 0);
v___x_172_ = l___private_Lake_Util_Version_0__Lake_isWildVer(v_val_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = l_String_Slice_toNat_x3f(v_val_171_);
if (lean_obj_tag(v___x_173_) == 1)
{
lean_object* v_val_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_182_; 
v_val_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_182_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_val_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 2);
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_val_174_);
v___x_179_ = v_reuseFailAlloc_181_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_a_170_);
return v___x_180_;
}
}
}
else
{
lean_object* v_str_183_; lean_object* v_startInclusive_184_; lean_object* v_endExclusive_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v___x_173_);
v_str_183_ = lean_ctor_get(v_val_171_, 0);
v_startInclusive_184_ = lean_ctor_get(v_val_171_, 1);
v_endExclusive_185_ = lean_ctor_get(v_val_171_, 2);
v___x_186_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0));
v___x_187_ = lean_string_append(v___x_186_, v_what_168_);
v___x_188_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0));
v___x_189_ = lean_string_append(v___x_187_, v___x_188_);
v___x_190_ = lean_string_utf8_extract_fast(v_str_183_, v_startInclusive_184_, v_endExclusive_185_);
v___x_191_ = lean_string_append(v___x_189_, v___x_190_);
lean_dec_ref(v___x_190_);
v___x_192_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_193_ = lean_string_append(v___x_191_, v___x_192_);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v_a_170_);
return v___x_194_;
}
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_box(1);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_170_);
return v___x_196_;
}
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_box(0);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v_a_170_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___boxed(lean_object* v_what_199_, lean_object* v_s_x3f_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v_what_199_, v_s_x3f_200_, v_a_201_);
lean_dec(v_s_x3f_200_);
lean_dec_ref(v_what_199_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent(lean_object* v_00_u03c3_203_, lean_object* v_what_204_, lean_object* v_s_x3f_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v_what_204_, v_s_x3f_205_, v_a_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___boxed(lean_object* v_00_u03c3_208_, lean_object* v_what_209_, lean_object* v_s_x3f_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent(v_00_u03c3_208_, v_what_209_, v_s_x3f_210_, v_a_211_);
lean_dec(v_s_x3f_210_);
lean_dec_ref(v_what_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(lean_object* v_s_213_, lean_object* v_p_214_){
_start:
{
lean_object* v___x_215_; uint8_t v_decide_216_; 
v___x_215_ = lean_string_utf8_byte_size(v_s_213_);
v_decide_216_ = lean_nat_dec_eq(v_p_214_, v___x_215_);
if (v_decide_216_ == 0)
{
uint32_t v___x_217_; uint32_t v___x_218_; uint8_t v___x_219_; 
v___x_217_ = lean_string_utf8_get_fast(v_s_213_, v_p_214_);
v___x_218_ = 32;
v___x_219_ = lean_uint32_dec_eq(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
uint32_t v___x_220_; uint8_t v___x_221_; 
v___x_220_ = 9;
v___x_221_ = lean_uint32_dec_eq(v___x_217_, v___x_220_);
if (v___x_221_ == 0)
{
uint32_t v___x_222_; uint8_t v___x_223_; 
v___x_222_ = 13;
v___x_223_ = lean_uint32_dec_eq(v___x_217_, v___x_222_);
if (v___x_223_ == 0)
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 10;
v___x_225_ = lean_uint32_dec_eq(v___x_217_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
v___x_226_ = lean_string_utf8_next_fast(v_s_213_, v_p_214_);
lean_dec(v_p_214_);
v_p_214_ = v___x_226_;
goto _start;
}
else
{
return v_p_214_;
}
}
else
{
return v_p_214_;
}
}
else
{
return v_p_214_;
}
}
else
{
return v_p_214_;
}
}
else
{
return v_p_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace___boxed(lean_object* v_s_228_, lean_object* v_p_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(v_s_228_, v_p_229_);
lean_dec_ref(v_s_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(lean_object* v_s_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; uint8_t v_decide_234_; 
v___x_233_ = lean_string_utf8_byte_size(v_s_231_);
v_decide_234_ = lean_nat_dec_eq(v_a_232_, v___x_233_);
if (v_decide_234_ == 0)
{
uint32_t v___x_235_; uint32_t v___x_236_; uint8_t v___x_237_; 
v___x_235_ = lean_string_utf8_get_fast(v_s_231_, v_a_232_);
v___x_236_ = 45;
v___x_237_ = lean_uint32_dec_eq(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_box(0);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_a_232_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_240_ = lean_string_utf8_next_fast(v_s_231_, v_a_232_);
lean_dec(v_a_232_);
v___x_241_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(v_s_231_, v___x_240_);
v___x_242_ = lean_string_utf8_extract_fast(v_s_231_, v___x_240_, v___x_241_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_241_);
return v___x_244_;
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_box(0);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v_a_232_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f___boxed(lean_object* v_s_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_247_, v_a_248_);
lean_dec_ref(v_s_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(lean_object* v_s_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_254_; lean_object* v_a_255_; 
v___x_254_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_252_, v_a_253_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
if (lean_obj_tag(v_a_255_) == 1)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_271_; 
lean_inc_ref(v_a_255_);
v_a_256_ = lean_ctor_get(v___x_254_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v___x_254_, 0);
lean_dec(v_unused_272_);
v___x_258_ = v___x_254_;
v_isShared_259_ = v_isSharedCheck_271_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_254_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_271_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_val_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_val_260_ = lean_ctor_get(v_a_255_, 0);
lean_inc(v_val_260_);
lean_dec_ref_known(v_a_255_, 1);
v___x_261_ = lean_string_utf8_byte_size(v_val_260_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_nat_dec_eq(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_265_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v_val_260_);
v___x_265_ = v___x_258_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_val_260_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_a_256_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec(v_val_260_);
v___x_267_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0));
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 1);
lean_ctor_set(v___x_258_, 0, v___x_267_);
v___x_269_ = v___x_258_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_a_256_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
v_a_273_ = lean_ctor_get(v___x_254_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v___x_254_, 0);
lean_dec(v_unused_282_);
v___x_275_ = v___x_254_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_254_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_a_273_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___boxed(lean_object* v_s_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_283_, v_a_284_);
lean_dec_ref(v_s_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(lean_object* v_s_287_, lean_object* v_x_288_, lean_object* v_startPos_289_, lean_object* v_endPos_290_){
_start:
{
lean_object* v___x_291_; 
lean_inc_ref(v_s_287_);
v___x_291_ = lean_apply_2(v_x_288_, v_s_287_, v_startPos_289_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v_a_293_; uint8_t v_decide_294_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
v_a_293_ = lean_ctor_get(v___x_291_, 1);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_291_, 2);
v_decide_294_ = lean_nat_dec_eq(v_a_293_, v_endPos_290_);
if (v_decide_294_ == 0)
{
lean_object* v_tail_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_a_292_);
v_tail_295_ = lean_string_utf8_extract(v_s_287_, v_a_293_, v_endPos_290_);
lean_dec(v_a_293_);
lean_dec_ref(v_s_287_);
v___x_296_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_297_ = lean_string_append(v___x_296_, v_tail_295_);
lean_dec_ref(v_tail_295_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
lean_dec(v_a_293_);
lean_dec_ref(v_s_287_);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v_a_292_);
return v___x_299_;
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_301_; 
lean_dec_ref(v_s_287_);
v_a_300_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_291_, 2);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v_a_300_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___boxed(lean_object* v_s_302_, lean_object* v_x_303_, lean_object* v_startPos_304_, lean_object* v_endPos_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_302_, v_x_303_, v_startPos_304_, v_endPos_305_);
lean_dec(v_endPos_305_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object* v_00_u03b1_307_, lean_object* v_s_308_, lean_object* v_x_309_, lean_object* v_startPos_310_, lean_object* v_endPos_311_){
_start:
{
lean_object* v___x_312_; 
lean_inc_ref(v_s_308_);
v___x_312_ = lean_apply_2(v_x_309_, v_s_308_, v_startPos_310_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v_a_314_; uint8_t v_decide_315_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
v_a_314_ = lean_ctor_get(v___x_312_, 1);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_312_, 2);
v_decide_315_ = lean_nat_dec_eq(v_a_314_, v_endPos_311_);
if (v_decide_315_ == 0)
{
lean_object* v_tail_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_a_313_);
v_tail_316_ = lean_string_utf8_extract(v_s_308_, v_a_314_, v_endPos_311_);
lean_dec(v_a_314_);
lean_dec_ref(v_s_308_);
v___x_317_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_318_ = lean_string_append(v___x_317_, v_tail_316_);
lean_dec_ref(v_tail_316_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; 
lean_dec(v_a_314_);
lean_dec_ref(v_s_308_);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v_a_313_);
return v___x_320_;
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_322_; 
lean_dec_ref(v_s_308_);
v_a_321_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_312_, 2);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_a_321_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___boxed(lean_object* v_00_u03b1_323_, lean_object* v_s_324_, lean_object* v_x_325_, lean_object* v_startPos_326_, lean_object* v_endPos_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lake_Util_Version_0__Lake_runVerParse(v_00_u03b1_323_, v_s_324_, v_x_325_, v_startPos_326_, v_endPos_327_);
lean_dec(v_endPos_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprSemVerCore_repr_spec__0(lean_object* v_a_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_nat_to_int(v_a_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(9u);
v___x_349_ = lean_nat_to_int(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__0));
v___x_361_ = lean_string_length(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__15, &l_Lake_instReprSemVerCore_repr___redArg___closed__15_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15);
v___x_363_ = lean_nat_to_int(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___redArg(lean_object* v_x_368_){
_start:
{
lean_object* v_major_369_; lean_object* v_minor_370_; lean_object* v_patch_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_major_369_ = lean_ctor_get(v_x_368_, 0);
lean_inc(v_major_369_);
v_minor_370_ = lean_ctor_get(v_x_368_, 1);
lean_inc(v_minor_370_);
v_patch_371_ = lean_ctor_get(v_x_368_, 2);
lean_inc(v_patch_371_);
lean_dec_ref(v_x_368_);
v___x_372_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_373_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__6));
v___x_374_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__7, &l_Lake_instReprSemVerCore_repr___redArg___closed__7_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7);
v___x_375_ = l_Nat_reprFast(v_major_369_);
v___x_376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
v___x_377_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_374_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = 0;
v___x_379_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*1, v___x_378_);
v___x_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_373_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_box(1);
v___x_384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__11));
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_372_);
v___x_388_ = l_Nat_reprFast(v_minor_370_);
v___x_389_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
v___x_390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_374_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*1, v___x_378_);
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_387_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_381_);
v___x_394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_383_);
v___x_395_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__13));
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_372_);
v___x_398_ = l_Nat_reprFast(v_patch_371_);
v___x_399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
v___x_400_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_374_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*1, v___x_378_);
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_397_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_404_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_402_);
v___x_406_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_403_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*1, v___x_378_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr(lean_object* v_x_410_, lean_object* v_prec_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lake_instReprSemVerCore_repr___redArg(v_x_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___boxed(lean_object* v_x_413_, lean_object* v_prec_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lake_instReprSemVerCore_repr(v_x_413_, v_prec_414_);
lean_dec(v_prec_414_);
return v_res_415_;
}
}
uint8_t l_Lake_instDecidableEqSemVerCore_decEq(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_major_420_; lean_object* v_minor_421_; lean_object* v_patch_422_; lean_object* v_major_423_; lean_object* v_minor_424_; lean_object* v_patch_425_; uint8_t v___x_426_; 
v_major_420_ = lean_ctor_get(v_x_418_, 0);
v_minor_421_ = lean_ctor_get(v_x_418_, 1);
v_patch_422_ = lean_ctor_get(v_x_418_, 2);
v_major_423_ = lean_ctor_get(v_x_419_, 0);
v_minor_424_ = lean_ctor_get(v_x_419_, 1);
v_patch_425_ = lean_ctor_get(v_x_419_, 2);
v___x_426_ = lean_nat_dec_eq(v_major_420_, v_major_423_);
if (v___x_426_ == 0)
{
return v___x_426_;
}
else
{
uint8_t v___x_427_; 
v___x_427_ = lean_nat_dec_eq(v_minor_421_, v_minor_424_);
if (v___x_427_ == 0)
{
return v___x_427_;
}
else
{
uint8_t v___x_428_; 
v___x_428_ = lean_nat_dec_eq(v_patch_422_, v_patch_425_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT void l_Lake_instDecidableEqSemVerCore_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_418_ = stack[0].m_obj;
lean_object* v_x_419_ = stack[1].m_obj;
uint8_t v_res_429_;
v_res_429_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_418_, v_x_419_);
stack->m_num = v_res_429_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore_decEq___boxed(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_430_, v_x_431_);
lean_dec_ref(v_x_431_);
lean_dec_ref(v_x_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
uint8_t l_Lake_instDecidableEqSemVerCore(lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_434_, v_x_435_);
return v___x_436_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqSemVerCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_434_ = stack[0].m_obj;
lean_object* v_x_435_ = stack[1].m_obj;
uint8_t v_res_437_;
v_res_437_ = l_Lake_instDecidableEqSemVerCore(v_x_434_, v_x_435_);
stack->m_num = v_res_437_;
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
uint8_t l_Lake_instOrdSemVerCore_ord(lean_object* v_x_442_, lean_object* v_x_443_){
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
LEAN_EXPORT void l_Lake_instOrdSemVerCore_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_442_ = stack[0].m_obj;
lean_object* v_x_443_ = stack[1].m_obj;
uint8_t v_res_463_;
v_res_463_ = l_Lake_instOrdSemVerCore_ord(v_x_442_, v_x_443_);
stack->m_num = v_res_463_;
}
LEAN_EXPORT lean_object* l_Lake_instOrdSemVerCore_ord___boxed(lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lake_instOrdSemVerCore_ord(v_x_464_, v_x_465_);
lean_dec_ref(v_x_465_);
lean_dec_ref(v_x_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
static lean_object* _init_l_Lake_SemVerCore_instLT(void){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = lean_box(0);
return v___x_470_;
}
}
static lean_object* _init_l_Lake_SemVerCore_instLE(void){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_box(0);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0(lean_object* v_x_472_, lean_object* v_y_473_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = l_Lake_instOrdSemVerCore_ord(v_x_472_, v_y_473_);
if (v___x_474_ == 2)
{
lean_inc_ref(v_y_473_);
return v_y_473_;
}
else
{
lean_inc_ref(v_x_472_);
return v_x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0___boxed(lean_object* v_x_475_, lean_object* v_y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lake_SemVerCore_instMin___lam__0(v_x_475_, v_y_476_);
lean_dec_ref(v_y_476_);
lean_dec_ref(v_x_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0(lean_object* v_x_480_, lean_object* v_y_481_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = l_Lake_instOrdSemVerCore_ord(v_x_480_, v_y_481_);
if (v___x_482_ == 2)
{
lean_inc_ref(v_x_480_);
return v_x_480_;
}
else
{
lean_inc_ref(v_y_481_);
return v_y_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0___boxed(lean_object* v_x_483_, lean_object* v_y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lake_SemVerCore_instMax___lam__0(v_x_483_, v_y_484_);
lean_dec_ref(v_y_484_);
lean_dec_ref(v_x_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(lean_object* v_s_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_a_497_; lean_object* v_a_498_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_a_505_; lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_557_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_495_);
v___x_504_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_494_, v___x_503_, v_a_495_, v_a_495_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_a_506_ = lean_ctor_get(v___x_504_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_557_ == 0)
{
v___x_508_ = v___x_504_;
v_isShared_509_ = v_isSharedCheck_557_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_557_;
goto v_resetjp_507_;
}
v___jp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0));
v___x_500_ = lean_string_append(v___x_499_, v_a_497_);
lean_dec_ref(v_a_497_);
v___x_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v_a_498_);
return v___x_501_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_array_get_size(v_a_505_);
v___x_511_ = lean_unsigned_to_nat(3u);
v___x_512_ = lean_nat_dec_eq(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_del_object(v___x_508_);
lean_dec(v_a_505_);
v___x_513_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1));
v___x_514_ = l_Nat_reprFast(v___x_510_);
v___x_515_ = lean_string_append(v___x_513_, v___x_514_);
lean_dec_ref(v___x_514_);
v___x_516_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2));
v___x_517_ = lean_string_append(v___x_515_, v___x_516_);
v_a_497_ = v___x_517_;
v_a_498_ = v_a_506_;
goto v___jp_496_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_array_fget_borrowed(v_a_505_, v___x_502_);
v___x_519_ = l_String_Slice_toNat_x3f(v___x_518_);
if (lean_obj_tag(v___x_519_) == 1)
{
lean_object* v_val_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_val_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_val_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_array_fget_borrowed(v_a_505_, v___x_521_);
v___x_523_ = l_String_Slice_toNat_x3f(v___x_522_);
if (lean_obj_tag(v___x_523_) == 1)
{
lean_object* v_val_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_val_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = lean_array_fget(v_a_505_, v___x_525_);
lean_dec(v_a_505_);
v___x_527_ = l_String_Slice_toNat_x3f(v___x_526_);
if (lean_obj_tag(v___x_527_) == 1)
{
lean_object* v_val_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
lean_dec(v___x_526_);
v_val_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_val_528_);
lean_dec_ref_known(v___x_527_, 1);
v___x_529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_529_, 0, v_val_520_);
lean_ctor_set(v___x_529_, 1, v_val_524_);
lean_ctor_set(v___x_529_, 2, v_val_528_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_529_);
v___x_531_ = v___x_508_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_a_506_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
lean_object* v_str_533_; lean_object* v_startInclusive_534_; lean_object* v_endExclusive_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v___x_527_);
lean_dec(v_val_524_);
lean_dec(v_val_520_);
lean_del_object(v___x_508_);
v_str_533_ = lean_ctor_get(v___x_526_, 0);
lean_inc_ref(v_str_533_);
v_startInclusive_534_ = lean_ctor_get(v___x_526_, 1);
lean_inc(v_startInclusive_534_);
v_endExclusive_535_ = lean_ctor_get(v___x_526_, 2);
lean_inc(v_endExclusive_535_);
lean_dec(v___x_526_);
v___x_536_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_537_ = lean_string_utf8_extract_fast(v_str_533_, v_startInclusive_534_, v_endExclusive_535_);
lean_dec(v_endExclusive_535_);
lean_dec(v_startInclusive_534_);
lean_dec_ref(v_str_533_);
v___x_538_ = lean_string_append(v___x_536_, v___x_537_);
lean_dec_ref(v___x_537_);
v___x_539_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_540_ = lean_string_append(v___x_538_, v___x_539_);
v_a_497_ = v___x_540_;
v_a_498_ = v_a_506_;
goto v___jp_496_;
}
}
else
{
lean_object* v_str_541_; lean_object* v_startInclusive_542_; lean_object* v_endExclusive_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_inc(v___x_522_);
lean_dec(v___x_523_);
lean_dec(v_val_520_);
lean_del_object(v___x_508_);
lean_dec(v_a_505_);
v_str_541_ = lean_ctor_get(v___x_522_, 0);
lean_inc_ref(v_str_541_);
v_startInclusive_542_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_startInclusive_542_);
v_endExclusive_543_ = lean_ctor_get(v___x_522_, 2);
lean_inc(v_endExclusive_543_);
lean_dec(v___x_522_);
v___x_544_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_545_ = lean_string_utf8_extract_fast(v_str_541_, v_startInclusive_542_, v_endExclusive_543_);
lean_dec(v_endExclusive_543_);
lean_dec(v_startInclusive_542_);
lean_dec_ref(v_str_541_);
v___x_546_ = lean_string_append(v___x_544_, v___x_545_);
lean_dec_ref(v___x_545_);
v___x_547_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_548_ = lean_string_append(v___x_546_, v___x_547_);
v_a_497_ = v___x_548_;
v_a_498_ = v_a_506_;
goto v___jp_496_;
}
}
else
{
lean_object* v_str_549_; lean_object* v_startInclusive_550_; lean_object* v_endExclusive_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_inc(v___x_518_);
lean_dec(v___x_519_);
lean_del_object(v___x_508_);
lean_dec(v_a_505_);
v_str_549_ = lean_ctor_get(v___x_518_, 0);
lean_inc_ref(v_str_549_);
v_startInclusive_550_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_startInclusive_550_);
v_endExclusive_551_ = lean_ctor_get(v___x_518_, 2);
lean_inc(v_endExclusive_551_);
lean_dec(v___x_518_);
v___x_552_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_553_ = lean_string_utf8_extract_fast(v_str_549_, v_startInclusive_550_, v_endExclusive_551_);
lean_dec(v_endExclusive_551_);
lean_dec(v_startInclusive_550_);
lean_dec_ref(v_str_549_);
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_556_ = lean_string_append(v___x_554_, v___x_555_);
v_a_497_ = v___x_556_;
v_a_498_ = v_a_506_;
goto v___jp_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_parse(lean_object* v_s_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_string_utf8_byte_size(v_s_558_);
lean_inc_ref(v_s_558_);
v___x_561_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_558_, v___x_559_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v_a_563_; uint8_t v_decide_564_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
v_a_563_ = lean_ctor_get(v___x_561_, 1);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_561_, 2);
v_decide_564_ = lean_nat_dec_eq(v_a_563_, v___x_560_);
if (v_decide_564_ == 0)
{
lean_object* v_tail_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v_a_562_);
v_tail_565_ = lean_string_utf8_extract(v_s_558_, v_a_563_, v___x_560_);
lean_dec(v_a_563_);
lean_dec_ref(v_s_558_);
v___x_566_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_567_ = lean_string_append(v___x_566_, v_tail_565_);
lean_dec_ref(v_tail_565_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; 
lean_dec(v_a_563_);
lean_dec_ref(v_s_558_);
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v_a_562_);
return v___x_569_;
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_571_; 
lean_dec_ref(v_s_558_);
v_a_570_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_561_, 2);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v_a_570_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_toString(lean_object* v_ver_573_){
_start:
{
lean_object* v_major_574_; lean_object* v_minor_575_; lean_object* v_patch_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_major_574_ = lean_ctor_get(v_ver_573_, 0);
lean_inc(v_major_574_);
v_minor_575_ = lean_ctor_get(v_ver_573_, 1);
lean_inc(v_minor_575_);
v_patch_576_ = lean_ctor_get(v_ver_573_, 2);
lean_inc(v_patch_576_);
lean_dec_ref(v_ver_573_);
v___x_577_ = l_Nat_reprFast(v_major_574_);
v___x_578_ = ((lean_object*)(l_Lake_SemVerCore_toString___closed__0));
v___x_579_ = lean_string_append(v___x_577_, v___x_578_);
v___x_580_ = l_Nat_reprFast(v_minor_575_);
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
lean_dec_ref(v___x_580_);
v___x_582_ = lean_string_append(v___x_581_, v___x_578_);
v___x_583_ = l_Nat_reprFast(v_patch_576_);
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
lean_dec_ref(v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instToJson___lam__0(lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = l_Lake_SemVerCore_toString(v_x_587_);
v___x_589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instFromJson___lam__0(lean_object* v_x_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Json_getStr_x3f(v_x_592_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_603_; 
v_a_602_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_593_, 1);
v___x_603_ = l_Lake_SemVerCore_parse(v_a_602_);
return v___x_603_;
}
}
}
static lean_object* _init_l_Lake_instReprStdVer_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(16u);
v___x_621_ = lean_nat_to_int(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___redArg(lean_object* v_x_625_){
_start:
{
lean_object* v_toSemVerCore_626_; lean_object* v_specialDescr_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_660_; 
v_toSemVerCore_626_ = lean_ctor_get(v_x_625_, 0);
v_specialDescr_627_ = lean_ctor_get(v_x_625_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_660_ == 0)
{
v___x_629_ = v_x_625_;
v_isShared_630_ = v_isSharedCheck_660_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_specialDescr_627_);
lean_inc(v_toSemVerCore_626_);
lean_dec(v_x_625_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_660_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_631_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_632_ = ((lean_object*)(l_Lake_instReprStdVer_repr___redArg___closed__3));
v___x_633_ = lean_obj_once(&l_Lake_instReprStdVer_repr___redArg___closed__4, &l_Lake_instReprStdVer_repr___redArg___closed__4_once, _init_l_Lake_instReprStdVer_repr___redArg___closed__4);
v___x_634_ = l_Lake_instReprSemVerCore_repr___redArg(v_toSemVerCore_626_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 4);
lean_ctor_set(v___x_629_, 1, v___x_634_);
lean_ctor_set(v___x_629_, 0, v___x_633_);
v___x_636_ = v___x_629_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_634_);
v___x_636_ = v_reuseFailAlloc_659_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_637_ = 0;
v___x_638_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set_uint8(v___x_638_, sizeof(void*)*1, v___x_637_);
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_632_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_box(1);
v___x_643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = ((lean_object*)(l_Lake_instReprStdVer_repr___redArg___closed__6));
v___x_645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_631_);
v___x_647_ = l_String_quote(v_specialDescr_627_);
v___x_648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
v___x_649_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_633_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*1, v___x_637_);
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_646_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_653_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___x_651_);
v___x_655_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_652_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*1, v___x_637_);
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr(lean_object* v_x_661_, lean_object* v_prec_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lake_instReprStdVer_repr___redArg(v_x_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___boxed(lean_object* v_x_664_, lean_object* v_prec_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lake_instReprStdVer_repr(v_x_664_, v_prec_665_);
lean_dec(v_prec_665_);
return v_res_666_;
}
}
uint8_t l_Lake_instDecidableEqStdVer_decEq(lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
lean_object* v_toSemVerCore_671_; lean_object* v_specialDescr_672_; lean_object* v_toSemVerCore_673_; lean_object* v_specialDescr_674_; uint8_t v___x_675_; 
v_toSemVerCore_671_ = lean_ctor_get(v_x_669_, 0);
v_specialDescr_672_ = lean_ctor_get(v_x_669_, 1);
v_toSemVerCore_673_ = lean_ctor_get(v_x_670_, 0);
v_specialDescr_674_ = lean_ctor_get(v_x_670_, 1);
v___x_675_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_671_, v_toSemVerCore_673_);
if (v___x_675_ == 0)
{
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = lean_string_dec_eq(v_specialDescr_672_, v_specialDescr_674_);
return v___x_676_;
}
}
}
LEAN_EXPORT void l_Lake_instDecidableEqStdVer_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_669_ = stack[0].m_obj;
lean_object* v_x_670_ = stack[1].m_obj;
uint8_t v_res_677_;
v_res_677_ = l_Lake_instDecidableEqStdVer_decEq(v_x_669_, v_x_670_);
stack->m_num = v_res_677_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer_decEq___boxed(lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
uint8_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l_Lake_instDecidableEqStdVer_decEq(v_x_678_, v_x_679_);
lean_dec_ref(v_x_679_);
lean_dec_ref(v_x_678_);
v_r_681_ = lean_box(v_res_680_);
return v_r_681_;
}
}
uint8_t l_Lake_instDecidableEqStdVer(lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = l_Lake_instDecidableEqStdVer_decEq(v_x_682_, v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqStdVer_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_682_ = stack[0].m_obj;
lean_object* v_x_683_ = stack[1].m_obj;
uint8_t v_res_685_;
v_res_685_ = l_Lake_instDecidableEqStdVer(v_x_682_, v_x_683_);
stack->m_num = v_res_685_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer___boxed(lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
uint8_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_Lake_instDecidableEqStdVer(v_x_686_, v_x_687_);
lean_dec_ref(v_x_687_);
lean_dec_ref(v_x_686_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0(lean_object* v_self_690_){
_start:
{
lean_object* v_toSemVerCore_691_; 
v_toSemVerCore_691_ = lean_ctor_get(v_self_690_, 0);
lean_inc_ref(v_toSemVerCore_691_);
return v_toSemVerCore_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed(lean_object* v_self_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lake_StdVer_instCoeSemVerCore___lam__0(v_self_692_);
lean_dec_ref(v_self_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_ofSemVerCore(lean_object* v_ver_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_ver_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
return v___x_698_;
}
}
uint8_t l_Lake_StdVer_compare(lean_object* v_a_701_, lean_object* v_b_702_){
_start:
{
lean_object* v_toSemVerCore_703_; lean_object* v_specialDescr_704_; lean_object* v_toSemVerCore_705_; lean_object* v_specialDescr_706_; uint8_t v___x_707_; 
v_toSemVerCore_703_ = lean_ctor_get(v_a_701_, 0);
v_specialDescr_704_ = lean_ctor_get(v_a_701_, 1);
v_toSemVerCore_705_ = lean_ctor_get(v_b_702_, 0);
v_specialDescr_706_ = lean_ctor_get(v_b_702_, 1);
v___x_707_ = l_Lake_instOrdSemVerCore_ord(v_toSemVerCore_703_, v_toSemVerCore_705_);
if (v___x_707_ == 1)
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_709_ = lean_string_dec_eq(v_specialDescr_704_, v___x_708_);
if (v___x_709_ == 0)
{
uint8_t v___x_710_; 
v___x_710_ = lean_string_dec_eq(v_specialDescr_706_, v___x_708_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = lean_string_compare(v_specialDescr_704_, v_specialDescr_706_);
return v___x_711_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = 0;
return v___x_712_;
}
}
else
{
uint8_t v___x_713_; 
v___x_713_ = lean_string_dec_eq(v_specialDescr_706_, v___x_708_);
if (v___x_713_ == 0)
{
uint8_t v___x_714_; 
v___x_714_ = 2;
return v___x_714_;
}
else
{
return v___x_707_;
}
}
}
else
{
return v___x_707_;
}
}
}
LEAN_EXPORT void l_Lake_StdVer_compare_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_701_ = stack[0].m_obj;
lean_object* v_b_702_ = stack[1].m_obj;
uint8_t v_res_715_;
v_res_715_ = l_Lake_StdVer_compare(v_a_701_, v_b_702_);
stack->m_num = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lake_StdVer_compare___boxed(lean_object* v_a_716_, lean_object* v_b_717_){
_start:
{
uint8_t v_res_718_; lean_object* v_r_719_; 
v_res_718_ = l_Lake_StdVer_compare(v_a_716_, v_b_717_);
lean_dec_ref(v_b_717_);
lean_dec_ref(v_a_716_);
v_r_719_ = lean_box(v_res_718_);
return v_r_719_;
}
}
static lean_object* _init_l_Lake_StdVer_instLT(void){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_box(0);
return v___x_722_;
}
}
static lean_object* _init_l_Lake_StdVer_instLE(void){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = lean_box(0);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0(lean_object* v_x_724_, lean_object* v_y_725_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = l_Lake_StdVer_compare(v_x_724_, v_y_725_);
if (v___x_726_ == 2)
{
lean_inc_ref(v_y_725_);
return v_y_725_;
}
else
{
lean_inc_ref(v_x_724_);
return v_x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0___boxed(lean_object* v_x_727_, lean_object* v_y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lake_StdVer_instMin___lam__0(v_x_727_, v_y_728_);
lean_dec_ref(v_y_728_);
lean_dec_ref(v_x_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0(lean_object* v_x_732_, lean_object* v_y_733_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = l_Lake_StdVer_compare(v_x_732_, v_y_733_);
if (v___x_734_ == 2)
{
lean_inc_ref(v_x_732_);
return v_x_732_;
}
else
{
lean_inc_ref(v_y_733_);
return v_y_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0___boxed(lean_object* v_x_735_, lean_object* v_y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lake_StdVer_instMax___lam__0(v_x_735_, v_y_736_);
lean_dec_ref(v_y_736_);
lean_dec_ref(v_x_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parseM(lean_object* v_s_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_742_; 
lean_inc_ref(v_s_740_);
v___x_742_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_740_, v_a_741_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v_a_744_; lean_object* v___x_745_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
v_a_744_ = lean_ctor_get(v___x_742_, 1);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_742_, 2);
v___x_745_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_740_, v_a_744_);
lean_dec_ref(v_s_740_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_a_747_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_755_ == 0)
{
v___x_749_ = v___x_745_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_a_743_);
lean_ctor_set(v___x_751_, 1, v_a_746_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_a_747_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v_a_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_a_743_);
v_a_756_ = lean_ctor_get(v___x_745_, 0);
v_a_757_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_745_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_inc(v_a_756_);
lean_dec(v___x_745_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_756_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v_s_740_);
v_a_765_ = lean_ctor_get(v___x_742_, 0);
v_a_766_ = lean_ctor_get(v___x_742_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_742_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_inc(v_a_765_);
lean_dec(v___x_742_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parse(lean_object* v_s_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_string_utf8_byte_size(v_s_774_);
lean_inc_ref(v_s_774_);
v___x_777_ = l_Lake_StdVer_parseM(v_s_774_, v___x_775_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v_a_779_; uint8_t v_decide_780_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
v_a_779_ = lean_ctor_get(v___x_777_, 1);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_777_, 2);
v_decide_780_ = lean_nat_dec_eq(v_a_779_, v___x_776_);
if (v_decide_780_ == 0)
{
lean_object* v_tail_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec(v_a_778_);
v_tail_781_ = lean_string_utf8_extract(v_s_774_, v_a_779_, v___x_776_);
lean_dec(v_a_779_);
lean_dec_ref(v_s_774_);
v___x_782_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_783_ = lean_string_append(v___x_782_, v_tail_781_);
lean_dec_ref(v_tail_781_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; 
lean_dec(v_a_779_);
lean_dec_ref(v_s_774_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v_a_778_);
return v___x_785_;
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_787_; 
lean_dec_ref(v_s_774_);
v_a_786_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_777_, 2);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v_a_786_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_toString(lean_object* v_ver_789_){
_start:
{
lean_object* v_toSemVerCore_790_; lean_object* v_specialDescr_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_toSemVerCore_790_ = lean_ctor_get(v_ver_789_, 0);
lean_inc_ref(v_toSemVerCore_790_);
v_specialDescr_791_ = lean_ctor_get(v_ver_789_, 1);
lean_inc_ref(v_specialDescr_791_);
lean_dec_ref(v_ver_789_);
v___x_792_ = lean_string_utf8_byte_size(v_specialDescr_791_);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_nat_dec_eq(v___x_792_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_795_ = l_Lake_SemVerCore_toString(v_toSemVerCore_790_);
v___x_796_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_797_ = lean_string_append(v___x_795_, v___x_796_);
v___x_798_ = lean_string_append(v___x_797_, v_specialDescr_791_);
lean_dec_ref(v_specialDescr_791_);
return v___x_798_;
}
else
{
lean_object* v___x_799_; 
lean_dec_ref(v_specialDescr_791_);
v___x_799_ = l_Lake_SemVerCore_toString(v_toSemVerCore_790_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instToJson___lam__0(lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = l_Lake_StdVer_toString(v_x_802_);
v___x_804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instFromJson___lam__0(lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Json_getStr_x3f(v_x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_808_, 1);
v___x_818_ = l_Lake_StdVer_parse(v_a_817_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___impl(lean_object* v_x_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_obj_tag_nat(v_x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___impl___boxed(lean_object* v_x_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lake_ToolchainVer_ctorIdx___impl(v_x_829_);
lean_dec_ref(v_x_829_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___redArg(lean_object* v_t_831_, lean_object* v_k_832_){
_start:
{
switch(lean_obj_tag(v_t_831_))
{
case 1:
{
lean_object* v_date_833_; lean_object* v_rev_834_; lean_object* v___x_835_; 
v_date_833_ = lean_ctor_get(v_t_831_, 0);
lean_inc_ref(v_date_833_);
v_rev_834_ = lean_ctor_get(v_t_831_, 1);
lean_inc(v_rev_834_);
lean_dec_ref_known(v_t_831_, 2);
v___x_835_ = lean_apply_2(v_k_832_, v_date_833_, v_rev_834_);
return v___x_835_;
}
case 2:
{
lean_object* v_n_836_; lean_object* v___x_837_; 
v_n_836_ = lean_ctor_get(v_t_831_, 0);
lean_inc(v_n_836_);
lean_dec_ref_known(v_t_831_, 1);
v___x_837_ = lean_apply_1(v_k_832_, v_n_836_);
return v___x_837_;
}
default: 
{
lean_object* v_ver_838_; lean_object* v___x_839_; 
v_ver_838_ = lean_ctor_get(v_t_831_, 0);
lean_inc_ref(v_ver_838_);
lean_dec_ref(v_t_831_);
v___x_839_ = lean_apply_1(v_k_832_, v_ver_838_);
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim(lean_object* v_motive_840_, lean_object* v_ctorIdx_841_, lean_object* v_t_842_, lean_object* v_h_843_, lean_object* v_k_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_842_, v_k_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___boxed(lean_object* v_motive_846_, lean_object* v_ctorIdx_847_, lean_object* v_t_848_, lean_object* v_h_849_, lean_object* v_k_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lake_ToolchainVer_ctorElim(v_motive_846_, v_ctorIdx_847_, v_t_848_, v_h_849_, v_k_850_);
lean_dec(v_ctorIdx_847_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim___redArg(lean_object* v_t_852_, lean_object* v_release_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_852_, v_release_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim(lean_object* v_motive_855_, lean_object* v_t_856_, lean_object* v_h_857_, lean_object* v_release_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_856_, v_release_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim___redArg(lean_object* v_t_860_, lean_object* v_nightly_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_860_, v_nightly_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim(lean_object* v_motive_863_, lean_object* v_t_864_, lean_object* v_h_865_, lean_object* v_nightly_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_864_, v_nightly_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim___redArg(lean_object* v_t_868_, lean_object* v_pr_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_868_, v_pr_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim(lean_object* v_motive_871_, lean_object* v_t_872_, lean_object* v_h_873_, lean_object* v_pr_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_872_, v_pr_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim___redArg(lean_object* v_t_876_, lean_object* v_other_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_876_, v_other_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim(lean_object* v_motive_879_, lean_object* v_t_880_, lean_object* v_h_881_, lean_object* v_other_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_880_, v_other_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override___redArg(lean_object* v_t_884_, lean_object* v_release_885_, lean_object* v_nightly_886_, lean_object* v_pr_887_, lean_object* v_other_888_){
_start:
{
switch(lean_obj_tag(v_t_884_))
{
case 0:
{
lean_object* v_ver_889_; lean_object* v___x_890_; 
lean_dec(v_other_888_);
lean_dec(v_pr_887_);
lean_dec(v_nightly_886_);
v_ver_889_ = lean_ctor_get(v_t_884_, 1);
lean_inc_ref(v_ver_889_);
lean_dec_ref_known(v_t_884_, 2);
v___x_890_ = lean_apply_1(v_release_885_, v_ver_889_);
return v___x_890_;
}
case 1:
{
lean_object* v_date_891_; lean_object* v_rev_892_; lean_object* v___x_893_; 
lean_dec(v_other_888_);
lean_dec(v_pr_887_);
lean_dec(v_release_885_);
v_date_891_ = lean_ctor_get(v_t_884_, 1);
lean_inc_ref(v_date_891_);
v_rev_892_ = lean_ctor_get(v_t_884_, 2);
lean_inc(v_rev_892_);
lean_dec_ref_known(v_t_884_, 3);
v___x_893_ = lean_apply_2(v_nightly_886_, v_date_891_, v_rev_892_);
return v___x_893_;
}
case 2:
{
lean_object* v_n_894_; lean_object* v___x_895_; 
lean_dec(v_other_888_);
lean_dec(v_nightly_886_);
lean_dec(v_release_885_);
v_n_894_ = lean_ctor_get(v_t_884_, 1);
lean_inc(v_n_894_);
lean_dec_ref_known(v_t_884_, 2);
v___x_895_ = lean_apply_1(v_pr_887_, v_n_894_);
return v___x_895_;
}
default: 
{
lean_object* v_v_896_; lean_object* v___x_897_; 
lean_dec(v_pr_887_);
lean_dec(v_nightly_886_);
lean_dec(v_release_885_);
v_v_896_ = lean_ctor_get(v_t_884_, 1);
lean_inc_ref(v_v_896_);
lean_dec_ref_known(v_t_884_, 2);
v___x_897_ = lean_apply_1(v_other_888_, v_v_896_);
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override(lean_object* v_motive_898_, lean_object* v_t_899_, lean_object* v_release_900_, lean_object* v_nightly_901_, lean_object* v_pr_902_, lean_object* v_other_903_){
_start:
{
switch(lean_obj_tag(v_t_899_))
{
case 0:
{
lean_object* v_ver_904_; lean_object* v___x_905_; 
lean_dec(v_other_903_);
lean_dec(v_pr_902_);
lean_dec(v_nightly_901_);
v_ver_904_ = lean_ctor_get(v_t_899_, 1);
lean_inc_ref(v_ver_904_);
lean_dec_ref_known(v_t_899_, 2);
v___x_905_ = lean_apply_1(v_release_900_, v_ver_904_);
return v___x_905_;
}
case 1:
{
lean_object* v_date_906_; lean_object* v_rev_907_; lean_object* v___x_908_; 
lean_dec(v_other_903_);
lean_dec(v_pr_902_);
lean_dec(v_release_900_);
v_date_906_ = lean_ctor_get(v_t_899_, 1);
lean_inc_ref(v_date_906_);
v_rev_907_ = lean_ctor_get(v_t_899_, 2);
lean_inc(v_rev_907_);
lean_dec_ref_known(v_t_899_, 3);
v___x_908_ = lean_apply_2(v_nightly_901_, v_date_906_, v_rev_907_);
return v___x_908_;
}
case 2:
{
lean_object* v_n_909_; lean_object* v___x_910_; 
lean_dec(v_other_903_);
lean_dec(v_nightly_901_);
lean_dec(v_release_900_);
v_n_909_ = lean_ctor_get(v_t_899_, 1);
lean_inc(v_n_909_);
lean_dec_ref_known(v_t_899_, 2);
v___x_910_ = lean_apply_1(v_pr_902_, v_n_909_);
return v___x_910_;
}
default: 
{
lean_object* v_v_911_; lean_object* v___x_912_; 
lean_dec(v_pr_902_);
lean_dec(v_nightly_901_);
lean_dec(v_release_900_);
v_v_911_ = lean_ctor_get(v_t_899_, 1);
lean_inc_ref(v_v_911_);
lean_dec_ref_known(v_t_899_, 2);
v___x_912_ = lean_apply_1(v_other_903_, v_v_911_);
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release___override(lean_object* v_ver_914_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_915_ = ((lean_object*)(l_Lake_ToolchainVer_release___override___closed__0));
lean_inc_ref(v_ver_914_);
v___x_916_ = l_Lake_StdVer_toString(v_ver_914_);
v___x_917_ = lean_string_append(v___x_915_, v___x_916_);
lean_dec_ref(v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v_ver_914_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly___override(lean_object* v_date_921_, lean_object* v_rev_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___y_927_; 
v___x_923_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__0));
lean_inc_ref(v_date_921_);
v___x_924_ = l_Lake_Date_toString(v_date_921_);
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
lean_dec_ref(v___x_924_);
if (lean_obj_tag(v_rev_922_) == 0)
{
lean_object* v___x_930_; 
v___x_930_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___y_927_ = v___x_930_;
goto v___jp_926_;
}
else
{
lean_object* v_val_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_val_931_ = lean_ctor_get(v_rev_922_, 0);
v___x_932_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
lean_inc(v_val_931_);
v___x_933_ = l_Nat_reprFast(v_val_931_);
v___x_934_ = lean_string_append(v___x_932_, v___x_933_);
lean_dec_ref(v___x_933_);
v___y_927_ = v___x_934_;
goto v___jp_926_;
}
v___jp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_string_append(v___x_925_, v___y_927_);
lean_dec_ref(v___y_927_);
v___x_929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_date_921_);
lean_ctor_set(v___x_929_, 2, v_rev_922_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr___override(lean_object* v_n_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = ((lean_object*)(l_Lake_ToolchainVer_pr___override___closed__0));
lean_inc(v_n_936_);
v___x_938_ = l_Nat_reprFast(v_n_936_);
v___x_939_ = lean_string_append(v___x_937_, v___x_938_);
lean_dec_ref(v___x_938_);
v___x_940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v_n_936_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other___override(lean_object* v_v_941_){
_start:
{
lean_object* v___x_942_; 
lean_inc_ref(v_v_941_);
v___x_942_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_942_, 0, v_v_941_);
lean_ctor_set(v___x_942_, 1, v_v_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override(lean_object* v_x_943_){
_start:
{
lean_object* v_toString_944_; 
v_toString_944_ = lean_ctor_get(v_x_943_, 0);
lean_inc_ref(v_toString_944_);
return v_toString_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override___boxed(lean_object* v_x_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lake_ToolchainVer_toString___override(v_x_945_);
lean_dec_ref(v_x_945_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_953_) == 0)
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1));
return v___x_955_;
}
else
{
lean_object* v_val_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_967_; 
v_val_956_ = lean_ctor_get(v_x_953_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_x_953_);
if (v_isSharedCheck_967_ == 0)
{
v___x_958_ = v_x_953_;
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_val_956_);
lean_dec(v_x_953_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3));
v___x_961_ = l_Nat_reprFast(v_val_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 3);
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_966_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_960_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l_Repr_addAppParen(v___x_964_, v_x_954_);
return v___x_965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___boxed(lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_x_968_, v_x_969_);
lean_dec(v_x_969_);
return v_res_970_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__3(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_unsigned_to_nat(2u);
v___x_978_ = lean_nat_to_int(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__4(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_unsigned_to_nat(1u);
v___x_980_ = lean_nat_to_int(v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr(lean_object* v_x_999_, lean_object* v_prec_1000_){
_start:
{
switch(lean_obj_tag(v_x_999_))
{
case 0:
{
lean_object* v_ver_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1020_; 
v_ver_1001_ = lean_ctor_get(v_x_999_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_x_999_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_x_999_, 0);
lean_dec(v_unused_1021_);
v___x_1003_ = v_x_999_;
v_isShared_1004_ = v_isSharedCheck_1020_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_ver_1001_);
lean_dec(v_x_999_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1020_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___y_1006_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_unsigned_to_nat(1024u);
v___x_1017_ = lean_nat_dec_le(v___x_1016_, v_prec_1000_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1006_ = v___x_1018_;
goto v___jp_1005_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1006_ = v___x_1019_;
goto v___jp_1005_;
}
v___jp_1005_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1007_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__2));
v___x_1008_ = l_Lake_instReprStdVer_repr___redArg(v_ver_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set_tag(v___x_1003_, 5);
lean_ctor_set(v___x_1003_, 1, v___x_1008_);
lean_ctor_set(v___x_1003_, 0, v___x_1007_);
v___x_1010_ = v___x_1003_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_inc(v___y_1006_);
v___x_1011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___y_1006_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = 0;
v___x_1013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*1, v___x_1012_);
v___x_1014_ = l_Repr_addAppParen(v___x_1013_, v_prec_1000_);
return v___x_1014_;
}
}
}
}
case 1:
{
lean_object* v_date_1022_; lean_object* v_rev_1023_; lean_object* v___y_1025_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_date_1022_ = lean_ctor_get(v_x_999_, 1);
lean_inc_ref(v_date_1022_);
v_rev_1023_ = lean_ctor_get(v_x_999_, 2);
lean_inc(v_rev_1023_);
lean_dec_ref_known(v_x_999_, 3);
v___x_1038_ = lean_unsigned_to_nat(1024u);
v___x_1039_ = lean_nat_dec_le(v___x_1038_, v_prec_1000_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1025_ = v___x_1040_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1025_ = v___x_1041_;
goto v___jp_1024_;
}
v___jp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1026_ = lean_box(1);
v___x_1027_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__7));
v___x_1028_ = lean_unsigned_to_nat(1024u);
v___x_1029_ = l_Lake_instReprDate_repr___redArg(v_date_1022_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1027_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1026_);
v___x_1032_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_rev_1023_, v___x_1028_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
lean_inc(v___y_1025_);
v___x_1034_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___y_1025_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = 0;
v___x_1036_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*1, v___x_1035_);
v___x_1037_ = l_Repr_addAppParen(v___x_1036_, v_prec_1000_);
return v___x_1037_;
}
}
case 2:
{
lean_object* v_n_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1062_; 
v_n_1042_ = lean_ctor_get(v_x_999_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_x_999_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v_x_999_, 0);
lean_dec(v_unused_1063_);
v___x_1044_ = v_x_999_;
v_isShared_1045_ = v_isSharedCheck_1062_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_n_1042_);
lean_dec(v_x_999_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1062_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___y_1047_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_unsigned_to_nat(1024u);
v___x_1059_ = lean_nat_dec_le(v___x_1058_, v_prec_1000_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1047_ = v___x_1060_;
goto v___jp_1046_;
}
else
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1047_ = v___x_1061_;
goto v___jp_1046_;
}
v___jp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1048_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__10));
v___x_1049_ = l_Nat_reprFast(v_n_1042_);
v___x_1050_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 5);
lean_ctor_set(v___x_1044_, 1, v___x_1050_);
lean_ctor_set(v___x_1044_, 0, v___x_1048_);
v___x_1052_ = v___x_1044_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_inc(v___y_1047_);
v___x_1053_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___y_1047_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = 0;
v___x_1055_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*1, v___x_1054_);
v___x_1056_ = l_Repr_addAppParen(v___x_1055_, v_prec_1000_);
return v___x_1056_;
}
}
}
}
default: 
{
lean_object* v_v_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1084_; 
v_v_1064_ = lean_ctor_get(v_x_999_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_x_999_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_x_999_, 0);
lean_dec(v_unused_1085_);
v___x_1066_ = v_x_999_;
v_isShared_1067_ = v_isSharedCheck_1084_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_v_1064_);
lean_dec(v_x_999_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1084_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___y_1069_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_unsigned_to_nat(1024u);
v___x_1081_ = lean_nat_dec_le(v___x_1080_, v_prec_1000_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1069_ = v___x_1082_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1069_ = v___x_1083_;
goto v___jp_1068_;
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1070_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__13));
v___x_1071_ = l_String_quote(v_v_1064_);
v___x_1072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 5);
lean_ctor_set(v___x_1066_, 1, v___x_1072_);
lean_ctor_set(v___x_1066_, 0, v___x_1070_);
v___x_1074_ = v___x_1066_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_inc(v___y_1069_);
v___x_1075_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___y_1069_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = 0;
v___x_1077_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*1, v___x_1076_);
v___x_1078_ = l_Repr_addAppParen(v___x_1077_, v_prec_1000_);
return v___x_1078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr___boxed(lean_object* v_x_1086_, lean_object* v_prec_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lake_instReprToolchainVer_repr(v_x_1086_, v_prec_1087_);
lean_dec(v_prec_1087_);
return v_res_1088_;
}
}
uint8_t l_Lake_instDecidableEqToolchainVer_decEq(lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
switch(lean_obj_tag(v_x_1091_))
{
case 0:
{
if (lean_obj_tag(v_x_1092_) == 0)
{
lean_object* v_ver_1093_; lean_object* v_ver_1094_; uint8_t v___x_1095_; 
v_ver_1093_ = lean_ctor_get(v_x_1091_, 1);
lean_inc_ref(v_ver_1093_);
lean_dec_ref_known(v_x_1091_, 2);
v_ver_1094_ = lean_ctor_get(v_x_1092_, 1);
lean_inc_ref(v_ver_1094_);
lean_dec_ref_known(v_x_1092_, 2);
v___x_1095_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_1093_, v_ver_1094_);
lean_dec_ref(v_ver_1094_);
lean_dec_ref(v_ver_1093_);
return v___x_1095_;
}
else
{
uint8_t v___x_1096_; 
lean_dec_ref_known(v_x_1091_, 2);
lean_dec_ref(v_x_1092_);
v___x_1096_ = 0;
return v___x_1096_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1092_) == 1)
{
lean_object* v_date_1097_; lean_object* v_rev_1098_; lean_object* v_date_1099_; lean_object* v_rev_1100_; uint8_t v___x_1101_; 
v_date_1097_ = lean_ctor_get(v_x_1091_, 1);
lean_inc_ref(v_date_1097_);
v_rev_1098_ = lean_ctor_get(v_x_1091_, 2);
lean_inc(v_rev_1098_);
lean_dec_ref_known(v_x_1091_, 3);
v_date_1099_ = lean_ctor_get(v_x_1092_, 1);
lean_inc_ref(v_date_1099_);
v_rev_1100_ = lean_ctor_get(v_x_1092_, 2);
lean_inc(v_rev_1100_);
lean_dec_ref_known(v_x_1092_, 3);
v___x_1101_ = l_Lake_instDecidableEqDate_decEq(v_date_1097_, v_date_1099_);
lean_dec_ref(v_date_1099_);
lean_dec_ref(v_date_1097_);
if (v___x_1101_ == 0)
{
lean_dec(v_rev_1100_);
lean_dec(v_rev_1098_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_1103_ = l_Option_instDecidableEq___redArg(v___x_1102_, v_rev_1098_, v_rev_1100_);
return v___x_1103_;
}
}
else
{
uint8_t v___x_1104_; 
lean_dec_ref_known(v_x_1091_, 3);
lean_dec_ref(v_x_1092_);
v___x_1104_ = 0;
return v___x_1104_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1092_) == 2)
{
lean_object* v_n_1105_; lean_object* v_n_1106_; uint8_t v___x_1107_; 
v_n_1105_ = lean_ctor_get(v_x_1091_, 1);
lean_inc(v_n_1105_);
lean_dec_ref_known(v_x_1091_, 2);
v_n_1106_ = lean_ctor_get(v_x_1092_, 1);
lean_inc(v_n_1106_);
lean_dec_ref_known(v_x_1092_, 2);
v___x_1107_ = lean_nat_dec_eq(v_n_1105_, v_n_1106_);
lean_dec(v_n_1106_);
lean_dec(v_n_1105_);
return v___x_1107_;
}
else
{
uint8_t v___x_1108_; 
lean_dec_ref_known(v_x_1091_, 2);
lean_dec_ref(v_x_1092_);
v___x_1108_ = 0;
return v___x_1108_;
}
}
default: 
{
if (lean_obj_tag(v_x_1092_) == 3)
{
lean_object* v_v_1109_; lean_object* v_v_1110_; uint8_t v___x_1111_; 
v_v_1109_ = lean_ctor_get(v_x_1091_, 1);
lean_inc_ref(v_v_1109_);
lean_dec_ref_known(v_x_1091_, 2);
v_v_1110_ = lean_ctor_get(v_x_1092_, 1);
lean_inc_ref(v_v_1110_);
lean_dec_ref_known(v_x_1092_, 2);
v___x_1111_ = lean_string_dec_eq(v_v_1109_, v_v_1110_);
lean_dec_ref(v_v_1110_);
lean_dec_ref(v_v_1109_);
return v___x_1111_;
}
else
{
uint8_t v___x_1112_; 
lean_dec_ref_known(v_x_1091_, 2);
lean_dec_ref(v_x_1092_);
v___x_1112_ = 0;
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instDecidableEqToolchainVer_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1091_ = stack[0].m_obj;
lean_object* v_x_1092_ = stack[1].m_obj;
uint8_t v_res_1113_;
v_res_1113_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1091_, v_x_1092_);
stack->m_num = v_res_1113_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer_decEq___boxed(lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
uint8_t v_res_1116_; lean_object* v_r_1117_; 
v_res_1116_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1114_, v_x_1115_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
uint8_t l_Lake_instDecidableEqToolchainVer(lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
uint8_t v___x_1120_; 
v___x_1120_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1118_, v_x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqToolchainVer_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1118_ = stack[0].m_obj;
lean_object* v_x_1119_ = stack[1].m_obj;
uint8_t v_res_1121_;
v_res_1121_ = l_Lake_instDecidableEqToolchainVer(v_x_1118_, v_x_1119_);
stack->m_num = v_res_1121_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer___boxed(lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
uint8_t v_res_1124_; lean_object* v_r_1125_; 
v_res_1124_ = l_Lake_instDecidableEqToolchainVer(v_x_1122_, v_x_1123_);
v_r_1125_ = lean_box(v_res_1124_);
return v_r_1125_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(lean_object* v_s_1129_){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1130_ = lean_string_utf8_byte_size(v_s_1129_);
v___x_1131_ = lean_unsigned_to_nat(8u);
v___x_1132_ = lean_nat_dec_le(v___x_1131_, v___x_1130_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec_ref(v_s_1129_);
v___x_1133_ = lean_box(0);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_string_memcmp(v_s_1129_, v___x_1134_, v___x_1135_, v___x_1135_, v___x_1131_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
lean_dec_ref(v_s_1129_);
v___x_1137_ = lean_box(0);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_inc_ref(v_s_1129_);
v___x_1138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1138_, 0, v_s_1129_);
lean_ctor_set(v___x_1138_, 1, v___x_1135_);
lean_ctor_set(v___x_1138_, 2, v___x_1130_);
v___x_1139_ = l_String_Slice_pos_x21(v___x_1138_, v___x_1131_);
lean_dec_ref_known(v___x_1138_, 3);
v___x_1140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1140_, 0, v_s_1129_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
lean_ctor_set(v___x_1140_, 2, v___x_1130_);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(lean_object* v_s_1142_, lean_object* v_pat_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v_s_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(lean_object* v_s_1145_, lean_object* v_pat_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(v_s_1145_, v_pat_1146_);
lean_dec_ref(v_pat_1146_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(lean_object* v_s_1148_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1149_ = lean_string_utf8_byte_size(v_s_1148_);
v___x_1150_ = lean_unsigned_to_nat(16u);
v___x_1151_ = lean_nat_dec_le(v___x_1150_, v___x_1149_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
lean_dec_ref(v_s_1148_);
v___x_1152_ = lean_box(0);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1153_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = lean_string_memcmp(v_s_1148_, v___x_1153_, v___x_1154_, v___x_1154_, v___x_1150_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_dec_ref(v_s_1148_);
v___x_1156_ = lean_box(0);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_inc_ref(v_s_1148_);
v___x_1157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1157_, 0, v_s_1148_);
lean_ctor_set(v___x_1157_, 1, v___x_1154_);
lean_ctor_set(v___x_1157_, 2, v___x_1149_);
v___x_1158_ = l_String_Slice_pos_x21(v___x_1157_, v___x_1150_);
lean_dec_ref_known(v___x_1157_, 3);
v___x_1159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1159_, 0, v_s_1148_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
lean_ctor_set(v___x_1159_, 2, v___x_1149_);
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(lean_object* v_s_1161_, lean_object* v_pat_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v_s_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(lean_object* v_s_1164_, lean_object* v_pat_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(v_s_1164_, v_pat_1165_);
lean_dec_ref(v_pat_1165_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object* v_s_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = lean_string_utf8_byte_size(v_s_1168_);
v___x_1170_ = lean_unsigned_to_nat(11u);
v___x_1171_ = lean_nat_dec_le(v___x_1170_, v___x_1169_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
lean_dec_ref(v_s_1168_);
v___x_1172_ = lean_box(0);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1173_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0));
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_string_memcmp(v_s_1168_, v___x_1173_, v___x_1174_, v___x_1174_, v___x_1170_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
lean_dec_ref(v_s_1168_);
v___x_1176_ = lean_box(0);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_inc_ref(v_s_1168_);
v___x_1177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1177_, 0, v_s_1168_);
lean_ctor_set(v___x_1177_, 1, v___x_1174_);
lean_ctor_set(v___x_1177_, 2, v___x_1169_);
v___x_1178_ = l_String_Slice_pos_x21(v___x_1177_, v___x_1170_);
lean_dec_ref_known(v___x_1177_, 3);
v___x_1179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1179_, 0, v_s_1168_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
lean_ctor_set(v___x_1179_, 2, v___x_1169_);
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(lean_object* v_s_1181_, lean_object* v_pat_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v_s_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object* v_s_1184_, lean_object* v_pat_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(v_s_1184_, v_pat_1185_);
lean_dec_ref(v_pat_1185_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(lean_object* v___x_1187_, lean_object* v_ver_1188_, lean_object* v_a_1189_, lean_object* v_b_1190_){
_start:
{
uint8_t v_decide_1191_; 
v_decide_1191_ = lean_nat_dec_eq(v_a_1189_, v___x_1187_);
if (v_decide_1191_ == 0)
{
uint32_t v___x_1192_; uint32_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1192_ = lean_string_utf8_get_fast(v_ver_1188_, v_a_1189_);
v___x_1193_ = 58;
v___x_1194_ = lean_uint32_dec_eq(v___x_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_box(0);
v___x_1196_ = lean_string_utf8_next_fast(v_ver_1188_, v_a_1189_);
lean_dec(v_a_1189_);
v_a_1189_ = v___x_1196_;
v_b_1190_ = v___x_1195_;
goto _start;
}
else
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_a_1189_);
return v___x_1198_;
}
}
else
{
lean_dec(v_a_1189_);
lean_inc(v_b_1190_);
return v_b_1190_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg___boxed(lean_object* v___x_1199_, lean_object* v_ver_1200_, lean_object* v_a_1201_, lean_object* v_b_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1199_, v_ver_1200_, v_a_1201_, v_b_1202_);
lean_dec(v_b_1202_);
lean_dec_ref(v_ver_1200_);
lean_dec(v___x_1199_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object* v___x_1204_, lean_object* v_rest_1205_, lean_object* v_a_1206_, lean_object* v_b_1207_){
_start:
{
uint8_t v_decide_1208_; 
v_decide_1208_ = lean_nat_dec_eq(v_a_1206_, v___x_1204_);
if (v_decide_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_string_utf8_next_fast(v_rest_1205_, v_a_1206_);
lean_dec(v_a_1206_);
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_nat_add(v_b_1207_, v___x_1210_);
lean_dec(v_b_1207_);
v_a_1206_ = v___x_1209_;
v_b_1207_ = v___x_1211_;
goto _start;
}
else
{
lean_dec(v_a_1206_);
return v_b_1207_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg___boxed(lean_object* v___x_1213_, lean_object* v_rest_1214_, lean_object* v_a_1215_, lean_object* v_b_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___x_1213_, v_rest_1214_, v_a_1215_, v_b_1216_);
lean_dec_ref(v_rest_1214_);
lean_dec(v___x_1213_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofString(lean_object* v_ver_1220_){
_start:
{
uint8_t v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1243_; lean_object* v___y_1244_; uint8_t v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1257_; lean_object* v___y_1258_; uint8_t v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1267_; uint8_t v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v_fst_1317_; lean_object* v_snd_1318_; lean_object* v___y_1340_; lean_object* v_searcher_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_searcher_1348_ = lean_unsigned_to_nat(0u);
v___x_1349_ = lean_string_utf8_byte_size(v_ver_1220_);
v___x_1350_ = lean_box(0);
v___x_1351_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1349_, v_ver_1220_, v_searcher_1348_, v___x_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
v___y_1340_ = v___x_1349_;
goto v___jp_1339_;
}
else
{
lean_object* v_val_1352_; 
v_val_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_val_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___y_1340_ = v_val_1352_;
goto v___jp_1339_;
}
v___jp_1221_:
{
if (v___y_1222_ == 0)
{
lean_object* v___x_1227_; 
v___x_1227_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v___y_1224_);
if (lean_obj_tag(v___x_1227_) == 1)
{
lean_object* v_val_1228_; lean_object* v_startInclusive_1229_; lean_object* v_endExclusive_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_val_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v_startInclusive_1229_ = lean_ctor_get(v_val_1228_, 1);
v_endExclusive_1230_ = lean_ctor_get(v_val_1228_, 2);
v___x_1231_ = lean_nat_sub(v_endExclusive_1230_, v_startInclusive_1229_);
v___x_1232_ = lean_nat_dec_eq(v___x_1231_, v___y_1223_);
lean_dec(v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1233_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1234_ = lean_unsigned_to_nat(8u);
v___x_1235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___y_1223_);
lean_ctor_set(v___x_1235_, 2, v___x_1234_);
v___x_1236_ = l_String_Slice_beq(v_val_1228_, v___x_1235_);
lean_dec_ref_known(v___x_1235_, 3);
lean_dec(v_val_1228_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_inc_ref(v_ver_1220_);
v___x_1237_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_ver_1220_);
lean_ctor_set(v___x_1237_, 1, v_ver_1220_);
return v___x_1237_;
}
else
{
lean_object* v___x_1238_; 
lean_dec_ref(v_ver_1220_);
v___x_1238_ = l_Lake_ToolchainVer_nightly___override(v___y_1226_, v___y_1225_);
return v___x_1238_;
}
}
else
{
lean_object* v___x_1239_; 
lean_dec(v_val_1228_);
lean_dec(v___y_1223_);
lean_dec_ref(v_ver_1220_);
v___x_1239_ = l_Lake_ToolchainVer_nightly___override(v___y_1226_, v___y_1225_);
return v___x_1239_;
}
}
else
{
lean_object* v___x_1240_; 
lean_dec(v___x_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1223_);
lean_inc_ref(v_ver_1220_);
v___x_1240_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_ver_1220_);
lean_ctor_set(v___x_1240_, 1, v_ver_1220_);
return v___x_1240_;
}
}
else
{
lean_object* v___x_1241_; 
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v_ver_1220_);
v___x_1241_ = l_Lake_ToolchainVer_nightly___override(v___y_1226_, v___y_1225_);
return v___x_1241_;
}
}
v___jp_1242_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
lean_dec_ref(v___y_1249_);
v___x_1252_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_1247_);
v___x_1253_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___y_1243_, v___y_1244_, v___x_1252_, v___y_1247_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
v___x_1254_ = lean_nat_dec_le(v___x_1253_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec(v___x_1253_);
if (v___x_1254_ == 0)
{
if (lean_obj_tag(v___y_1251_) == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_inc_ref(v_ver_1220_);
v___x_1255_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_ver_1220_);
lean_ctor_set(v___x_1255_, 1, v_ver_1220_);
return v___x_1255_;
}
else
{
v___y_1222_ = v___y_1245_;
v___y_1223_ = v___y_1247_;
v___y_1224_ = v___y_1248_;
v___y_1225_ = v___y_1251_;
v___y_1226_ = v___y_1250_;
goto v___jp_1221_;
}
}
else
{
v___y_1222_ = v___y_1245_;
v___y_1223_ = v___y_1247_;
v___y_1224_ = v___y_1248_;
v___y_1225_ = v___y_1251_;
v___y_1226_ = v___y_1250_;
goto v___jp_1221_;
}
}
v___jp_1256_:
{
lean_object* v___x_1265_; 
v___x_1265_ = lean_box(0);
v___y_1243_ = v___y_1257_;
v___y_1244_ = v___y_1258_;
v___y_1245_ = v___y_1259_;
v___y_1246_ = v___y_1260_;
v___y_1247_ = v___y_1261_;
v___y_1248_ = v___y_1262_;
v___y_1249_ = v___y_1263_;
v___y_1250_ = v___y_1264_;
v___y_1251_ = v___x_1265_;
goto v___jp_1242_;
}
v___jp_1266_:
{
lean_object* v___x_1271_; 
lean_inc_ref(v___y_1267_);
v___x_1271_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v___y_1267_);
if (lean_obj_tag(v___x_1271_) == 1)
{
lean_object* v_val_1272_; lean_object* v_rest_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref(v___y_1267_);
v_val_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_val_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v_rest_1273_ = l_String_Slice_toString(v_val_1272_);
lean_dec(v_val_1272_);
v___x_1274_ = lean_unsigned_to_nat(10u);
v___x_1275_ = lean_string_utf8_byte_size(v_rest_1273_);
lean_inc_n(v___y_1269_, 3);
lean_inc_ref_n(v_rest_1273_, 2);
v___x_1276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1276_, 0, v_rest_1273_);
lean_ctor_set(v___x_1276_, 1, v___y_1269_);
lean_ctor_set(v___x_1276_, 2, v___x_1275_);
v___x_1277_ = l_String_Slice_Pos_nextn(v___x_1276_, v___y_1269_, v___x_1274_);
lean_inc(v___x_1277_);
v___x_1278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1278_, 0, v_rest_1273_);
lean_ctor_set(v___x_1278_, 1, v___y_1269_);
lean_ctor_set(v___x_1278_, 2, v___x_1277_);
v___x_1279_ = l_String_Slice_toString(v___x_1278_);
lean_dec_ref_known(v___x_1278_, 3);
v___x_1280_ = l_Lake_Date_ofString_x3f(v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 1)
{
lean_object* v_val_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = lean_unsigned_to_nat(4u);
v___x_1283_ = lean_nat_sub(v___x_1275_, v___x_1277_);
v___x_1284_ = lean_nat_dec_le(v___x_1282_, v___x_1283_);
lean_dec(v___x_1283_);
if (v___x_1284_ == 0)
{
lean_dec(v___x_1277_);
v___y_1257_ = v___x_1275_;
v___y_1258_ = v_rest_1273_;
v___y_1259_ = v___y_1268_;
v___y_1260_ = v___x_1274_;
v___y_1261_ = v___y_1269_;
v___y_1262_ = v___y_1270_;
v___y_1263_ = v___x_1276_;
v___y_1264_ = v_val_1281_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1286_ = lean_string_memcmp(v_rest_1273_, v___x_1285_, v___x_1277_, v___y_1269_, v___x_1282_);
if (v___x_1286_ == 0)
{
lean_dec(v___x_1277_);
v___y_1257_ = v___x_1275_;
v___y_1258_ = v_rest_1273_;
v___y_1259_ = v___y_1268_;
v___y_1260_ = v___x_1274_;
v___y_1261_ = v___y_1269_;
v___y_1262_ = v___y_1270_;
v___y_1263_ = v___x_1276_;
v___y_1264_ = v_val_1281_;
goto v___jp_1256_;
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
v___x_1288_ = l_String_Slice_pos_x21(v___x_1287_, v___x_1282_);
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
lean_inc(v___y_1269_);
v___x_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___y_1269_);
lean_ctor_set(v___x_1293_, 2, v___x_1292_);
v___x_1294_ = l_String_Slice_toNat_x3f(v___x_1293_);
lean_dec_ref_known(v___x_1293_, 3);
v___y_1243_ = v___x_1275_;
v___y_1244_ = v_rest_1273_;
v___y_1245_ = v___y_1268_;
v___y_1246_ = v___x_1274_;
v___y_1247_ = v___y_1269_;
v___y_1248_ = v___y_1270_;
v___y_1249_ = v___x_1276_;
v___y_1250_ = v_val_1281_;
v___y_1251_ = v___x_1294_;
goto v___jp_1242_;
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
lean_dec(v___y_1269_);
lean_inc_ref(v_ver_1220_);
v___x_1295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_ver_1220_);
lean_ctor_set(v___x_1295_, 1, v_ver_1220_);
return v___x_1295_;
}
}
else
{
lean_object* v___x_1296_; 
lean_dec(v___x_1271_);
lean_dec(v___y_1269_);
v___x_1296_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___y_1267_);
if (lean_obj_tag(v___x_1296_) == 1)
{
lean_object* v_val_1297_; lean_object* v___x_1298_; 
v_val_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1298_ = l_String_Slice_toNat_x3f(v_val_1297_);
lean_dec(v_val_1297_);
if (lean_obj_tag(v___x_1298_) == 1)
{
if (v___y_1268_ == 0)
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
lean_inc_ref(v_ver_1220_);
v___x_1302_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_ver_1220_);
lean_ctor_set(v___x_1302_, 1, v_ver_1220_);
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; 
lean_dec_ref(v_ver_1220_);
v___x_1303_ = l_Lake_ToolchainVer_pr___override(v_val_1299_);
return v___x_1303_;
}
}
else
{
lean_object* v_val_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v___y_1270_);
lean_dec_ref(v_ver_1220_);
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
lean_inc_ref(v_ver_1220_);
v___x_1306_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_ver_1220_);
lean_ctor_set(v___x_1306_, 1, v_ver_1220_);
return v___x_1306_;
}
}
else
{
lean_object* v___x_1307_; 
lean_dec(v___x_1296_);
lean_inc_ref(v_ver_1220_);
v___x_1307_ = l_Lake_StdVer_parse(v_ver_1220_);
if (lean_obj_tag(v___x_1307_) == 1)
{
if (v___y_1268_ == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1309_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1310_ = lean_string_dec_eq(v___y_1270_, v___x_1309_);
lean_dec_ref(v___y_1270_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
lean_dec(v_a_1308_);
lean_inc_ref(v_ver_1220_);
v___x_1311_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1311_, 0, v_ver_1220_);
lean_ctor_set(v___x_1311_, 1, v_ver_1220_);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; 
lean_dec_ref(v_ver_1220_);
v___x_1312_ = l_Lake_ToolchainVer_release___override(v_a_1308_);
return v___x_1312_;
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1314_; 
lean_dec_ref(v___y_1270_);
lean_dec_ref(v_ver_1220_);
v_a_1313_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1314_ = l_Lake_ToolchainVer_release___override(v_a_1313_);
return v___x_1314_;
}
}
else
{
lean_object* v___x_1315_; 
lean_dec_ref(v___x_1307_);
lean_dec_ref(v___y_1270_);
lean_inc_ref(v_ver_1220_);
v___x_1315_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1315_, 0, v_ver_1220_);
lean_ctor_set(v___x_1315_, 1, v_ver_1220_);
return v___x_1315_;
}
}
}
}
v___jp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v_noOrigin_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1319_ = lean_string_utf8_byte_size(v_fst_1317_);
v___x_1320_ = lean_unsigned_to_nat(0u);
v_noOrigin_1321_ = lean_nat_dec_eq(v___x_1319_, v___x_1320_);
v___x_1322_ = lean_string_utf8_byte_size(v_snd_1318_);
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_nat_dec_le(v___x_1323_, v___x_1322_);
if (v___x_1324_ == 0)
{
v___y_1267_ = v_snd_1318_;
v___y_1268_ = v_noOrigin_1321_;
v___y_1269_ = v___x_1320_;
v___y_1270_ = v_fst_1317_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__1));
v___x_1326_ = lean_string_memcmp(v_snd_1318_, v___x_1325_, v___x_1320_, v___x_1320_, v___x_1323_);
if (v___x_1326_ == 0)
{
v___y_1267_ = v_snd_1318_;
v___y_1268_ = v_noOrigin_1321_;
v___y_1269_ = v___x_1320_;
v___y_1270_ = v_fst_1317_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_inc_ref(v_snd_1318_);
v___x_1327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1327_, 0, v_snd_1318_);
lean_ctor_set(v___x_1327_, 1, v___x_1320_);
lean_ctor_set(v___x_1327_, 2, v___x_1322_);
v___x_1328_ = l_String_Slice_Pos_nextn(v___x_1327_, v___x_1320_, v___x_1323_);
lean_dec_ref_known(v___x_1327_, 3);
v___x_1329_ = lean_string_utf8_extract_fast(v_snd_1318_, v___x_1328_, v___x_1322_);
lean_dec(v___x_1328_);
lean_dec_ref(v_snd_1318_);
v___x_1330_ = l_Lake_StdVer_parse(v___x_1329_);
if (lean_obj_tag(v___x_1330_) == 1)
{
if (v_noOrigin_1321_ == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1332_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1333_ = lean_string_dec_eq(v_fst_1317_, v___x_1332_);
lean_dec_ref(v_fst_1317_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
lean_dec(v_a_1331_);
lean_inc_ref(v_ver_1220_);
v___x_1334_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_ver_1220_);
lean_ctor_set(v___x_1334_, 1, v_ver_1220_);
return v___x_1334_;
}
else
{
lean_object* v___x_1335_; 
lean_dec_ref(v_ver_1220_);
v___x_1335_ = l_Lake_ToolchainVer_release___override(v_a_1331_);
return v___x_1335_;
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1337_; 
lean_dec_ref(v_fst_1317_);
lean_dec_ref(v_ver_1220_);
v_a_1336_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1337_ = l_Lake_ToolchainVer_release___override(v_a_1336_);
return v___x_1337_;
}
}
else
{
lean_object* v___x_1338_; 
lean_dec_ref(v___x_1330_);
lean_dec_ref(v_fst_1317_);
lean_inc_ref(v_ver_1220_);
v___x_1338_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_ver_1220_);
lean_ctor_set(v___x_1338_, 1, v_ver_1220_);
return v___x_1338_;
}
}
}
}
v___jp_1339_:
{
lean_object* v___x_1341_; uint8_t v_decide_1342_; 
v___x_1341_ = lean_string_utf8_byte_size(v_ver_1220_);
v_decide_1342_ = lean_nat_dec_eq(v___y_1340_, v___x_1341_);
if (v_decide_1342_ == 0)
{
lean_object* v_pos_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_pos_1343_ = lean_string_utf8_next_fast(v_ver_1220_, v___y_1340_);
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = lean_string_utf8_extract_fast(v_ver_1220_, v___x_1344_, v___y_1340_);
lean_dec(v___y_1340_);
v___x_1346_ = lean_string_utf8_extract_fast(v_ver_1220_, v_pos_1343_, v___x_1341_);
v_fst_1317_ = v___x_1345_;
v_snd_1318_ = v___x_1346_;
goto v___jp_1316_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v___y_1340_);
v___x_1347_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
lean_inc_ref(v_ver_1220_);
v_fst_1317_ = v___x_1347_;
v_snd_1318_ = v_ver_1220_;
goto v___jp_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(lean_object* v___x_1353_, lean_object* v___x_1354_, lean_object* v_rest_1355_, lean_object* v_inst_1356_, lean_object* v_R_1357_, lean_object* v_a_1358_, lean_object* v_b_1359_, lean_object* v_c_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___x_1353_, v_rest_1355_, v_a_1358_, v_b_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v_rest_1364_, lean_object* v_inst_1365_, lean_object* v_R_1366_, lean_object* v_a_1367_, lean_object* v_b_1368_, lean_object* v_c_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(v___x_1362_, v___x_1363_, v_rest_1364_, v_inst_1365_, v_R_1366_, v_a_1367_, v_b_1368_, v_c_1369_);
lean_dec_ref(v_rest_1364_);
lean_dec_ref(v___x_1363_);
lean_dec(v___x_1362_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(lean_object* v___x_1371_, lean_object* v___x_1372_, lean_object* v_ver_1373_, lean_object* v_inst_1374_, lean_object* v_R_1375_, lean_object* v_a_1376_, lean_object* v_b_1377_, lean_object* v_c_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_1371_, v_ver_1373_, v_a_1376_, v_b_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___boxed(lean_object* v___x_1380_, lean_object* v___x_1381_, lean_object* v_ver_1382_, lean_object* v_inst_1383_, lean_object* v_R_1384_, lean_object* v_a_1385_, lean_object* v_b_1386_, lean_object* v_c_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(v___x_1380_, v___x_1381_, v_ver_1382_, v_inst_1383_, v_R_1384_, v_a_1385_, v_b_1386_, v_c_1387_);
lean_dec(v_b_1386_);
lean_dec_ref(v_ver_1382_);
lean_dec_ref(v___x_1381_);
lean_dec(v___x_1380_);
return v_res_1388_;
}
}
lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object* v_toolchainFile_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_IO_FS_readFile(v_toolchainFile_1389_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1409_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1409_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1409_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_str_1400_; lean_object* v_startInclusive_1401_; lean_object* v_endExclusive_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_string_utf8_byte_size(v_a_1392_);
v___x_1398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1398_, 0, v_a_1392_);
lean_ctor_set(v___x_1398_, 1, v___x_1396_);
lean_ctor_set(v___x_1398_, 2, v___x_1397_);
v___x_1399_ = l_String_Slice_trimAscii(v___x_1398_);
v_str_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc_ref(v_str_1400_);
v_startInclusive_1401_ = lean_ctor_get(v___x_1399_, 1);
lean_inc(v_startInclusive_1401_);
v_endExclusive_1402_ = lean_ctor_get(v___x_1399_, 2);
lean_inc(v_endExclusive_1402_);
lean_dec_ref(v___x_1399_);
v___x_1403_ = lean_string_utf8_extract_fast(v_str_1400_, v_startInclusive_1401_, v_endExclusive_1402_);
lean_dec(v_endExclusive_1402_);
lean_dec(v_startInclusive_1401_);
lean_dec_ref(v_str_1400_);
v___x_1404_ = l_Lake_ToolchainVer_ofString(v___x_1403_);
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1405_);
v___x_1407_ = v___x_1394_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1421_; 
v_a_1410_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1412_ = v___x_1391_;
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1391_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
if (lean_obj_tag(v_a_1410_) == 11)
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
lean_dec_ref_known(v_a_1410_, 2);
v___x_1414_ = lean_box(0);
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1414_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
else
{
lean_object* v___x_1419_; 
if (v_isShared_1413_ == 0)
{
v___x_1419_ = v___x_1412_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1410_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_ToolchainVer_ofFile_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_toolchainFile_1389_ = stack[0].m_obj;
lean_object* v_res_1422_;
v_res_1422_ = l_Lake_ToolchainVer_ofFile_x3f(v_toolchainFile_1389_);
stack->m_obj
 = v_res_1422_;
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f___boxed(lean_object* v_toolchainFile_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lake_ToolchainVer_ofFile_x3f(v_toolchainFile_1423_);
lean_dec_ref(v_toolchainFile_1423_);
return v_res_1425_;
}
}
lean_object* l_Lake_ToolchainVer_ofDir_x3f(lean_object* v_dir_1426_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = ((lean_object*)(l_Lake_toolchainFileName___closed__0));
v___x_1429_ = l_System_FilePath_join(v_dir_1426_, v___x_1428_);
v___x_1430_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1429_);
lean_dec_ref(v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT void l_Lake_ToolchainVer_ofDir_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_dir_1426_ = stack[0].m_obj;
lean_object* v_res_1431_;
v_res_1431_ = l_Lake_ToolchainVer_ofDir_x3f(v_dir_1426_);
stack->m_obj
 = v_res_1431_;
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
uint8_t l_Lake_ToolchainVer_blt(lean_object* v_a_1465_, lean_object* v_b_1466_){
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
LEAN_EXPORT void l_Lake_ToolchainVer_blt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1465_ = stack[0].m_obj;
lean_object* v_b_1466_ = stack[1].m_obj;
uint8_t v_res_1490_;
v_res_1490_ = l_Lake_ToolchainVer_blt(v_a_1465_, v_b_1466_);
stack->m_num = v_res_1490_;
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_blt___boxed(lean_object* v_a_1491_, lean_object* v_b_1492_){
_start:
{
uint8_t v_res_1493_; lean_object* v_r_1494_; 
v_res_1493_ = l_Lake_ToolchainVer_blt(v_a_1491_, v_b_1492_);
lean_dec_ref(v_b_1492_);
lean_dec_ref(v_a_1491_);
v_r_1494_ = lean_box(v_res_1493_);
return v_r_1494_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLT(void){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_box(0);
return v___x_1495_;
}
}
uint8_t l_Lake_ToolchainVer_decLt(lean_object* v_a_1496_, lean_object* v_b_1497_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = l_Lake_ToolchainVer_blt(v_a_1496_, v_b_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT void l_Lake_ToolchainVer_decLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1496_ = stack[0].m_obj;
lean_object* v_b_1497_ = stack[1].m_obj;
uint8_t v_res_1499_;
v_res_1499_ = l_Lake_ToolchainVer_decLt(v_a_1496_, v_b_1497_);
stack->m_num = v_res_1499_;
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLt___boxed(lean_object* v_a_1500_, lean_object* v_b_1501_){
_start:
{
uint8_t v_res_1502_; lean_object* v_r_1503_; 
v_res_1502_ = l_Lake_ToolchainVer_decLt(v_a_1500_, v_b_1501_);
lean_dec_ref(v_b_1501_);
lean_dec_ref(v_a_1500_);
v_r_1503_ = lean_box(v_res_1502_);
return v_r_1503_;
}
}
uint8_t l_Lake_ToolchainVer_ble(lean_object* v_a_1504_, lean_object* v_b_1505_){
_start:
{
switch(lean_obj_tag(v_a_1504_))
{
case 0:
{
if (lean_obj_tag(v_b_1505_) == 0)
{
lean_object* v_ver_1506_; lean_object* v_ver_1507_; uint8_t v___x_1508_; 
v_ver_1506_ = lean_ctor_get(v_a_1504_, 1);
v_ver_1507_ = lean_ctor_get(v_b_1505_, 1);
v___x_1508_ = l_Lake_StdVer_compare(v_ver_1506_, v_ver_1507_);
if (v___x_1508_ == 2)
{
uint8_t v___x_1509_; 
v___x_1509_ = 0;
return v___x_1509_;
}
else
{
uint8_t v___x_1510_; 
v___x_1510_ = 1;
return v___x_1510_;
}
}
else
{
uint8_t v___x_1511_; 
v___x_1511_ = 0;
return v___x_1511_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1505_) == 1)
{
lean_object* v_date_1512_; lean_object* v_rev_1513_; lean_object* v_date_1514_; lean_object* v_rev_1515_; lean_object* v___y_1517_; uint8_t v___x_1522_; 
v_date_1512_ = lean_ctor_get(v_a_1504_, 1);
v_rev_1513_ = lean_ctor_get(v_a_1504_, 2);
v_date_1514_ = lean_ctor_get(v_b_1505_, 1);
v_rev_1515_ = lean_ctor_get(v_b_1505_, 2);
v___x_1522_ = l_Lake_instOrdDate_ord(v_date_1512_, v_date_1514_);
if (v___x_1522_ == 0)
{
uint8_t v___x_1523_; 
v___x_1523_ = 1;
return v___x_1523_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = l_Lake_instDecidableEqDate_decEq(v_date_1512_, v_date_1514_);
if (v___x_1524_ == 0)
{
return v___x_1524_;
}
else
{
if (lean_obj_tag(v_rev_1513_) == 0)
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_unsigned_to_nat(0u);
v___y_1517_ = v___x_1525_;
goto v___jp_1516_;
}
else
{
lean_object* v_val_1526_; 
v_val_1526_ = lean_ctor_get(v_rev_1513_, 0);
v___y_1517_ = v_val_1526_;
goto v___jp_1516_;
}
}
}
v___jp_1516_:
{
if (lean_obj_tag(v_rev_1515_) == 0)
{
lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = lean_nat_dec_le(v___y_1517_, v___x_1518_);
return v___x_1519_;
}
else
{
lean_object* v_val_1520_; uint8_t v___x_1521_; 
v_val_1520_ = lean_ctor_get(v_rev_1515_, 0);
v___x_1521_ = lean_nat_dec_le(v___y_1517_, v_val_1520_);
return v___x_1521_;
}
}
}
else
{
uint8_t v___x_1527_; 
v___x_1527_ = 0;
return v___x_1527_;
}
}
case 2:
{
if (lean_obj_tag(v_b_1505_) == 2)
{
lean_object* v_n_1528_; lean_object* v_n_1529_; uint8_t v___x_1530_; 
v_n_1528_ = lean_ctor_get(v_a_1504_, 1);
v_n_1529_ = lean_ctor_get(v_b_1505_, 1);
v___x_1530_ = lean_nat_dec_eq(v_n_1528_, v_n_1529_);
return v___x_1530_;
}
else
{
uint8_t v___x_1531_; 
v___x_1531_ = 0;
return v___x_1531_;
}
}
default: 
{
if (lean_obj_tag(v_b_1505_) == 3)
{
lean_object* v_v_1532_; lean_object* v_v_1533_; uint8_t v___x_1534_; 
v_v_1532_ = lean_ctor_get(v_a_1504_, 1);
v_v_1533_ = lean_ctor_get(v_b_1505_, 1);
v___x_1534_ = lean_string_dec_eq(v_v_1532_, v_v_1533_);
return v___x_1534_;
}
else
{
uint8_t v___x_1535_; 
v___x_1535_ = 0;
return v___x_1535_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_ToolchainVer_ble_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1504_ = stack[0].m_obj;
lean_object* v_b_1505_ = stack[1].m_obj;
uint8_t v_res_1536_;
v_res_1536_ = l_Lake_ToolchainVer_ble(v_a_1504_, v_b_1505_);
stack->m_num = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ble___boxed(lean_object* v_a_1537_, lean_object* v_b_1538_){
_start:
{
uint8_t v_res_1539_; lean_object* v_r_1540_; 
v_res_1539_ = l_Lake_ToolchainVer_ble(v_a_1537_, v_b_1538_);
lean_dec_ref(v_b_1538_);
lean_dec_ref(v_a_1537_);
v_r_1540_ = lean_box(v_res_1539_);
return v_r_1540_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLE(void){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_box(0);
return v___x_1541_;
}
}
uint8_t l_Lake_ToolchainVer_decLe(lean_object* v_a_1542_, lean_object* v_b_1543_){
_start:
{
uint8_t v___x_1544_; 
v___x_1544_ = l_Lake_ToolchainVer_ble(v_a_1542_, v_b_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT void l_Lake_ToolchainVer_decLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1542_ = stack[0].m_obj;
lean_object* v_b_1543_ = stack[1].m_obj;
uint8_t v_res_1545_;
v_res_1545_ = l_Lake_ToolchainVer_decLe(v_a_1542_, v_b_1543_);
stack->m_num = v_res_1545_;
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLe___boxed(lean_object* v_a_1546_, lean_object* v_b_1547_){
_start:
{
uint8_t v_res_1548_; lean_object* v_r_1549_; 
v_res_1548_ = l_Lake_ToolchainVer_decLe(v_a_1546_, v_b_1547_);
lean_dec_ref(v_b_1547_);
lean_dec_ref(v_a_1546_);
v_r_1549_ = lean_box(v_res_1548_);
return v_r_1549_;
}
}
LEAN_EXPORT lean_object* l_Lake_normalizeToolchain(lean_object* v_s_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v_toString_1552_; 
v___x_1551_ = l_Lake_ToolchainVer_ofString(v_s_1550_);
v_toString_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc_ref(v_toString_1552_);
lean_dec_ref(v___x_1551_);
return v_toString_1552_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeVersionToolchainVer___lam__0(lean_object* v_x_1557_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = l_Lake_ToolchainVer_ofString(v_x_1557_);
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
lean_object* l_Lake_ComparatorOp_ctorIdx___impl(uint8_t v_x_1562_){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_box(v_x_1562_);
v___x_1564_ = lean_obj_tag_nat(v___x_1563_);
lean_dec(v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT void l_Lake_ComparatorOp_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1562_ = stack[0].m_num;
lean_object* v_res_1565_;
v_res_1565_ = l_Lake_ComparatorOp_ctorIdx___impl(v_x_1562_);
stack->m_obj
 = v_res_1565_;
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___impl___boxed(lean_object* v_x_1566_){
_start:
{
uint8_t v_x_4__boxed_1567_; lean_object* v_res_1568_; 
v_x_4__boxed_1567_ = lean_unbox(v_x_1566_);
v_res_1568_ = l_Lake_ComparatorOp_ctorIdx___impl(v_x_4__boxed_1567_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg(lean_object* v_k_1569_){
_start:
{
lean_inc(v_k_1569_);
return v_k_1569_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg___boxed(lean_object* v_k_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lake_ComparatorOp_ctorElim___redArg(v_k_1570_);
lean_dec(v_k_1570_);
return v_res_1571_;
}
}
lean_object* l_Lake_ComparatorOp_ctorElim(lean_object* v_motive_1572_, lean_object* v_ctorIdx_1573_, uint8_t v_t_1574_, lean_object* v_h_1575_, lean_object* v_k_1576_){
_start:
{
lean_inc(v_k_1576_);
return v_k_1576_;
}
}
LEAN_EXPORT void l_Lake_ComparatorOp_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_1573_ = stack[1].m_obj;
uint8_t v_t_1574_ = stack[2].m_num;
lean_object* v_k_1576_ = stack[4].m_obj;
lean_object* v_res_1577_;
v_res_1577_ = l_Lake_ComparatorOp_ctorElim(lean_box(0), v_ctorIdx_1573_, v_t_1574_, lean_box(0), v_k_1576_);
stack->m_obj
 = v_res_1577_;
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___boxed(lean_object* v_motive_1578_, lean_object* v_ctorIdx_1579_, lean_object* v_t_1580_, lean_object* v_h_1581_, lean_object* v_k_1582_){
_start:
{
uint8_t v_t_boxed_1583_; lean_object* v_res_1584_; 
v_t_boxed_1583_ = lean_unbox(v_t_1580_);
v_res_1584_ = l_Lake_ComparatorOp_ctorElim(v_motive_1578_, v_ctorIdx_1579_, v_t_boxed_1583_, v_h_1581_, v_k_1582_);
lean_dec(v_k_1582_);
lean_dec(v_ctorIdx_1579_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg(lean_object* v_lt_1585_){
_start:
{
lean_inc(v_lt_1585_);
return v_lt_1585_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg___boxed(lean_object* v_lt_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lake_ComparatorOp_lt_elim___redArg(v_lt_1586_);
lean_dec(v_lt_1586_);
return v_res_1587_;
}
}
lean_object* l_Lake_ComparatorOp_lt_elim(lean_object* v_motive_1588_, uint8_t v_t_1589_, lean_object* v_h_1590_, lean_object* v_lt_1591_){
_start:
{
lean_inc(v_lt_1591_);
return v_lt_1591_;
}
}
LEAN_EXPORT void l_Lake_ComparatorOp_lt_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1589_ = stack[1].m_num;
lean_object* v_lt_1591_ = stack[3].m_obj;
lean_object* v_res_1592_;
v_res_1592_ = l_Lake_ComparatorOp_lt_elim(lean_box(0), v_t_1589_, lean_box(0), v_lt_1591_);
stack->m_obj
 = v_res_1592_;
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___boxed(lean_object* v_motive_1593_, lean_object* v_t_1594_, lean_object* v_h_1595_, lean_object* v_lt_1596_){
_start:
{
uint8_t v_t_boxed_1597_; lean_object* v_res_1598_; 
v_t_boxed_1597_ = lean_unbox(v_t_1594_);
v_res_1598_ = l_Lake_ComparatorOp_lt_elim(v_motive_1593_, v_t_boxed_1597_, v_h_1595_, v_lt_1596_);
lean_dec(v_lt_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg(lean_object* v_le_1599_){
_start:
{
lean_inc(v_le_1599_);
return v_le_1599_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg___boxed(lean_object* v_le_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lake_ComparatorOp_le_elim___redArg(v_le_1600_);
lean_dec(v_le_1600_);
return v_res_1601_;
}
}
lean_object* l_Lake_ComparatorOp_le_elim(lean_object* v_motive_1602_, uint8_t v_t_1603_, lean_object* v_h_1604_, lean_object* v_le_1605_){
_start:
{
lean_inc(v_le_1605_);
return v_le_1605_;
}
}
LEAN_EXPORT void l_Lake_ComparatorOp_le_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1603_ = stack[1].m_num;
lean_object* v_le_1605_ = stack[3].m_obj;
lean_object* v_res_1606_;
v_res_1606_ = l_Lake_ComparatorOp_le_elim(lean_box(0), v_t_1603_, lean_box(0), v_le_1605_);
stack->m_obj
 = v_res_1606_;
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___boxed(lean_object* v_motive_1607_, lean_object* v_t_1608_, lean_object* v_h_1609_, lean_object* v_le_1610_){
_start:
{
uint8_t v_t_boxed_1611_; lean_object* v_res_1612_; 
v_t_boxed_1611_ = lean_unbox(v_t_1608_);
v_res_1612_ = l_Lake_ComparatorOp_le_elim(v_motive_1607_, v_t_boxed_1611_, v_h_1609_, v_le_1610_);
lean_dec(v_le_1610_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg(lean_object* v_gt_1613_){
_start:
{
lean_inc(v_gt_1613_);
return v_gt_1613_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg___boxed(lean_object* v_gt_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lake_ComparatorOp_gt_elim___redArg(v_gt_1614_);
lean_dec(v_gt_1614_);
return v_res_1615_;
}
}
lean_object* l_Lake_ComparatorOp_gt_elim(lean_object* v_motive_1616_, uint8_t v_t_1617_, lean_object* v_h_1618_, lean_object* v_gt_1619_){
_start:
{
lean_inc(v_gt_1619_);
return v_gt_1619_;
}
}
LEAN_EXPORT void l_Lake_ComparatorOp_gt_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1617_ = stack[1].m_num;
lean_object* v_gt_1619_ = stack[3].m_obj;
lean_object* v_res_1620_;
v_res_1620_ = l_Lake_ComparatorOp_gt_elim(lean_box(0), v_t_1617_, lean_box(0), v_gt_1619_);
stack->m_obj
 = v_res_1620_;
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
lean_object* l_Lake_ComparatorOp_ge_elim(lean_object* v_motive_1630_, uint8_t v_t_1631_, lean_object* v_h_1632_, lean_object* v_ge_1633_){
_start:
{
lean_inc(v_ge_1633_);
return v_ge_1633_;
}
}
LEAN_EXPORT void l_Lake_ComparatorOp_ge_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1631_ = stack[1].m_num;
lean_object* v_ge_1633_ = stack[3].m_obj;
lean_object* v_res_1634_;
v_res_1634_ = l_Lake_ComparatorOp_ge_elim(lean_box(0), v_t_1631_, lean_box(0), v_ge_1633_);
stack->m_obj
 = v_res_1634_;
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___boxed(lean_object* v_motive_1635_, lean_object* v_t_1636_, lean_object* v_h_1637_, lean_object* v_ge_1638_){
_start:
{
uint8_t v_t_boxed_1639_; lean_object* v_res_1640_; 
v_t_boxed_1639_ = lean_unbox(v_t_1636_);
v_res_1640_ = l_Lake_ComparatorOp_ge_elim(v_motive_1635_, v_t_boxed_1639_, v_h_1637_, v_ge_1638_);
lean_dec(v_ge_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg(lean_object* v_eq_1641_){
_start:
{
lean_inc(v_eq_1641_);
return v_eq_1641_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg___boxed(lean_object* v_eq_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lake_ComparatorOp_eq_elim___redArg(v_eq_1642_);
lean_dec(v_eq_1642_);
return v_res_1643_;
}
}
lean_object* l_Lake_ComparatorOp_eq_elim(lean_object* v_motive_1644_, uint8_t v_t_1645_, lean_object* v_h_1646_, lean_object* v_eq_1647_){
_start:
{
lean_inc(v_eq_1647_);
return v_eq_1647_;
}
}
LEAN_EXPORT void l_Lake_ComparatorOp_eq_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1645_ = stack[1].m_num;
lean_object* v_eq_1647_ = stack[3].m_obj;
lean_object* v_res_1648_;
v_res_1648_ = l_Lake_ComparatorOp_eq_elim(lean_box(0), v_t_1645_, lean_box(0), v_eq_1647_);
stack->m_obj
 = v_res_1648_;
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___boxed(lean_object* v_motive_1649_, lean_object* v_t_1650_, lean_object* v_h_1651_, lean_object* v_eq_1652_){
_start:
{
uint8_t v_t_boxed_1653_; lean_object* v_res_1654_; 
v_t_boxed_1653_ = lean_unbox(v_t_1650_);
v_res_1654_ = l_Lake_ComparatorOp_eq_elim(v_motive_1649_, v_t_boxed_1653_, v_h_1651_, v_eq_1652_);
lean_dec(v_eq_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg(lean_object* v_ne_1655_){
_start:
{
lean_inc(v_ne_1655_);
return v_ne_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg___boxed(lean_object* v_ne_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lake_ComparatorOp_ne_elim___redArg(v_ne_1656_);
lean_dec(v_ne_1656_);
return v_res_1657_;
}
}
lean_object* l_Lake_ComparatorOp_ne_elim(lean_object* v_motive_1658_, uint8_t v_t_1659_, lean_object* v_h_1660_, lean_object* v_ne_1661_){
_start:
{
lean_inc(v_ne_1661_);
return v_ne_1661_;
}
}
LEAN_EXPORT void l_Lake_ComparatorOp_ne_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1659_ = stack[1].m_num;
lean_object* v_ne_1661_ = stack[3].m_obj;
lean_object* v_res_1662_;
v_res_1662_ = l_Lake_ComparatorOp_ne_elim(lean_box(0), v_t_1659_, lean_box(0), v_ne_1661_);
stack->m_obj
 = v_res_1662_;
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
lean_object* l_Lake_instReprComparatorOp_repr(uint8_t v_x_1687_, lean_object* v_prec_1688_){
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
LEAN_EXPORT void l_Lake_instReprComparatorOp_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1687_ = stack[0].m_num;
lean_object* v_prec_1688_ = stack[1].m_obj;
lean_object* v_res_1755_;
v_res_1755_ = l_Lake_instReprComparatorOp_repr(v_x_1687_, v_prec_1688_);
stack->m_obj
 = v_res_1755_;
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr___boxed(lean_object* v_x_1756_, lean_object* v_prec_1757_){
_start:
{
uint8_t v_x_329__boxed_1758_; lean_object* v_res_1759_; 
v_x_329__boxed_1758_ = lean_unbox(v_x_1756_);
v_res_1759_ = l_Lake_instReprComparatorOp_repr(v_x_329__boxed_1758_, v_prec_1757_);
lean_dec(v_prec_1757_);
return v_res_1759_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp_default(void){
_start:
{
uint8_t v___x_1762_; 
v___x_1762_ = 0;
return v___x_1762_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp(void){
_start:
{
uint8_t v___x_1763_; 
v___x_1763_ = 0;
return v___x_1763_;
}
}
lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(lean_object* v_sym_1764_, uint8_t v_cmp_1765_, lean_object* v_t_1766_){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = lean_box(v_cmp_1765_);
lean_inc_ref(v_sym_1764_);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v_sym_1764_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_Data_Trie_insert___redArg(v_t_1766_, v_sym_1764_, v___x_1768_);
lean_dec_ref(v_sym_1764_);
return v___x_1769_;
}
}
LEAN_EXPORT void l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sym_1764_ = stack[0].m_obj;
uint8_t v_cmp_1765_ = stack[1].m_num;
lean_object* v_t_1766_ = stack[2].m_obj;
lean_object* v_res_1770_;
v_res_1770_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v_sym_1764_, v_cmp_1765_, v_t_1766_);
stack->m_obj
 = v_res_1770_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0___boxed(lean_object* v_sym_1771_, lean_object* v_cmp_1772_, lean_object* v_t_1773_){
_start:
{
uint8_t v_cmp_boxed_1774_; lean_object* v_res_1775_; 
v_cmp_boxed_1774_ = lean_unbox(v_cmp_1772_);
v_res_1775_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v_sym_1771_, v_cmp_boxed_1774_, v_t_1773_);
return v_res_1775_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9(void){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_Data_Trie_empty___redArg();
return v___x_1785_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10(void){
_start:
{
lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1786_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9);
v___x_1787_ = 0;
v___x_1788_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
v___x_1789_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1788_, v___x_1787_, v___x_1786_);
return v___x_1789_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11(void){
_start:
{
lean_object* v___x_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1790_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10);
v___x_1791_ = 1;
v___x_1792_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7));
v___x_1793_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1792_, v___x_1791_, v___x_1790_);
return v___x_1793_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12(void){
_start:
{
lean_object* v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11);
v___x_1795_ = 1;
v___x_1796_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
v___x_1797_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1796_, v___x_1795_, v___x_1794_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13(void){
_start:
{
lean_object* v___x_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1798_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12);
v___x_1799_ = 2;
v___x_1800_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
v___x_1801_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1800_, v___x_1799_, v___x_1798_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14(void){
_start:
{
lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13);
v___x_1803_ = 3;
v___x_1804_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4));
v___x_1805_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1804_, v___x_1803_, v___x_1802_);
return v___x_1805_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15(void){
_start:
{
lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1806_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14);
v___x_1807_ = 3;
v___x_1808_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
v___x_1809_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1808_, v___x_1807_, v___x_1806_);
return v___x_1809_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16(void){
_start:
{
lean_object* v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1810_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15);
v___x_1811_ = 4;
v___x_1812_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
v___x_1813_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1812_, v___x_1811_, v___x_1810_);
return v___x_1813_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17(void){
_start:
{
lean_object* v___x_1814_; uint8_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1814_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16);
v___x_1815_ = 5;
v___x_1816_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1));
v___x_1817_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1816_, v___x_1815_, v___x_1814_);
return v___x_1817_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18(void){
_start:
{
lean_object* v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1818_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17);
v___x_1819_ = 5;
v___x_1820_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
v___x_1821_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1820_, v___x_1819_, v___x_1818_);
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie(void){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(lean_object* v_s_1825_, lean_object* v_p_1826_){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie;
v___x_1828_ = lean_string_utf8_byte_size(v_s_1825_);
lean_inc(v_p_1826_);
v___x_1829_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_1825_, v___x_1827_, v_p_1826_, v___x_1828_);
if (lean_obj_tag(v___x_1829_) == 1)
{
lean_object* v_val_1830_; lean_object* v_fst_1831_; lean_object* v_snd_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1846_; 
v_val_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_val_1830_);
lean_dec_ref_known(v___x_1829_, 1);
v_fst_1831_ = lean_ctor_get(v_val_1830_, 0);
v_snd_1832_ = lean_ctor_get(v_val_1830_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_val_1830_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1834_ = v_val_1830_;
v_isShared_1835_ = v_isSharedCheck_1846_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_snd_1832_);
lean_inc(v_fst_1831_);
lean_dec(v_val_1830_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1846_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v_p_x27_1837_; uint8_t v___x_1838_; 
v___x_1836_ = lean_string_utf8_byte_size(v_fst_1831_);
lean_dec(v_fst_1831_);
v_p_x27_1837_ = lean_nat_add(v_p_1826_, v___x_1836_);
v___x_1838_ = lean_string_is_valid_pos(v_s_1825_, v_p_x27_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_dec(v_p_x27_1837_);
lean_dec(v_snd_1832_);
v___x_1839_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0));
if (v_isShared_1835_ == 0)
{
lean_ctor_set_tag(v___x_1834_, 1);
lean_ctor_set(v___x_1834_, 1, v_p_1826_);
lean_ctor_set(v___x_1834_, 0, v___x_1839_);
v___x_1841_ = v___x_1834_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_p_1826_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
else
{
lean_object* v___x_1844_; 
lean_dec(v_p_1826_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v_p_x27_1837_);
lean_ctor_set(v___x_1834_, 0, v_snd_1832_);
v___x_1844_ = v___x_1834_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_snd_1832_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_p_x27_1837_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec(v___x_1829_);
v___x_1847_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1));
v___x_1848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v_p_1826_);
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___boxed(lean_object* v_s_1849_, lean_object* v_p_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1849_, v_p_1850_);
lean_dec_ref(v_s_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f(lean_object* v_s_1852_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1852_, v___x_1853_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v_a_1856_; lean_object* v___x_1857_; uint8_t v_decide_1858_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
v_a_1856_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1854_, 2);
v___x_1857_ = lean_string_utf8_byte_size(v_s_1852_);
v_decide_1858_ = lean_nat_dec_eq(v_a_1856_, v___x_1857_);
lean_dec(v_a_1856_);
if (v_decide_1858_ == 0)
{
lean_object* v___x_1859_; 
lean_dec(v_a_1855_);
v___x_1859_ = lean_box(0);
return v___x_1859_;
}
else
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_a_1855_);
return v___x_1860_;
}
}
else
{
lean_object* v___x_1861_; 
lean_dec_ref_known(v___x_1854_, 2);
v___x_1861_ = lean_box(0);
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f___boxed(lean_object* v_s_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lake_ComparatorOp_ofString_x3f(v_s_1862_);
lean_dec_ref(v_s_1862_);
return v_res_1863_;
}
}
lean_object* l_Lake_ComparatorOp_toString(uint8_t v_self_1864_){
_start:
{
switch(v_self_1864_)
{
case 0:
{
lean_object* v___x_1865_; 
v___x_1865_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
return v___x_1865_;
}
case 1:
{
lean_object* v___x_1866_; 
v___x_1866_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
return v___x_1866_;
}
case 2:
{
lean_object* v___x_1867_; 
v___x_1867_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
return v___x_1867_;
}
case 3:
{
lean_object* v___x_1868_; 
v___x_1868_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
return v___x_1868_;
}
case 4:
{
lean_object* v___x_1869_; 
v___x_1869_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
return v___x_1869_;
}
default: 
{
lean_object* v___x_1870_; 
v___x_1870_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
return v___x_1870_;
}
}
}
}
LEAN_EXPORT void l_Lake_ComparatorOp_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_self_1864_ = stack[0].m_num;
lean_object* v_res_1871_;
v_res_1871_ = l_Lake_ComparatorOp_toString(v_self_1864_);
stack->m_obj
 = v_res_1871_;
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString___boxed(lean_object* v_self_1872_){
_start:
{
uint8_t v_self_boxed_1873_; lean_object* v_res_1874_; 
v_self_boxed_1873_ = lean_unbox(v_self_1872_);
v_res_1874_ = l_Lake_ComparatorOp_toString(v_self_boxed_1873_);
return v_res_1874_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_unsigned_to_nat(7u);
v___x_1887_ = lean_nat_to_int(v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_unsigned_to_nat(6u);
v___x_1892_ = lean_nat_to_int(v___x_1891_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_unsigned_to_nat(19u);
v___x_1897_ = lean_nat_to_int(v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___redArg(lean_object* v_x_1898_){
_start:
{
lean_object* v_ver_1899_; uint8_t v_op_1900_; uint8_t v_includeSuffixes_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_ver_1899_ = lean_ctor_get(v_x_1898_, 0);
lean_inc_ref(v_ver_1899_);
v_op_1900_ = lean_ctor_get_uint8(v_x_1898_, sizeof(void*)*1);
v_includeSuffixes_1901_ = lean_ctor_get_uint8(v_x_1898_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_1898_);
v___x_1902_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_1903_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__3));
v___x_1904_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__4, &l_Lake_instReprVerComparator_repr___redArg___closed__4_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__4);
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = l_Lake_instReprStdVer_repr___redArg(v_ver_1899_);
v___x_1907_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1904_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = 0;
v___x_1909_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set_uint8(v___x_1909_, sizeof(void*)*1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1903_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_1912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_box(1);
v___x_1914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__6));
v___x_1916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v___x_1902_);
v___x_1918_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__7, &l_Lake_instReprVerComparator_repr___redArg___closed__7_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__7);
v___x_1919_ = l_Lake_instReprComparatorOp_repr(v_op_1900_, v___x_1905_);
v___x_1920_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set_uint8(v___x_1921_, sizeof(void*)*1, v___x_1908_);
v___x_1922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1917_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v___x_1911_);
v___x_1924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v___x_1913_);
v___x_1925_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__9));
v___x_1926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1902_);
v___x_1928_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__10, &l_Lake_instReprVerComparator_repr___redArg___closed__10_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__10);
v___x_1929_ = l_Bool_repr___redArg(v_includeSuffixes_1901_);
v___x_1930_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*1, v___x_1908_);
v___x_1932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1927_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_1934_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_1935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v___x_1932_);
v___x_1936_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_1937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1933_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set_uint8(v___x_1939_, sizeof(void*)*1, v___x_1908_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr(lean_object* v_x_1940_, lean_object* v_prec_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lake_instReprVerComparator_repr___redArg(v_x_1940_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___boxed(lean_object* v_x_1943_, lean_object* v_prec_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lake_instReprVerComparator_repr(v_x_1943_, v_prec_1944_);
lean_dec(v_prec_1944_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(lean_object* v_s_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1961_; 
lean_inc(v_a_1960_);
v___x_1961_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1959_, v_a_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2028_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_a_1963_ = lean_ctor_get(v___x_1961_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1965_ = v___x_1961_;
v_isShared_1966_ = v_isSharedCheck_2028_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2028_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; uint8_t v_decide_1968_; 
v___x_1967_ = lean_string_utf8_byte_size(v_s_1959_);
v_decide_1968_ = lean_nat_dec_eq(v_a_1963_, v___x_1967_);
if (v_decide_1968_ == 0)
{
lean_object* v___x_1969_; 
lean_del_object(v___x_1965_);
lean_dec(v_a_1960_);
lean_inc_ref(v_s_1959_);
v___x_1969_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_1959_, v_a_1963_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v_a_1971_; lean_object* v___x_1972_; lean_object* v_a_1973_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
v_a_1971_ = lean_ctor_get(v___x_1969_, 1);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1969_, 2);
v___x_1972_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_1959_, v_a_1971_);
lean_dec_ref(v_s_1959_);
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
if (lean_obj_tag(v_a_1973_) == 1)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1995_; 
lean_inc_ref(v_a_1973_);
v_a_1974_ = lean_ctor_get(v___x_1972_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1972_, 0);
lean_dec(v_unused_1996_);
v___x_1976_ = v___x_1972_;
v_isShared_1977_ = v_isSharedCheck_1995_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1972_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1995_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_val_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v_val_1978_ = lean_ctor_get(v_a_1973_, 0);
lean_inc(v_val_1978_);
lean_dec_ref_known(v_a_1973_, 1);
v___x_1979_ = lean_string_utf8_byte_size(v_val_1978_);
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_1981_ = lean_nat_dec_eq(v___x_1979_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1986_; 
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v_a_1970_);
lean_ctor_set(v___x_1982_, 1, v_val_1978_);
v___x_1983_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
v___x_1984_ = lean_unbox(v_a_1962_);
lean_dec(v_a_1962_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*1, v___x_1984_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*1 + 1, v___x_1981_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1983_);
v___x_1986_ = v___x_1976_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_a_1974_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1993_; 
lean_dec(v_val_1978_);
v___x_1988_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1970_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
v___x_1991_ = lean_unbox(v_a_1962_);
lean_dec(v_a_1962_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*1, v___x_1991_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*1 + 1, v___x_1981_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1990_);
v___x_1993_ = v___x_1976_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_a_1974_);
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
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2008_; 
v_a_1997_ = lean_ctor_get(v___x_1972_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v___x_1972_, 0);
lean_dec(v_unused_2009_);
v___x_1999_ = v___x_1972_;
v_isShared_2000_ = v_isSharedCheck_2008_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1972_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2008_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2006_; 
v___x_2001_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v_a_1970_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
v___x_2004_ = lean_unbox(v_a_1962_);
lean_dec(v_a_1962_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*1, v___x_2004_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*1 + 1, v_decide_1968_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2003_);
v___x_2006_ = v___x_1999_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_a_1997_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_a_1962_);
lean_dec_ref(v_s_1959_);
v_a_2010_ = lean_ctor_get(v___x_1969_, 0);
v_a_2011_ = lean_ctor_get(v___x_1969_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1969_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_inc(v_a_2010_);
lean_dec(v___x_1969_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2010_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_a_2011_);
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
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_dec(v_a_1962_);
v___x_2019_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0));
v___x_2020_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2020_, 0, v_s_1959_);
lean_ctor_set(v___x_2020_, 1, v_a_1960_);
lean_ctor_set(v___x_2020_, 2, v___x_1967_);
v___x_2021_ = l_String_Slice_toString(v___x_2020_);
lean_dec_ref_known(v___x_2020_, 3);
v___x_2022_ = lean_string_append(v___x_2019_, v___x_2021_);
lean_dec_ref(v___x_2021_);
v___x_2023_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1));
v___x_2024_ = lean_string_append(v___x_2022_, v___x_2023_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 1);
lean_ctor_set(v___x_1965_, 0, v___x_2024_);
v___x_2026_ = v___x_1965_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_a_1963_);
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
lean_object* v_a_2029_; lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_a_1960_);
lean_dec_ref(v_s_1959_);
v_a_2029_ = lean_ctor_get(v___x_1961_, 0);
v_a_2030_ = lean_ctor_get(v___x_1961_, 1);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_1961_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_inc(v_a_2029_);
lean_dec(v___x_1961_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2029_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_parse(lean_object* v_s_2038_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_unsigned_to_nat(0u);
v___x_2040_ = lean_string_utf8_byte_size(v_s_2038_);
lean_inc_ref(v_s_2038_);
v___x_2041_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_2038_, v___x_2039_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v_a_2043_; uint8_t v_decide_2044_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
v_a_2043_ = lean_ctor_get(v___x_2041_, 1);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2041_, 2);
v_decide_2044_ = lean_nat_dec_eq(v_a_2043_, v___x_2040_);
if (v_decide_2044_ == 0)
{
lean_object* v_tail_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec(v_a_2042_);
v_tail_2045_ = lean_string_utf8_extract(v_s_2038_, v_a_2043_, v___x_2040_);
lean_dec(v_a_2043_);
lean_dec_ref(v_s_2038_);
v___x_2046_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_2047_ = lean_string_append(v___x_2046_, v_tail_2045_);
lean_dec_ref(v_tail_2045_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; 
lean_dec(v_a_2043_);
lean_dec_ref(v_s_2038_);
v___x_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_a_2042_);
return v___x_2049_;
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
lean_dec_ref(v_s_2038_);
v_a_2050_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2041_, 2);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_a_2050_);
return v___x_2051_;
}
}
}
uint8_t l_Lake_VerComparator_test(lean_object* v_self_2052_, lean_object* v_ver_2053_){
_start:
{
lean_object* v_ver_2054_; uint8_t v_op_2055_; uint8_t v_includeSuffixes_2056_; lean_object* v_ver_2058_; 
v_ver_2054_ = lean_ctor_get(v_self_2052_, 0);
v_op_2055_ = lean_ctor_get_uint8(v_self_2052_, sizeof(void*)*1);
v_includeSuffixes_2056_ = lean_ctor_get_uint8(v_self_2052_, sizeof(void*)*1 + 1);
if (v_includeSuffixes_2056_ == 0)
{
lean_object* v_toSemVerCore_2075_; lean_object* v_specialDescr_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_toSemVerCore_2075_ = lean_ctor_get(v_ver_2053_, 0);
v_specialDescr_2076_ = lean_ctor_get(v_ver_2053_, 1);
v___x_2077_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_2078_ = lean_string_dec_eq(v_specialDescr_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v_toSemVerCore_2079_; lean_object* v_specialDescr_2080_; uint8_t v___x_2081_; 
v_toSemVerCore_2079_ = lean_ctor_get(v_ver_2054_, 0);
v_specialDescr_2080_ = lean_ctor_get(v_ver_2054_, 1);
v___x_2081_ = lean_string_dec_eq(v_specialDescr_2080_, v___x_2077_);
if (v___x_2081_ == 0)
{
uint8_t v___x_2082_; 
v___x_2082_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_2079_, v_toSemVerCore_2075_);
if (v___x_2082_ == 0)
{
return v___x_2082_;
}
else
{
switch(v_op_2055_)
{
case 0:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_string_dec_lt(v_specialDescr_2076_, v_specialDescr_2080_);
return v___x_2083_;
}
case 1:
{
uint8_t v___x_2084_; 
v___x_2084_ = l_String_decLE(v_specialDescr_2076_, v_specialDescr_2080_);
return v___x_2084_;
}
case 2:
{
uint8_t v___x_2085_; 
v___x_2085_ = lean_string_dec_lt(v_specialDescr_2080_, v_specialDescr_2076_);
return v___x_2085_;
}
case 3:
{
uint8_t v___x_2086_; 
v___x_2086_ = l_String_decLE(v_specialDescr_2080_, v_specialDescr_2076_);
return v___x_2086_;
}
case 4:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_string_dec_eq(v_specialDescr_2076_, v_specialDescr_2080_);
return v___x_2087_;
}
default: 
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_string_dec_eq(v_specialDescr_2076_, v_specialDescr_2080_);
if (v___x_2088_ == 0)
{
return v___x_2082_;
}
else
{
return v___x_2081_;
}
}
}
}
}
else
{
return v_includeSuffixes_2056_;
}
}
else
{
v_ver_2058_ = v_ver_2053_;
goto v___jp_2057_;
}
}
else
{
v_ver_2058_ = v_ver_2053_;
goto v___jp_2057_;
}
v___jp_2057_:
{
switch(v_op_2055_)
{
case 0:
{
uint8_t v___x_2059_; 
v___x_2059_ = l_Lake_StdVer_compare(v_ver_2058_, v_ver_2054_);
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
case 1:
{
uint8_t v___x_2062_; 
v___x_2062_ = l_Lake_StdVer_compare(v_ver_2058_, v_ver_2054_);
if (v___x_2062_ == 2)
{
uint8_t v___x_2063_; 
v___x_2063_ = 0;
return v___x_2063_;
}
else
{
uint8_t v___x_2064_; 
v___x_2064_ = 1;
return v___x_2064_;
}
}
case 2:
{
uint8_t v___x_2065_; 
v___x_2065_ = l_Lake_StdVer_compare(v_ver_2054_, v_ver_2058_);
if (v___x_2065_ == 0)
{
uint8_t v___x_2066_; 
v___x_2066_ = 1;
return v___x_2066_;
}
else
{
uint8_t v___x_2067_; 
v___x_2067_ = 0;
return v___x_2067_;
}
}
case 3:
{
uint8_t v___x_2068_; 
v___x_2068_ = l_Lake_StdVer_compare(v_ver_2054_, v_ver_2058_);
if (v___x_2068_ == 2)
{
uint8_t v___x_2069_; 
v___x_2069_ = 0;
return v___x_2069_;
}
else
{
uint8_t v___x_2070_; 
v___x_2070_ = 1;
return v___x_2070_;
}
}
case 4:
{
uint8_t v___x_2071_; 
v___x_2071_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_2058_, v_ver_2054_);
return v___x_2071_;
}
default: 
{
uint8_t v___x_2072_; 
v___x_2072_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_2058_, v_ver_2054_);
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
}
}
LEAN_EXPORT void l_Lake_VerComparator_test_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_2052_ = stack[0].m_obj;
lean_object* v_ver_2053_ = stack[1].m_obj;
uint8_t v_res_2089_;
v_res_2089_ = l_Lake_VerComparator_test(v_self_2052_, v_ver_2053_);
stack->m_num = v_res_2089_;
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_test___boxed(lean_object* v_self_2090_, lean_object* v_ver_2091_){
_start:
{
uint8_t v_res_2092_; lean_object* v_r_2093_; 
v_res_2092_ = l_Lake_VerComparator_test(v_self_2090_, v_ver_2091_);
lean_dec_ref(v_ver_2091_);
lean_dec_ref(v_self_2090_);
v_r_2093_ = lean_box(v_res_2092_);
return v_r_2093_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_toString(lean_object* v_self_2094_){
_start:
{
lean_object* v_ver_2095_; uint8_t v_op_2096_; uint8_t v_includeSuffixes_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_ver_2095_ = lean_ctor_get(v_self_2094_, 0);
lean_inc_ref(v_ver_2095_);
v_op_2096_ = lean_ctor_get_uint8(v_self_2094_, sizeof(void*)*1);
v_includeSuffixes_2097_ = lean_ctor_get_uint8(v_self_2094_, sizeof(void*)*1 + 1);
lean_dec_ref(v_self_2094_);
v___x_2098_ = l_Lake_ComparatorOp_toString(v_op_2096_);
v___x_2099_ = l_Lake_StdVer_toString(v_ver_2095_);
v___x_2100_ = lean_string_append(v___x_2098_, v___x_2099_);
lean_dec_ref(v___x_2099_);
if (v_includeSuffixes_2097_ == 0)
{
return v___x_2100_;
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_2102_ = lean_string_append(v___x_2100_, v___x_2101_);
return v___x_2102_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_2105_, lean_object* v_x_2106_, lean_object* v_x_2107_){
_start:
{
if (lean_obj_tag(v_x_2107_) == 0)
{
lean_dec(v_x_2105_);
return v_x_2106_;
}
else
{
lean_object* v_head_2108_; lean_object* v_tail_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2119_; 
v_head_2108_ = lean_ctor_get(v_x_2107_, 0);
v_tail_2109_ = lean_ctor_get(v_x_2107_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_x_2107_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2111_ = v_x_2107_;
v_isShared_2112_ = v_isSharedCheck_2119_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_tail_2109_);
lean_inc(v_head_2108_);
lean_dec(v_x_2107_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2119_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
lean_inc(v_x_2105_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set_tag(v___x_2111_, 5);
lean_ctor_set(v___x_2111_, 1, v_x_2105_);
lean_ctor_set(v___x_2111_, 0, v_x_2106_);
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_x_2106_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_x_2105_);
v___x_2114_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2108_);
v___x_2116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v_x_2106_ = v___x_2116_;
v_x_2107_ = v_tail_2109_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_){
_start:
{
if (lean_obj_tag(v_x_2122_) == 0)
{
lean_dec(v_x_2120_);
return v_x_2121_;
}
else
{
lean_object* v_head_2123_; lean_object* v_tail_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2134_; 
v_head_2123_ = lean_ctor_get(v_x_2122_, 0);
v_tail_2124_ = lean_ctor_get(v_x_2122_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_2122_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2126_ = v_x_2122_;
v_isShared_2127_ = v_isSharedCheck_2134_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_tail_2124_);
lean_inc(v_head_2123_);
lean_dec(v_x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2134_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
lean_inc(v_x_2120_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set_tag(v___x_2126_, 5);
lean_ctor_set(v___x_2126_, 1, v_x_2120_);
lean_ctor_set(v___x_2126_, 0, v_x_2121_);
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_x_2121_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_x_2120_);
v___x_2129_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2123_);
v___x_2131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2129_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_2120_, v___x_2131_, v_tail_2124_);
return v___x_2132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(lean_object* v_x_2135_, lean_object* v_x_2136_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 0)
{
lean_object* v___x_2137_; 
lean_dec(v_x_2136_);
v___x_2137_ = lean_box(0);
return v___x_2137_;
}
else
{
lean_object* v_tail_2138_; 
v_tail_2138_ = lean_ctor_get(v_x_2135_, 1);
if (lean_obj_tag(v_tail_2138_) == 0)
{
lean_object* v_head_2139_; lean_object* v___x_2140_; 
lean_dec(v_x_2136_);
v_head_2139_ = lean_ctor_get(v_x_2135_, 0);
lean_inc(v_head_2139_);
lean_dec_ref_known(v_x_2135_, 2);
v___x_2140_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2139_);
return v___x_2140_;
}
else
{
lean_object* v_head_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_inc(v_tail_2138_);
v_head_2141_ = lean_ctor_get(v_x_2135_, 0);
lean_inc(v_head_2141_);
lean_dec_ref_known(v_x_2135_, 2);
v___x_2142_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2141_);
v___x_2143_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(v_x_2136_, v___x_2142_, v_tail_2138_);
return v___x_2143_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0));
v___x_2150_ = lean_string_length(v___x_2149_);
return v___x_2150_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3);
v___x_2152_ = lean_nat_to_int(v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(lean_object* v_xs_2160_){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2161_ = lean_array_get_size(v_xs_2160_);
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = lean_nat_dec_eq(v___x_2161_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2164_ = lean_array_to_list(v_xs_2160_);
v___x_2165_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2166_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(v___x_2164_, v___x_2165_);
v___x_2167_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2168_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___x_2166_);
v___x_2170_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2167_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = l_Std_Format_fill(v___x_2172_);
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; 
lean_dec_ref(v_xs_2160_);
v___x_2174_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(lean_object* v_x_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_){
_start:
{
if (lean_obj_tag(v_x_2177_) == 0)
{
lean_dec(v_x_2175_);
return v_x_2176_;
}
else
{
lean_object* v_head_2178_; lean_object* v_tail_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2189_; 
v_head_2178_ = lean_ctor_get(v_x_2177_, 0);
v_tail_2179_ = lean_ctor_get(v_x_2177_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_x_2177_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2181_ = v_x_2177_;
v_isShared_2182_ = v_isSharedCheck_2189_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_tail_2179_);
lean_inc(v_head_2178_);
lean_dec(v_x_2177_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2189_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
lean_inc(v_x_2175_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set_tag(v___x_2181_, 5);
lean_ctor_set(v___x_2181_, 1, v_x_2175_);
lean_ctor_set(v___x_2181_, 0, v_x_2176_);
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_x_2176_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_x_2175_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2178_);
v___x_2186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2184_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v_x_2176_ = v___x_2186_;
v_x_2177_ = v_tail_2179_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(lean_object* v_x_2190_, lean_object* v_x_2191_){
_start:
{
if (lean_obj_tag(v_x_2190_) == 0)
{
lean_object* v___x_2192_; 
lean_dec(v_x_2191_);
v___x_2192_ = lean_box(0);
return v___x_2192_;
}
else
{
lean_object* v_tail_2193_; 
v_tail_2193_ = lean_ctor_get(v_x_2190_, 1);
if (lean_obj_tag(v_tail_2193_) == 0)
{
lean_object* v_head_2194_; lean_object* v___x_2195_; 
lean_dec(v_x_2191_);
v_head_2194_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_head_2194_);
lean_dec_ref_known(v_x_2190_, 2);
v___x_2195_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2194_);
return v___x_2195_;
}
else
{
lean_object* v_head_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_inc(v_tail_2193_);
v_head_2196_ = lean_ctor_get(v_x_2190_, 0);
lean_inc(v_head_2196_);
lean_dec_ref_known(v_x_2190_, 2);
v___x_2197_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2196_);
v___x_2198_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(v_x_2191_, v___x_2197_, v_tail_2193_);
return v___x_2198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(lean_object* v_xs_2199_){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2200_ = lean_array_get_size(v_xs_2199_);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_nat_dec_eq(v___x_2200_, v___x_2201_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2203_ = lean_array_to_list(v_xs_2199_);
v___x_2204_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2205_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(v___x_2203_, v___x_2204_);
v___x_2206_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2207_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2205_);
v___x_2209_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2206_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = l_Std_Format_fill(v___x_2211_);
return v___x_2212_;
}
else
{
lean_object* v___x_2213_; 
lean_dec_ref(v_xs_2199_);
v___x_2213_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2213_;
}
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_unsigned_to_nat(12u);
v___x_2224_ = lean_nat_to_int(v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_unsigned_to_nat(11u);
v___x_2229_ = lean_nat_to_int(v___x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object* v_x_2230_){
_start:
{
lean_object* v_toString_2231_; lean_object* v_clauses_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2266_; 
v_toString_2231_ = lean_ctor_get(v_x_2230_, 0);
v_clauses_2232_ = lean_ctor_get(v_x_2230_, 1);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_x_2230_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2234_ = v_x_2230_;
v_isShared_2235_ = v_isSharedCheck_2266_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_clauses_2232_);
lean_inc(v_toString_2231_);
lean_dec(v_x_2230_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2266_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2236_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_2237_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__3));
v___x_2238_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__4, &l_Lake_instReprVerRange_repr___redArg___closed__4_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__4);
v___x_2239_ = l_String_quote(v_toString_2231_);
v___x_2240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set_tag(v___x_2234_, 4);
lean_ctor_set(v___x_2234_, 1, v___x_2240_);
lean_ctor_set(v___x_2234_, 0, v___x_2238_);
v___x_2242_ = v___x_2234_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
uint8_t v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2243_ = 0;
v___x_2244_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set_uint8(v___x_2244_, sizeof(void*)*1, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2237_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_2247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2245_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = lean_box(1);
v___x_2249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__6));
v___x_2251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v___x_2236_);
v___x_2253_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__7, &l_Lake_instReprVerRange_repr___redArg___closed__7_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__7);
v___x_2254_ = l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(v_clauses_2232_);
v___x_2255_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*1, v___x_2243_);
v___x_2257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2252_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_2259_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_2260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set(v___x_2260_, 1, v___x_2257_);
v___x_2261_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_2262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2258_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*1, v___x_2243_);
return v___x_2264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr(lean_object* v_x_2267_, lean_object* v_prec_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lake_instReprVerRange_repr___redArg(v_x_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___boxed(lean_object* v_x_2270_, lean_object* v_prec_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lake_instReprVerRange_repr(v_x_2270_, v_prec_2271_);
lean_dec(v_prec_2271_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0(lean_object* v_self_2282_){
_start:
{
lean_object* v_toString_2283_; 
v_toString_2283_ = lean_ctor_get(v_self_2282_, 0);
lean_inc_ref(v_toString_2283_);
return v_toString_2283_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0___boxed(lean_object* v_self_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lake_VerRange_instToString___lam__0(v_self_2284_);
lean_dec_ref(v_self_2284_);
return v_res_2285_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(lean_object* v_as_2289_, size_t v_i_2290_, size_t v_stop_2291_, lean_object* v_b_2292_){
_start:
{
uint8_t v___x_2293_; 
v___x_2293_ = lean_usize_dec_eq(v_i_2290_, v_stop_2291_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; size_t v___x_2299_; size_t v___x_2300_; 
v___x_2294_ = lean_array_uget_borrowed(v_as_2289_, v_i_2290_);
v___x_2295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0));
v___x_2296_ = lean_string_append(v_b_2292_, v___x_2295_);
lean_inc(v___x_2294_);
v___x_2297_ = l_Lake_VerComparator_toString(v___x_2294_);
v___x_2298_ = lean_string_append(v___x_2296_, v___x_2297_);
lean_dec_ref(v___x_2297_);
v___x_2299_ = ((size_t)1ULL);
v___x_2300_ = lean_usize_add(v_i_2290_, v___x_2299_);
v_i_2290_ = v___x_2300_;
v_b_2292_ = v___x_2298_;
goto _start;
}
else
{
return v_b_2292_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2289_ = stack[0].m_obj;
size_t v_i_2290_ = stack[1].m_num;
size_t v_stop_2291_ = stack[2].m_num;
lean_object* v_b_2292_ = stack[3].m_obj;
lean_object* v_res_2302_;
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_as_2289_, v_i_2290_, v_stop_2291_, v_b_2292_);
stack->m_obj
 = v_res_2302_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___boxed(lean_object* v_as_2303_, lean_object* v_i_2304_, lean_object* v_stop_2305_, lean_object* v_b_2306_){
_start:
{
size_t v_i_boxed_2307_; size_t v_stop_boxed_2308_; lean_object* v_res_2309_; 
v_i_boxed_2307_ = lean_unbox_usize(v_i_2304_);
lean_dec(v_i_2304_);
v_stop_boxed_2308_ = lean_unbox_usize(v_stop_2305_);
lean_dec(v_stop_2305_);
v_res_2309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_as_2303_, v_i_boxed_2307_, v_stop_boxed_2308_, v_b_2306_);
lean_dec_ref(v_as_2303_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(lean_object* v_ands_2311_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2312_ = lean_array_get_size(v_ands_2311_);
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = lean_nat_dec_eq(v___x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2315_ = lean_array_fget_borrowed(v_ands_2311_, v___x_2313_);
lean_inc(v___x_2315_);
v___x_2316_ = l_Lake_VerComparator_toString(v___x_2315_);
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_nat_dec_lt(v___x_2317_, v___x_2312_);
if (v___x_2318_ == 0)
{
return v___x_2316_;
}
else
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_nat_dec_le(v___x_2312_, v___x_2312_);
if (v___x_2319_ == 0)
{
if (v___x_2318_ == 0)
{
return v___x_2316_;
}
else
{
size_t v___x_2320_; size_t v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = ((size_t)1ULL);
v___x_2321_ = lean_usize_of_nat(v___x_2312_);
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2311_, v___x_2320_, v___x_2321_, v___x_2316_);
return v___x_2322_;
}
}
else
{
size_t v___x_2323_; size_t v___x_2324_; lean_object* v___x_2325_; 
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_of_nat(v___x_2312_);
v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2311_, v___x_2323_, v___x_2324_, v___x_2316_);
return v___x_2325_;
}
}
}
else
{
lean_object* v___x_2326_; 
v___x_2326_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0));
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___boxed(lean_object* v_ands_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v_ands_2327_);
lean_dec_ref(v_ands_2327_);
return v_res_2328_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(lean_object* v_as_2330_, size_t v_i_2331_, size_t v_stop_2332_, lean_object* v_b_2333_){
_start:
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_usize_dec_eq(v_i_2331_, v_stop_2332_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; size_t v___x_2340_; size_t v___x_2341_; 
v___x_2335_ = lean_array_uget_borrowed(v_as_2330_, v_i_2331_);
v___x_2336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0));
v___x_2337_ = lean_string_append(v_b_2333_, v___x_2336_);
v___x_2338_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2335_);
v___x_2339_ = lean_string_append(v___x_2337_, v___x_2338_);
lean_dec_ref(v___x_2338_);
v___x_2340_ = ((size_t)1ULL);
v___x_2341_ = lean_usize_add(v_i_2331_, v___x_2340_);
v_i_2331_ = v___x_2341_;
v_b_2333_ = v___x_2339_;
goto _start;
}
else
{
return v_b_2333_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2330_ = stack[0].m_obj;
size_t v_i_2331_ = stack[1].m_num;
size_t v_stop_2332_ = stack[2].m_num;
lean_object* v_b_2333_ = stack[3].m_obj;
lean_object* v_res_2343_;
v_res_2343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_as_2330_, v_i_2331_, v_stop_2332_, v_b_2333_);
stack->m_obj
 = v_res_2343_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___boxed(lean_object* v_as_2344_, lean_object* v_i_2345_, lean_object* v_stop_2346_, lean_object* v_b_2347_){
_start:
{
size_t v_i_boxed_2348_; size_t v_stop_boxed_2349_; lean_object* v_res_2350_; 
v_i_boxed_2348_ = lean_unbox_usize(v_i_2345_);
lean_dec(v_i_2345_);
v_stop_boxed_2349_ = lean_unbox_usize(v_stop_2346_);
lean_dec(v_stop_2346_);
v_res_2350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_as_2344_, v_i_boxed_2348_, v_stop_boxed_2349_, v_b_2347_);
lean_dec_ref(v_as_2344_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(lean_object* v_ors_2351_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2352_ = lean_array_get_size(v_ors_2351_);
v___x_2353_ = lean_unsigned_to_nat(0u);
v___x_2354_ = lean_nat_dec_eq(v___x_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2355_ = lean_array_fget_borrowed(v_ors_2351_, v___x_2353_);
v___x_2356_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2355_);
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = lean_nat_dec_lt(v___x_2357_, v___x_2352_);
if (v___x_2358_ == 0)
{
return v___x_2356_;
}
else
{
uint8_t v___x_2359_; 
v___x_2359_ = lean_nat_dec_le(v___x_2352_, v___x_2352_);
if (v___x_2359_ == 0)
{
if (v___x_2358_ == 0)
{
return v___x_2356_;
}
else
{
size_t v___x_2360_; size_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = ((size_t)1ULL);
v___x_2361_ = lean_usize_of_nat(v___x_2352_);
v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2351_, v___x_2360_, v___x_2361_, v___x_2356_);
return v___x_2362_;
}
}
else
{
size_t v___x_2363_; size_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = ((size_t)1ULL);
v___x_2364_ = lean_usize_of_nat(v___x_2352_);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2351_, v___x_2363_, v___x_2364_, v___x_2356_);
return v___x_2365_;
}
}
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs___boxed(lean_object* v_ors_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_ors_2367_);
lean_dec_ref(v_ors_2367_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_ofClauses(lean_object* v_clauses_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_clauses_2369_);
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v_clauses_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_appendRange(lean_object* v_ands_2372_, lean_object* v_minVer_2373_, lean_object* v_maxVer_2374_, lean_object* v_specialDescr_2375_){
_start:
{
lean_object* v_minVer_2376_; lean_object* v___x_2377_; lean_object* v_maxVer_2378_; uint8_t v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v_minVer_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2376_, 0, v_minVer_2373_);
lean_ctor_set(v_minVer_2376_, 1, v_specialDescr_2375_);
v___x_2377_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2378_, 0, v_maxVer_2374_);
lean_ctor_set(v_maxVer_2378_, 1, v___x_2377_);
v___x_2379_ = 3;
v___x_2380_ = 0;
v___x_2381_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2381_, 0, v_minVer_2376_);
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*1, v___x_2379_);
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*1 + 1, v___x_2380_);
v___x_2382_ = lean_array_push(v_ands_2372_, v___x_2381_);
v___x_2383_ = 0;
v___x_2384_ = 1;
v___x_2385_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2385_, 0, v_maxVer_2378_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*1, v___x_2383_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*1 + 1, v___x_2384_);
v___x_2386_ = lean_array_push(v___x_2382_, v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(lean_object* v_s_2389_, lean_object* v_ands_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_a_2395_; lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2567_; 
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2391_);
lean_inc_ref(v_s_2389_);
v___x_2394_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2389_, v___x_2393_, v_a_2391_, v_a_2391_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_a_2396_ = lean_ctor_get(v___x_2394_, 1);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2398_ = v___x_2394_;
v_isShared_2399_ = v_isSharedCheck_2567_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2567_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; 
v___x_2400_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2389_, v_a_2396_);
lean_dec_ref(v_s_2389_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2557_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_a_2402_ = lean_ctor_get(v___x_2400_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2404_ = v___x_2400_;
v_isShared_2405_ = v_isSharedCheck_2557_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2557_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2406_ = lean_array_get_size(v_a_2395_);
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = lean_nat_dec_eq(v___x_2406_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = lean_unsigned_to_nat(2u);
v___x_2410_ = lean_nat_dec_eq(v___x_2406_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2411_ = lean_unsigned_to_nat(3u);
v___x_2412_ = lean_nat_dec_eq(v___x_2406_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
lean_dec(v_a_2401_);
lean_del_object(v___x_2398_);
lean_dec(v_a_2395_);
lean_dec_ref(v_ands_2390_);
v___x_2413_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0));
v___x_2414_ = l_Nat_reprFast(v___x_2406_);
v___x_2415_ = lean_string_append(v___x_2413_, v___x_2414_);
lean_dec_ref(v___x_2414_);
v___x_2416_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2417_ = lean_string_append(v___x_2415_, v___x_2416_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2417_);
v___x_2419_ = v___x_2404_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_a_2402_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_array_fget_borrowed(v_a_2395_, v___x_2392_);
v___x_2422_ = l_String_Slice_toNat_x3f(v___x_2421_);
if (lean_obj_tag(v___x_2422_) == 1)
{
lean_object* v_val_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_val_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_val_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v___x_2424_ = lean_array_fget_borrowed(v_a_2395_, v___x_2407_);
v___x_2425_ = l_String_Slice_toNat_x3f(v___x_2424_);
if (lean_obj_tag(v___x_2425_) == 1)
{
lean_object* v_val_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_val_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_val_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = lean_array_fget(v_a_2395_, v___x_2409_);
lean_dec(v_a_2395_);
v___x_2428_ = l_String_Slice_toNat_x3f(v___x_2427_);
if (lean_obj_tag(v___x_2428_) == 1)
{
lean_object* v_val_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v_minVer_2434_; 
lean_dec(v___x_2427_);
v_val_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_val_2429_);
lean_dec_ref_known(v___x_2428_, 1);
lean_inc(v_val_2426_);
lean_inc(v_val_2423_);
v___x_2430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2430_, 0, v_val_2423_);
lean_ctor_set(v___x_2430_, 1, v_val_2426_);
lean_ctor_set(v___x_2430_, 2, v_val_2429_);
v___x_2431_ = lean_nat_add(v_val_2426_, v___x_2407_);
lean_dec(v_val_2426_);
v___x_2432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2432_, 0, v_val_2423_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
lean_ctor_set(v___x_2432_, 2, v___x_2392_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v_a_2401_);
lean_ctor_set(v___x_2398_, 0, v___x_2430_);
v_minVer_2434_ = v___x_2398_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_a_2401_);
v_minVer_2434_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2435_; lean_object* v_maxVer_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2435_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2436_, 0, v___x_2432_);
lean_ctor_set(v_maxVer_2436_, 1, v___x_2435_);
v___x_2437_ = 3;
v___x_2438_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2438_, 0, v_minVer_2434_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*1, v___x_2437_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*1 + 1, v___x_2410_);
v___x_2439_ = lean_array_push(v_ands_2390_, v___x_2438_);
v___x_2440_ = 0;
v___x_2441_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2441_, 0, v_maxVer_2436_);
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*1, v___x_2440_);
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*1 + 1, v___x_2412_);
v___x_2442_ = lean_array_push(v___x_2439_, v___x_2441_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2442_);
v___x_2444_ = v___x_2404_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_a_2402_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
else
{
lean_object* v_str_2447_; lean_object* v_startInclusive_2448_; lean_object* v_endExclusive_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_dec(v___x_2428_);
lean_dec(v_val_2426_);
lean_dec(v_val_2423_);
lean_dec(v_a_2401_);
lean_del_object(v___x_2398_);
lean_dec_ref(v_ands_2390_);
v_str_2447_ = lean_ctor_get(v___x_2427_, 0);
lean_inc_ref(v_str_2447_);
v_startInclusive_2448_ = lean_ctor_get(v___x_2427_, 1);
lean_inc(v_startInclusive_2448_);
v_endExclusive_2449_ = lean_ctor_get(v___x_2427_, 2);
lean_inc(v_endExclusive_2449_);
lean_dec(v___x_2427_);
v___x_2450_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2451_ = lean_string_utf8_extract_fast(v_str_2447_, v_startInclusive_2448_, v_endExclusive_2449_);
lean_dec(v_endExclusive_2449_);
lean_dec(v_startInclusive_2448_);
lean_dec_ref(v_str_2447_);
v___x_2452_ = lean_string_append(v___x_2450_, v___x_2451_);
lean_dec_ref(v___x_2451_);
v___x_2453_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2454_ = lean_string_append(v___x_2452_, v___x_2453_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2454_);
v___x_2456_ = v___x_2404_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_a_2402_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
else
{
lean_object* v_str_2458_; lean_object* v_startInclusive_2459_; lean_object* v_endExclusive_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_inc(v___x_2424_);
lean_dec(v___x_2425_);
lean_dec(v_val_2423_);
lean_dec(v_a_2401_);
lean_del_object(v___x_2398_);
lean_dec(v_a_2395_);
lean_dec_ref(v_ands_2390_);
v_str_2458_ = lean_ctor_get(v___x_2424_, 0);
lean_inc_ref(v_str_2458_);
v_startInclusive_2459_ = lean_ctor_get(v___x_2424_, 1);
lean_inc(v_startInclusive_2459_);
v_endExclusive_2460_ = lean_ctor_get(v___x_2424_, 2);
lean_inc(v_endExclusive_2460_);
lean_dec(v___x_2424_);
v___x_2461_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2462_ = lean_string_utf8_extract_fast(v_str_2458_, v_startInclusive_2459_, v_endExclusive_2460_);
lean_dec(v_endExclusive_2460_);
lean_dec(v_startInclusive_2459_);
lean_dec_ref(v_str_2458_);
v___x_2463_ = lean_string_append(v___x_2461_, v___x_2462_);
lean_dec_ref(v___x_2462_);
v___x_2464_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2465_ = lean_string_append(v___x_2463_, v___x_2464_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2465_);
v___x_2467_ = v___x_2404_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_a_2402_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
else
{
lean_object* v_str_2469_; lean_object* v_startInclusive_2470_; lean_object* v_endExclusive_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
lean_inc(v___x_2421_);
lean_dec(v___x_2422_);
lean_dec(v_a_2401_);
lean_del_object(v___x_2398_);
lean_dec(v_a_2395_);
lean_dec_ref(v_ands_2390_);
v_str_2469_ = lean_ctor_get(v___x_2421_, 0);
lean_inc_ref(v_str_2469_);
v_startInclusive_2470_ = lean_ctor_get(v___x_2421_, 1);
lean_inc(v_startInclusive_2470_);
v_endExclusive_2471_ = lean_ctor_get(v___x_2421_, 2);
lean_inc(v_endExclusive_2471_);
lean_dec(v___x_2421_);
v___x_2472_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2473_ = lean_string_utf8_extract_fast(v_str_2469_, v_startInclusive_2470_, v_endExclusive_2471_);
lean_dec(v_endExclusive_2471_);
lean_dec(v_startInclusive_2470_);
lean_dec_ref(v_str_2469_);
v___x_2474_ = lean_string_append(v___x_2472_, v___x_2473_);
lean_dec_ref(v___x_2473_);
v___x_2475_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2476_ = lean_string_append(v___x_2474_, v___x_2475_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2476_);
v___x_2478_ = v___x_2404_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_a_2402_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = lean_array_fget_borrowed(v_a_2395_, v___x_2392_);
v___x_2481_ = l_String_Slice_toNat_x3f(v___x_2480_);
if (lean_obj_tag(v___x_2481_) == 1)
{
lean_object* v_val_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_val_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_val_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v___x_2483_ = lean_array_fget(v_a_2395_, v___x_2407_);
lean_dec(v_a_2395_);
v___x_2484_ = l_String_Slice_toNat_x3f(v___x_2483_);
if (lean_obj_tag(v___x_2484_) == 1)
{
lean_object* v_val_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_minVer_2490_; 
lean_dec(v___x_2483_);
v_val_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc_n(v_val_2485_, 2);
lean_dec_ref_known(v___x_2484_, 1);
lean_inc(v_val_2482_);
v___x_2486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2486_, 0, v_val_2482_);
lean_ctor_set(v___x_2486_, 1, v_val_2485_);
lean_ctor_set(v___x_2486_, 2, v___x_2392_);
v___x_2487_ = lean_nat_add(v_val_2485_, v___x_2407_);
lean_dec(v_val_2485_);
v___x_2488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2488_, 0, v_val_2482_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
lean_ctor_set(v___x_2488_, 2, v___x_2392_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v_a_2401_);
lean_ctor_set(v___x_2398_, 0, v___x_2486_);
v_minVer_2490_ = v___x_2398_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_a_2401_);
v_minVer_2490_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2491_; lean_object* v_maxVer_2492_; uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2491_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2492_, 0, v___x_2488_);
lean_ctor_set(v_maxVer_2492_, 1, v___x_2491_);
v___x_2493_ = 3;
v___x_2494_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2494_, 0, v_minVer_2490_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*1, v___x_2493_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*1 + 1, v___x_2408_);
v___x_2495_ = lean_array_push(v_ands_2390_, v___x_2494_);
v___x_2496_ = 0;
v___x_2497_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2497_, 0, v_maxVer_2492_);
lean_ctor_set_uint8(v___x_2497_, sizeof(void*)*1, v___x_2496_);
lean_ctor_set_uint8(v___x_2497_, sizeof(void*)*1 + 1, v___x_2410_);
v___x_2498_ = lean_array_push(v___x_2495_, v___x_2497_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2498_);
v___x_2500_ = v___x_2404_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_a_2402_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
else
{
lean_object* v_str_2503_; lean_object* v_startInclusive_2504_; lean_object* v_endExclusive_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
lean_dec(v___x_2484_);
lean_dec(v_val_2482_);
lean_dec(v_a_2401_);
lean_del_object(v___x_2398_);
lean_dec_ref(v_ands_2390_);
v_str_2503_ = lean_ctor_get(v___x_2483_, 0);
lean_inc_ref(v_str_2503_);
v_startInclusive_2504_ = lean_ctor_get(v___x_2483_, 1);
lean_inc(v_startInclusive_2504_);
v_endExclusive_2505_ = lean_ctor_get(v___x_2483_, 2);
lean_inc(v_endExclusive_2505_);
lean_dec(v___x_2483_);
v___x_2506_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2507_ = lean_string_utf8_extract_fast(v_str_2503_, v_startInclusive_2504_, v_endExclusive_2505_);
lean_dec(v_endExclusive_2505_);
lean_dec(v_startInclusive_2504_);
lean_dec_ref(v_str_2503_);
v___x_2508_ = lean_string_append(v___x_2506_, v___x_2507_);
lean_dec_ref(v___x_2507_);
v___x_2509_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2510_ = lean_string_append(v___x_2508_, v___x_2509_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2510_);
v___x_2512_ = v___x_2404_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_a_2402_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
else
{
lean_object* v_str_2514_; lean_object* v_startInclusive_2515_; lean_object* v_endExclusive_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
lean_inc(v___x_2480_);
lean_dec(v___x_2481_);
lean_dec(v_a_2401_);
lean_del_object(v___x_2398_);
lean_dec(v_a_2395_);
lean_dec_ref(v_ands_2390_);
v_str_2514_ = lean_ctor_get(v___x_2480_, 0);
lean_inc_ref(v_str_2514_);
v_startInclusive_2515_ = lean_ctor_get(v___x_2480_, 1);
lean_inc(v_startInclusive_2515_);
v_endExclusive_2516_ = lean_ctor_get(v___x_2480_, 2);
lean_inc(v_endExclusive_2516_);
lean_dec(v___x_2480_);
v___x_2517_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2518_ = lean_string_utf8_extract_fast(v_str_2514_, v_startInclusive_2515_, v_endExclusive_2516_);
lean_dec(v_endExclusive_2516_);
lean_dec(v_startInclusive_2515_);
lean_dec_ref(v_str_2514_);
v___x_2519_ = lean_string_append(v___x_2517_, v___x_2518_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2521_ = lean_string_append(v___x_2519_, v___x_2520_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2521_);
v___x_2523_ = v___x_2404_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_a_2402_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_array_fget(v_a_2395_, v___x_2392_);
lean_dec(v_a_2395_);
v___x_2526_ = l_String_Slice_toNat_x3f(v___x_2525_);
if (lean_obj_tag(v___x_2526_) == 1)
{
lean_object* v_val_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_minVer_2532_; 
lean_dec(v___x_2525_);
v_val_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc_n(v_val_2527_, 2);
lean_dec_ref_known(v___x_2526_, 1);
v___x_2528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2528_, 0, v_val_2527_);
lean_ctor_set(v___x_2528_, 1, v___x_2392_);
lean_ctor_set(v___x_2528_, 2, v___x_2392_);
v___x_2529_ = lean_nat_add(v_val_2527_, v___x_2407_);
lean_dec(v_val_2527_);
v___x_2530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v___x_2392_);
lean_ctor_set(v___x_2530_, 2, v___x_2392_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v_a_2401_);
lean_ctor_set(v___x_2398_, 0, v___x_2528_);
v_minVer_2532_ = v___x_2398_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_a_2401_);
v_minVer_2532_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2533_; lean_object* v_maxVer_2534_; uint8_t v___x_2535_; uint8_t v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2533_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2534_, 0, v___x_2530_);
lean_ctor_set(v_maxVer_2534_, 1, v___x_2533_);
v___x_2535_ = 3;
v___x_2536_ = 0;
v___x_2537_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2537_, 0, v_minVer_2532_);
lean_ctor_set_uint8(v___x_2537_, sizeof(void*)*1, v___x_2535_);
lean_ctor_set_uint8(v___x_2537_, sizeof(void*)*1 + 1, v___x_2536_);
v___x_2538_ = lean_array_push(v_ands_2390_, v___x_2537_);
v___x_2539_ = 0;
v___x_2540_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2540_, 0, v_maxVer_2534_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*1, v___x_2539_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*1 + 1, v___x_2408_);
v___x_2541_ = lean_array_push(v___x_2538_, v___x_2540_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2541_);
v___x_2543_ = v___x_2404_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_a_2402_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
else
{
lean_object* v_str_2546_; lean_object* v_startInclusive_2547_; lean_object* v_endExclusive_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
lean_dec(v___x_2526_);
lean_dec(v_a_2401_);
lean_del_object(v___x_2398_);
lean_dec_ref(v_ands_2390_);
v_str_2546_ = lean_ctor_get(v___x_2525_, 0);
lean_inc_ref(v_str_2546_);
v_startInclusive_2547_ = lean_ctor_get(v___x_2525_, 1);
lean_inc(v_startInclusive_2547_);
v_endExclusive_2548_ = lean_ctor_get(v___x_2525_, 2);
lean_inc(v_endExclusive_2548_);
lean_dec(v___x_2525_);
v___x_2549_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2550_ = lean_string_utf8_extract_fast(v_str_2546_, v_startInclusive_2547_, v_endExclusive_2548_);
lean_dec(v_endExclusive_2548_);
lean_dec(v_startInclusive_2547_);
lean_dec_ref(v_str_2546_);
v___x_2551_ = lean_string_append(v___x_2549_, v___x_2550_);
lean_dec_ref(v___x_2550_);
v___x_2552_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2553_ = lean_string_append(v___x_2551_, v___x_2552_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2553_);
v___x_2555_ = v___x_2404_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_a_2402_);
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
}
else
{
lean_object* v_a_2558_; lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_del_object(v___x_2398_);
lean_dec(v_a_2395_);
lean_dec_ref(v_ands_2390_);
v_a_2558_ = lean_ctor_get(v___x_2400_, 0);
v_a_2559_ = lean_ctor_get(v___x_2400_, 1);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2400_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_inc(v_a_2558_);
lean_dec(v___x_2400_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2558_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(lean_object* v_s_2570_, lean_object* v_ands_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v_a_2576_; lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2799_; 
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2572_);
lean_inc_ref(v_s_2570_);
v___x_2575_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2570_, v___x_2574_, v_a_2572_, v_a_2572_);
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
v_a_2577_ = lean_ctor_get(v___x_2575_, 1);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2579_ = v___x_2575_;
v_isShared_2580_ = v_isSharedCheck_2799_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_inc(v_a_2576_);
lean_dec(v___x_2575_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2799_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; 
v___x_2581_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2570_, v_a_2577_);
lean_dec_ref(v_s_2570_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2789_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_a_2583_ = lean_ctor_get(v___x_2581_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2585_ = v___x_2581_;
v_isShared_2586_ = v_isSharedCheck_2789_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2789_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2587_ = lean_array_get_size(v_a_2576_);
v___x_2588_ = lean_unsigned_to_nat(1u);
v___x_2589_ = lean_nat_dec_eq(v___x_2587_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2590_ = lean_unsigned_to_nat(2u);
v___x_2591_ = lean_nat_dec_eq(v___x_2587_, v___x_2590_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = lean_unsigned_to_nat(3u);
v___x_2593_ = lean_nat_dec_eq(v___x_2587_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_dec(v_a_2582_);
lean_del_object(v___x_2579_);
lean_dec(v_a_2576_);
lean_dec_ref(v_ands_2571_);
v___x_2594_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0));
v___x_2595_ = l_Nat_reprFast(v___x_2587_);
v___x_2596_ = lean_string_append(v___x_2594_, v___x_2595_);
lean_dec_ref(v___x_2595_);
v___x_2597_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2598_ = lean_string_append(v___x_2596_, v___x_2597_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2598_);
v___x_2600_ = v___x_2585_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_a_2583_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_array_fget_borrowed(v_a_2576_, v___x_2573_);
v___x_2603_ = l_String_Slice_toNat_x3f(v___x_2602_);
if (lean_obj_tag(v___x_2603_) == 1)
{
lean_object* v_val_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_val_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_val_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v___x_2605_ = lean_array_fget_borrowed(v_a_2576_, v___x_2588_);
v___x_2606_ = l_String_Slice_toNat_x3f(v___x_2605_);
if (lean_obj_tag(v___x_2606_) == 1)
{
lean_object* v_val_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v_val_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_val_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = lean_array_fget(v_a_2576_, v___x_2590_);
lean_dec(v_a_2576_);
v___x_2609_ = l_String_Slice_toNat_x3f(v___x_2608_);
if (lean_obj_tag(v___x_2609_) == 1)
{
lean_object* v_val_2610_; uint8_t v___x_2611_; 
lean_dec(v___x_2608_);
v_val_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_val_2610_);
lean_dec_ref_known(v___x_2609_, 1);
v___x_2611_ = lean_nat_dec_eq(v_val_2604_, v___x_2573_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v_minVer_2615_; lean_object* v___x_2616_; lean_object* v_maxVer_2617_; uint8_t v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_del_object(v___x_2579_);
lean_inc(v_val_2604_);
v___x_2612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2612_, 0, v_val_2604_);
lean_ctor_set(v___x_2612_, 1, v_val_2607_);
lean_ctor_set(v___x_2612_, 2, v_val_2610_);
v___x_2613_ = lean_nat_add(v_val_2604_, v___x_2588_);
lean_dec(v_val_2604_);
v___x_2614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___x_2573_);
lean_ctor_set(v___x_2614_, 2, v___x_2573_);
v_minVer_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2615_, 0, v___x_2612_);
lean_ctor_set(v_minVer_2615_, 1, v_a_2582_);
v___x_2616_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2617_, 0, v___x_2614_);
lean_ctor_set(v_maxVer_2617_, 1, v___x_2616_);
v___x_2618_ = 3;
v___x_2619_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2619_, 0, v_minVer_2615_);
lean_ctor_set_uint8(v___x_2619_, sizeof(void*)*1, v___x_2618_);
lean_ctor_set_uint8(v___x_2619_, sizeof(void*)*1 + 1, v___x_2611_);
v___x_2620_ = lean_array_push(v_ands_2571_, v___x_2619_);
v___x_2621_ = 0;
v___x_2622_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2622_, 0, v_maxVer_2617_);
lean_ctor_set_uint8(v___x_2622_, sizeof(void*)*1, v___x_2621_);
lean_ctor_set_uint8(v___x_2622_, sizeof(void*)*1 + 1, v___x_2593_);
v___x_2623_ = lean_array_push(v___x_2620_, v___x_2622_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2623_);
v___x_2625_ = v___x_2585_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_a_2583_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
else
{
uint8_t v___x_2627_; uint8_t v___y_2629_; 
v___x_2627_ = lean_nat_dec_eq(v_val_2607_, v___x_2573_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v_minVer_2648_; lean_object* v___x_2649_; lean_object* v_maxVer_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_del_object(v___x_2585_);
lean_inc(v_val_2607_);
lean_inc(v_val_2604_);
v___x_2645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2645_, 0, v_val_2604_);
lean_ctor_set(v___x_2645_, 1, v_val_2607_);
lean_ctor_set(v___x_2645_, 2, v_val_2610_);
v___x_2646_ = lean_nat_add(v_val_2607_, v___x_2588_);
lean_dec(v_val_2607_);
v___x_2647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2647_, 0, v_val_2604_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
lean_ctor_set(v___x_2647_, 2, v___x_2573_);
v_minVer_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2648_, 0, v___x_2645_);
lean_ctor_set(v_minVer_2648_, 1, v_a_2582_);
v___x_2649_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2650_, 0, v___x_2647_);
lean_ctor_set(v_maxVer_2650_, 1, v___x_2649_);
v___x_2651_ = 3;
v___x_2652_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2652_, 0, v_minVer_2648_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*1, v___x_2651_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*1 + 1, v___x_2627_);
v___x_2653_ = lean_array_push(v_ands_2571_, v___x_2652_);
v___x_2654_ = 0;
v___x_2655_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2655_, 0, v_maxVer_2650_);
lean_ctor_set_uint8(v___x_2655_, sizeof(void*)*1, v___x_2654_);
lean_ctor_set_uint8(v___x_2655_, sizeof(void*)*1 + 1, v___x_2611_);
v___x_2656_ = lean_array_push(v___x_2653_, v___x_2655_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 1, v_a_2583_);
lean_ctor_set(v___x_2579_, 0, v___x_2656_);
v___x_2658_ = v___x_2579_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_a_2583_);
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
uint8_t v___x_2660_; 
v___x_2660_ = lean_nat_dec_eq(v_val_2610_, v___x_2573_);
if (v___x_2660_ == 0)
{
lean_del_object(v___x_2579_);
v___y_2629_ = v___x_2591_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = lean_string_utf8_byte_size(v_a_2582_);
v___x_2662_ = lean_nat_dec_eq(v___x_2661_, v___x_2573_);
if (v___x_2662_ == 0)
{
lean_del_object(v___x_2579_);
v___y_2629_ = v___x_2662_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
lean_dec(v_val_2610_);
lean_dec(v_val_2607_);
lean_dec(v_val_2604_);
lean_del_object(v___x_2585_);
lean_dec(v_a_2582_);
lean_dec_ref(v_ands_2571_);
v___x_2663_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1));
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 1);
lean_ctor_set(v___x_2579_, 1, v_a_2583_);
lean_ctor_set(v___x_2579_, 0, v___x_2663_);
v___x_2665_ = v___x_2579_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_a_2583_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
v___jp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_minVer_2633_; lean_object* v___x_2634_; lean_object* v_maxVer_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_inc(v_val_2610_);
lean_inc(v_val_2607_);
lean_inc(v_val_2604_);
v___x_2630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2630_, 0, v_val_2604_);
lean_ctor_set(v___x_2630_, 1, v_val_2607_);
lean_ctor_set(v___x_2630_, 2, v_val_2610_);
v___x_2631_ = lean_nat_add(v_val_2610_, v___x_2588_);
lean_dec(v_val_2610_);
v___x_2632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2632_, 0, v_val_2604_);
lean_ctor_set(v___x_2632_, 1, v_val_2607_);
lean_ctor_set(v___x_2632_, 2, v___x_2631_);
v_minVer_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2633_, 0, v___x_2630_);
lean_ctor_set(v_minVer_2633_, 1, v_a_2582_);
v___x_2634_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2635_, 0, v___x_2632_);
lean_ctor_set(v_maxVer_2635_, 1, v___x_2634_);
v___x_2636_ = 3;
v___x_2637_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2637_, 0, v_minVer_2633_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*1, v___x_2636_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*1 + 1, v___y_2629_);
v___x_2638_ = lean_array_push(v_ands_2571_, v___x_2637_);
v___x_2639_ = 0;
v___x_2640_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2640_, 0, v_maxVer_2635_);
lean_ctor_set_uint8(v___x_2640_, sizeof(void*)*1, v___x_2639_);
lean_ctor_set_uint8(v___x_2640_, sizeof(void*)*1 + 1, v___x_2627_);
v___x_2641_ = lean_array_push(v___x_2638_, v___x_2640_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2641_);
v___x_2643_ = v___x_2585_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_a_2583_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_str_2667_; lean_object* v_startInclusive_2668_; lean_object* v_endExclusive_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_dec(v___x_2609_);
lean_dec(v_val_2607_);
lean_dec(v_val_2604_);
lean_dec(v_a_2582_);
lean_del_object(v___x_2579_);
lean_dec_ref(v_ands_2571_);
v_str_2667_ = lean_ctor_get(v___x_2608_, 0);
lean_inc_ref(v_str_2667_);
v_startInclusive_2668_ = lean_ctor_get(v___x_2608_, 1);
lean_inc(v_startInclusive_2668_);
v_endExclusive_2669_ = lean_ctor_get(v___x_2608_, 2);
lean_inc(v_endExclusive_2669_);
lean_dec(v___x_2608_);
v___x_2670_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2671_ = lean_string_utf8_extract_fast(v_str_2667_, v_startInclusive_2668_, v_endExclusive_2669_);
lean_dec(v_endExclusive_2669_);
lean_dec(v_startInclusive_2668_);
lean_dec_ref(v_str_2667_);
v___x_2672_ = lean_string_append(v___x_2670_, v___x_2671_);
lean_dec_ref(v___x_2671_);
v___x_2673_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2674_ = lean_string_append(v___x_2672_, v___x_2673_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2674_);
v___x_2676_ = v___x_2585_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2583_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
else
{
lean_object* v_str_2678_; lean_object* v_startInclusive_2679_; lean_object* v_endExclusive_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
lean_inc(v___x_2605_);
lean_dec(v___x_2606_);
lean_dec(v_val_2604_);
lean_dec(v_a_2582_);
lean_del_object(v___x_2579_);
lean_dec(v_a_2576_);
lean_dec_ref(v_ands_2571_);
v_str_2678_ = lean_ctor_get(v___x_2605_, 0);
lean_inc_ref(v_str_2678_);
v_startInclusive_2679_ = lean_ctor_get(v___x_2605_, 1);
lean_inc(v_startInclusive_2679_);
v_endExclusive_2680_ = lean_ctor_get(v___x_2605_, 2);
lean_inc(v_endExclusive_2680_);
lean_dec(v___x_2605_);
v___x_2681_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2682_ = lean_string_utf8_extract_fast(v_str_2678_, v_startInclusive_2679_, v_endExclusive_2680_);
lean_dec(v_endExclusive_2680_);
lean_dec(v_startInclusive_2679_);
lean_dec_ref(v_str_2678_);
v___x_2683_ = lean_string_append(v___x_2681_, v___x_2682_);
lean_dec_ref(v___x_2682_);
v___x_2684_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2685_ = lean_string_append(v___x_2683_, v___x_2684_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2685_);
v___x_2687_ = v___x_2585_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_a_2583_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
else
{
lean_object* v_str_2689_; lean_object* v_startInclusive_2690_; lean_object* v_endExclusive_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
lean_inc(v___x_2602_);
lean_dec(v___x_2603_);
lean_dec(v_a_2582_);
lean_del_object(v___x_2579_);
lean_dec(v_a_2576_);
lean_dec_ref(v_ands_2571_);
v_str_2689_ = lean_ctor_get(v___x_2602_, 0);
lean_inc_ref(v_str_2689_);
v_startInclusive_2690_ = lean_ctor_get(v___x_2602_, 1);
lean_inc(v_startInclusive_2690_);
v_endExclusive_2691_ = lean_ctor_get(v___x_2602_, 2);
lean_inc(v_endExclusive_2691_);
lean_dec(v___x_2602_);
v___x_2692_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2693_ = lean_string_utf8_extract_fast(v_str_2689_, v_startInclusive_2690_, v_endExclusive_2691_);
lean_dec(v_endExclusive_2691_);
lean_dec(v_startInclusive_2690_);
lean_dec_ref(v_str_2689_);
v___x_2694_ = lean_string_append(v___x_2692_, v___x_2693_);
lean_dec_ref(v___x_2693_);
v___x_2695_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2696_ = lean_string_append(v___x_2694_, v___x_2695_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2696_);
v___x_2698_ = v___x_2585_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_a_2583_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_del_object(v___x_2579_);
v___x_2700_ = lean_array_fget_borrowed(v_a_2576_, v___x_2573_);
v___x_2701_ = l_String_Slice_toNat_x3f(v___x_2700_);
if (lean_obj_tag(v___x_2701_) == 1)
{
lean_object* v_val_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_val_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_val_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = lean_array_fget(v_a_2576_, v___x_2588_);
lean_dec(v_a_2576_);
v___x_2704_ = l_String_Slice_toNat_x3f(v___x_2703_);
if (lean_obj_tag(v___x_2704_) == 1)
{
lean_object* v_val_2705_; uint8_t v___x_2706_; 
lean_dec(v___x_2703_);
v_val_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_val_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v___x_2706_ = lean_nat_dec_eq(v_val_2702_, v___x_2573_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v_minVer_2710_; lean_object* v___x_2711_; lean_object* v_maxVer_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
lean_inc(v_val_2702_);
v___x_2707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2707_, 0, v_val_2702_);
lean_ctor_set(v___x_2707_, 1, v_val_2705_);
lean_ctor_set(v___x_2707_, 2, v___x_2573_);
v___x_2708_ = lean_nat_add(v_val_2702_, v___x_2588_);
lean_dec(v_val_2702_);
v___x_2709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v___x_2573_);
lean_ctor_set(v___x_2709_, 2, v___x_2573_);
v_minVer_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2710_, 0, v___x_2707_);
lean_ctor_set(v_minVer_2710_, 1, v_a_2582_);
v___x_2711_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2712_, 0, v___x_2709_);
lean_ctor_set(v_maxVer_2712_, 1, v___x_2711_);
v___x_2713_ = 3;
v___x_2714_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2714_, 0, v_minVer_2710_);
lean_ctor_set_uint8(v___x_2714_, sizeof(void*)*1, v___x_2713_);
lean_ctor_set_uint8(v___x_2714_, sizeof(void*)*1 + 1, v___x_2706_);
v___x_2715_ = lean_array_push(v_ands_2571_, v___x_2714_);
v___x_2716_ = 0;
v___x_2717_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2717_, 0, v_maxVer_2712_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*1, v___x_2716_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*1 + 1, v___x_2591_);
v___x_2718_ = lean_array_push(v___x_2715_, v___x_2717_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2718_);
v___x_2720_ = v___x_2585_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_a_2583_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v_minVer_2725_; lean_object* v___x_2726_; lean_object* v_maxVer_2727_; uint8_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
lean_inc(v_val_2705_);
lean_inc(v_val_2702_);
v___x_2722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2722_, 0, v_val_2702_);
lean_ctor_set(v___x_2722_, 1, v_val_2705_);
lean_ctor_set(v___x_2722_, 2, v___x_2573_);
v___x_2723_ = lean_nat_add(v_val_2705_, v___x_2588_);
lean_dec(v_val_2705_);
v___x_2724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2724_, 0, v_val_2702_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
lean_ctor_set(v___x_2724_, 2, v___x_2573_);
v_minVer_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2725_, 0, v___x_2722_);
lean_ctor_set(v_minVer_2725_, 1, v_a_2582_);
v___x_2726_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2727_, 0, v___x_2724_);
lean_ctor_set(v_maxVer_2727_, 1, v___x_2726_);
v___x_2728_ = 3;
v___x_2729_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2729_, 0, v_minVer_2725_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*1, v___x_2728_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*1 + 1, v___x_2589_);
v___x_2730_ = lean_array_push(v_ands_2571_, v___x_2729_);
v___x_2731_ = 0;
v___x_2732_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2732_, 0, v_maxVer_2727_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*1, v___x_2731_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*1 + 1, v___x_2706_);
v___x_2733_ = lean_array_push(v___x_2730_, v___x_2732_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2733_);
v___x_2735_ = v___x_2585_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_a_2583_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
else
{
lean_object* v_str_2737_; lean_object* v_startInclusive_2738_; lean_object* v_endExclusive_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
lean_dec(v___x_2704_);
lean_dec(v_val_2702_);
lean_dec(v_a_2582_);
lean_dec_ref(v_ands_2571_);
v_str_2737_ = lean_ctor_get(v___x_2703_, 0);
lean_inc_ref(v_str_2737_);
v_startInclusive_2738_ = lean_ctor_get(v___x_2703_, 1);
lean_inc(v_startInclusive_2738_);
v_endExclusive_2739_ = lean_ctor_get(v___x_2703_, 2);
lean_inc(v_endExclusive_2739_);
lean_dec(v___x_2703_);
v___x_2740_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2741_ = lean_string_utf8_extract_fast(v_str_2737_, v_startInclusive_2738_, v_endExclusive_2739_);
lean_dec(v_endExclusive_2739_);
lean_dec(v_startInclusive_2738_);
lean_dec_ref(v_str_2737_);
v___x_2742_ = lean_string_append(v___x_2740_, v___x_2741_);
lean_dec_ref(v___x_2741_);
v___x_2743_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2744_ = lean_string_append(v___x_2742_, v___x_2743_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2744_);
v___x_2746_ = v___x_2585_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_a_2583_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
else
{
lean_object* v_str_2748_; lean_object* v_startInclusive_2749_; lean_object* v_endExclusive_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
lean_inc(v___x_2700_);
lean_dec(v___x_2701_);
lean_dec(v_a_2582_);
lean_dec(v_a_2576_);
lean_dec_ref(v_ands_2571_);
v_str_2748_ = lean_ctor_get(v___x_2700_, 0);
lean_inc_ref(v_str_2748_);
v_startInclusive_2749_ = lean_ctor_get(v___x_2700_, 1);
lean_inc(v_startInclusive_2749_);
v_endExclusive_2750_ = lean_ctor_get(v___x_2700_, 2);
lean_inc(v_endExclusive_2750_);
lean_dec(v___x_2700_);
v___x_2751_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2752_ = lean_string_utf8_extract_fast(v_str_2748_, v_startInclusive_2749_, v_endExclusive_2750_);
lean_dec(v_endExclusive_2750_);
lean_dec(v_startInclusive_2749_);
lean_dec_ref(v_str_2748_);
v___x_2753_ = lean_string_append(v___x_2751_, v___x_2752_);
lean_dec_ref(v___x_2752_);
v___x_2754_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2755_ = lean_string_append(v___x_2753_, v___x_2754_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2755_);
v___x_2757_ = v___x_2585_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_a_2583_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_del_object(v___x_2579_);
v___x_2759_ = lean_array_fget(v_a_2576_, v___x_2573_);
lean_dec(v_a_2576_);
v___x_2760_ = l_String_Slice_toNat_x3f(v___x_2759_);
if (lean_obj_tag(v___x_2760_) == 1)
{
lean_object* v_val_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v_minVer_2765_; lean_object* v___x_2766_; lean_object* v_maxVer_2767_; uint8_t v___x_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
lean_dec(v___x_2759_);
v_val_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc_n(v_val_2761_, 2);
lean_dec_ref_known(v___x_2760_, 1);
v___x_2762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2762_, 0, v_val_2761_);
lean_ctor_set(v___x_2762_, 1, v___x_2573_);
lean_ctor_set(v___x_2762_, 2, v___x_2573_);
v___x_2763_ = lean_nat_add(v_val_2761_, v___x_2588_);
lean_dec(v_val_2761_);
v___x_2764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
lean_ctor_set(v___x_2764_, 1, v___x_2573_);
lean_ctor_set(v___x_2764_, 2, v___x_2573_);
v_minVer_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2765_, 0, v___x_2762_);
lean_ctor_set(v_minVer_2765_, 1, v_a_2582_);
v___x_2766_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2767_, 0, v___x_2764_);
lean_ctor_set(v_maxVer_2767_, 1, v___x_2766_);
v___x_2768_ = 3;
v___x_2769_ = 0;
v___x_2770_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2770_, 0, v_minVer_2765_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*1, v___x_2768_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*1 + 1, v___x_2769_);
v___x_2771_ = lean_array_push(v_ands_2571_, v___x_2770_);
v___x_2772_ = 0;
v___x_2773_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2773_, 0, v_maxVer_2767_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*1, v___x_2772_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*1 + 1, v___x_2589_);
v___x_2774_ = lean_array_push(v___x_2771_, v___x_2773_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2774_);
v___x_2776_ = v___x_2585_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_a_2583_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
else
{
lean_object* v_str_2778_; lean_object* v_startInclusive_2779_; lean_object* v_endExclusive_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
lean_dec(v___x_2760_);
lean_dec(v_a_2582_);
lean_dec_ref(v_ands_2571_);
v_str_2778_ = lean_ctor_get(v___x_2759_, 0);
lean_inc_ref(v_str_2778_);
v_startInclusive_2779_ = lean_ctor_get(v___x_2759_, 1);
lean_inc(v_startInclusive_2779_);
v_endExclusive_2780_ = lean_ctor_get(v___x_2759_, 2);
lean_inc(v_endExclusive_2780_);
lean_dec(v___x_2759_);
v___x_2781_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2782_ = lean_string_utf8_extract_fast(v_str_2778_, v_startInclusive_2779_, v_endExclusive_2780_);
lean_dec(v_endExclusive_2780_);
lean_dec(v_startInclusive_2779_);
lean_dec_ref(v_str_2778_);
v___x_2783_ = lean_string_append(v___x_2781_, v___x_2782_);
lean_dec_ref(v___x_2782_);
v___x_2784_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2785_ = lean_string_append(v___x_2783_, v___x_2784_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2785_);
v___x_2787_ = v___x_2585_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_a_2583_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_del_object(v___x_2579_);
lean_dec(v_a_2576_);
lean_dec_ref(v_ands_2571_);
v_a_2790_ = lean_ctor_get(v___x_2581_, 0);
v_a_2791_ = lean_ctor_get(v___x_2581_, 1);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2581_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_inc(v_a_2790_);
lean_dec(v___x_2581_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2790_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(lean_object* v_s_2805_, lean_object* v_ands_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v___y_2809_; lean_object* v___y_2813_; lean_object* v___y_2818_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v_a_2824_; lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2971_; 
v___x_2821_ = lean_unsigned_to_nat(0u);
v___x_2822_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2807_);
lean_inc_ref(v_s_2805_);
v___x_2823_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2805_, v___x_2822_, v_a_2807_, v_a_2807_);
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_a_2825_ = lean_ctor_get(v___x_2823_, 1);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2827_ = v___x_2823_;
v_isShared_2828_ = v_isSharedCheck_2971_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2971_;
goto v_resetjp_2826_;
}
v___jp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0));
v___x_2811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
lean_ctor_set(v___x_2811_, 1, v___y_2809_);
return v___x_2811_;
}
v___jp_2812_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2814_ = ((lean_object*)(l_Lake_VerComparator_wild));
v___x_2815_ = lean_array_push(v_ands_2806_, v___x_2814_);
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
lean_ctor_set(v___x_2816_, 1, v___y_2813_);
return v___x_2816_;
}
v___jp_2817_:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1));
v___x_2820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
lean_ctor_set(v___x_2820_, 1, v___y_2818_);
return v___x_2820_;
}
v_resetjp_2826_:
{
lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___x_2944_; lean_object* v___y_2946_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2944_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__1));
v___x_2966_ = lean_array_get_size(v_a_2824_);
v___x_2967_ = lean_nat_dec_lt(v___x_2821_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; 
v___x_2968_ = lean_box(0);
v___y_2946_ = v___x_2968_;
goto v___jp_2945_;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_array_fget_borrowed(v_a_2824_, v___x_2821_);
lean_inc(v___x_2969_);
v___x_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
v___y_2946_ = v___x_2970_;
goto v___jp_2945_;
}
v___jp_2829_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2835_ = lean_unsigned_to_nat(3u);
v___x_2836_ = lean_array_get_size(v_a_2824_);
lean_dec(v_a_2824_);
v___x_2837_ = lean_nat_dec_lt(v___x_2835_, v___x_2836_);
if (v___x_2837_ == 0)
{
switch(lean_obj_tag(v___y_2831_))
{
case 2:
{
switch(lean_obj_tag(v___y_2834_))
{
case 2:
{
if (lean_obj_tag(v___y_2833_) == 1)
{
lean_object* v_n_2838_; lean_object* v_n_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v_minVer_2844_; lean_object* v_maxVer_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; uint8_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v_n_2838_ = lean_ctor_get(v___y_2831_, 0);
lean_inc_n(v_n_2838_, 2);
lean_dec_ref_known(v___y_2831_, 1);
v_n_2839_ = lean_ctor_get(v___y_2834_, 0);
lean_inc_n(v_n_2839_, 2);
lean_dec_ref_known(v___y_2834_, 1);
v___x_2840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2840_, 0, v_n_2838_);
lean_ctor_set(v___x_2840_, 1, v_n_2839_);
lean_ctor_set(v___x_2840_, 2, v___x_2821_);
v___x_2841_ = lean_nat_add(v_n_2839_, v___y_2832_);
lean_dec(v_n_2839_);
v___x_2842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2842_, 0, v_n_2838_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
lean_ctor_set(v___x_2842_, 2, v___x_2821_);
v___x_2843_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2844_, 0, v___x_2840_);
lean_ctor_set(v_minVer_2844_, 1, v___x_2843_);
v_maxVer_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2845_, 0, v___x_2842_);
lean_ctor_set(v_maxVer_2845_, 1, v___x_2843_);
v___x_2846_ = 3;
v___x_2847_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2847_, 0, v_minVer_2844_);
lean_ctor_set_uint8(v___x_2847_, sizeof(void*)*1, v___x_2846_);
lean_ctor_set_uint8(v___x_2847_, sizeof(void*)*1 + 1, v___x_2837_);
v___x_2848_ = lean_array_push(v_ands_2806_, v___x_2847_);
v___x_2849_ = 0;
v___x_2850_ = 1;
v___x_2851_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2851_, 0, v_maxVer_2845_);
lean_ctor_set_uint8(v___x_2851_, sizeof(void*)*1, v___x_2849_);
lean_ctor_set_uint8(v___x_2851_, sizeof(void*)*1 + 1, v___x_2850_);
v___x_2852_ = lean_array_push(v___x_2848_, v___x_2851_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 1, v___y_2830_);
lean_ctor_set(v___x_2827_, 0, v___x_2852_);
v___x_2854_ = v___x_2827_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v___y_2830_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
else
{
lean_dec_ref_known(v___y_2834_, 1);
lean_dec_ref_known(v___y_2831_, 1);
lean_dec(v___y_2833_);
lean_del_object(v___x_2827_);
lean_dec_ref(v_ands_2806_);
v___y_2818_ = v___y_2830_;
goto v___jp_2817_;
}
}
case 1:
{
if (lean_obj_tag(v___y_2833_) == 2)
{
lean_dec_ref_known(v___y_2833_, 1);
lean_dec_ref_known(v___y_2831_, 1);
lean_del_object(v___x_2827_);
lean_dec_ref(v_ands_2806_);
v___y_2809_ = v___y_2830_;
goto v___jp_2808_;
}
else
{
lean_object* v_n_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v_minVer_2861_; lean_object* v_maxVer_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; uint8_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
lean_dec(v___y_2833_);
v_n_2856_ = lean_ctor_get(v___y_2831_, 0);
lean_inc_n(v_n_2856_, 2);
lean_dec_ref_known(v___y_2831_, 1);
v___x_2857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2857_, 0, v_n_2856_);
lean_ctor_set(v___x_2857_, 1, v___x_2821_);
lean_ctor_set(v___x_2857_, 2, v___x_2821_);
v___x_2858_ = lean_nat_add(v_n_2856_, v___y_2832_);
lean_dec(v_n_2856_);
v___x_2859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v___x_2821_);
lean_ctor_set(v___x_2859_, 2, v___x_2821_);
v___x_2860_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2861_, 0, v___x_2857_);
lean_ctor_set(v_minVer_2861_, 1, v___x_2860_);
v_maxVer_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2862_, 0, v___x_2859_);
lean_ctor_set(v_maxVer_2862_, 1, v___x_2860_);
v___x_2863_ = 3;
v___x_2864_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2864_, 0, v_minVer_2861_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*1, v___x_2863_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*1 + 1, v___x_2837_);
v___x_2865_ = lean_array_push(v_ands_2806_, v___x_2864_);
v___x_2866_ = 0;
v___x_2867_ = 1;
v___x_2868_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2868_, 0, v_maxVer_2862_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*1, v___x_2866_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*1 + 1, v___x_2867_);
v___x_2869_ = lean_array_push(v___x_2865_, v___x_2868_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 1, v___y_2830_);
lean_ctor_set(v___x_2827_, 0, v___x_2869_);
v___x_2871_ = v___x_2827_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v___y_2830_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
default: 
{
lean_dec_ref_known(v___y_2831_, 1);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_del_object(v___x_2827_);
lean_dec_ref(v_ands_2806_);
v___y_2818_ = v___y_2830_;
goto v___jp_2817_;
}
}
}
case 1:
{
if (lean_obj_tag(v___y_2833_) == 2)
{
lean_dec_ref_known(v___y_2833_, 1);
lean_dec(v___y_2834_);
lean_del_object(v___x_2827_);
lean_dec_ref(v_ands_2806_);
v___y_2809_ = v___y_2830_;
goto v___jp_2808_;
}
else
{
lean_dec(v___y_2833_);
if (lean_obj_tag(v___y_2834_) == 2)
{
lean_object* v___x_2873_; lean_object* v___x_2875_; 
lean_dec_ref_known(v___y_2834_, 1);
lean_dec_ref(v_ands_2806_);
v___x_2873_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2));
if (v_isShared_2828_ == 0)
{
lean_ctor_set_tag(v___x_2827_, 1);
lean_ctor_set(v___x_2827_, 1, v___y_2830_);
lean_ctor_set(v___x_2827_, 0, v___x_2873_);
v___x_2875_ = v___x_2827_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___y_2830_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
else
{
lean_dec(v___y_2834_);
lean_del_object(v___x_2827_);
v___y_2813_ = v___y_2830_;
goto v___jp_2812_;
}
}
}
default: 
{
lean_dec(v___y_2831_);
lean_del_object(v___x_2827_);
if (lean_obj_tag(v___y_2834_) == 1)
{
if (lean_obj_tag(v___y_2833_) == 2)
{
lean_dec_ref_known(v___y_2833_, 1);
lean_dec_ref(v_ands_2806_);
v___y_2809_ = v___y_2830_;
goto v___jp_2808_;
}
else
{
lean_dec(v___y_2833_);
v___y_2813_ = v___y_2830_;
goto v___jp_2812_;
}
}
else
{
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
v___y_2813_ = v___y_2830_;
goto v___jp_2812_;
}
}
}
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2831_);
lean_dec_ref(v_ands_2806_);
v___x_2877_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3));
v___x_2878_ = l_Nat_reprFast(v___x_2836_);
v___x_2879_ = lean_string_append(v___x_2877_, v___x_2878_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2881_ = lean_string_append(v___x_2879_, v___x_2880_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set_tag(v___x_2827_, 1);
lean_ctor_set(v___x_2827_, 1, v___y_2830_);
lean_ctor_set(v___x_2827_, 0, v___x_2881_);
v___x_2883_ = v___x_2827_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___y_2830_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
v___jp_2885_:
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2888_, v___y_2891_, v___y_2887_);
lean_dec(v___y_2891_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2909_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_a_2894_ = lean_ctor_get(v___x_2892_, 1);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2896_ = v___x_2892_;
v_isShared_2897_ = v_isSharedCheck_2909_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2909_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = lean_string_utf8_byte_size(v_s_2805_);
v___x_2899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2899_, 0, v_s_2805_);
lean_ctor_set(v___x_2899_, 1, v___x_2821_);
lean_ctor_set(v___x_2899_, 2, v___x_2898_);
v___x_2900_ = l_String_Slice_Pos_get_x3f(v___x_2899_, v_a_2894_);
lean_dec_ref_known(v___x_2899_, 3);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_del_object(v___x_2896_);
v___y_2830_ = v_a_2894_;
v___y_2831_ = v___y_2886_;
v___y_2832_ = v___y_2889_;
v___y_2833_ = v_a_2893_;
v___y_2834_ = v___y_2890_;
goto v___jp_2829_;
}
else
{
lean_object* v_val_2901_; uint32_t v___x_2902_; uint32_t v___x_2903_; uint8_t v___x_2904_; 
v_val_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_val_2901_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2902_ = 45;
v___x_2903_ = lean_unbox_uint32(v_val_2901_);
lean_dec(v_val_2901_);
v___x_2904_ = lean_uint32_dec_eq(v___x_2903_, v___x_2902_);
if (v___x_2904_ == 0)
{
lean_del_object(v___x_2896_);
v___y_2830_ = v_a_2894_;
v___y_2831_ = v___y_2886_;
v___y_2832_ = v___y_2889_;
v___y_2833_ = v_a_2893_;
v___y_2834_ = v___y_2890_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
lean_dec(v_a_2893_);
lean_dec(v___y_2890_);
lean_dec(v___y_2886_);
lean_del_object(v___x_2827_);
lean_dec(v_a_2824_);
lean_dec_ref(v_ands_2806_);
v___x_2905_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4));
if (v_isShared_2897_ == 0)
{
lean_ctor_set_tag(v___x_2896_, 1);
lean_ctor_set(v___x_2896_, 0, v___x_2905_);
v___x_2907_ = v___x_2896_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_a_2894_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v___y_2890_);
lean_dec(v___y_2886_);
lean_del_object(v___x_2827_);
lean_dec(v_a_2824_);
lean_dec_ref(v_ands_2806_);
lean_dec_ref(v_s_2805_);
v_a_2910_ = lean_ctor_get(v___x_2892_, 0);
v_a_2911_ = lean_ctor_get(v___x_2892_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2892_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_inc(v_a_2910_);
lean_dec(v___x_2892_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2910_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
v___jp_2919_:
{
lean_object* v___x_2925_; 
v___x_2925_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2923_, v___y_2924_, v___y_2921_);
lean_dec(v___y_2924_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v_a_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
v_a_2927_ = lean_ctor_get(v___x_2925_, 1);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2925_, 2);
v___x_2928_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__12));
v___x_2929_ = lean_unsigned_to_nat(2u);
v___x_2930_ = lean_array_get_size(v_a_2824_);
v___x_2931_ = lean_nat_dec_lt(v___x_2929_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; 
v___x_2932_ = lean_box(0);
v___y_2886_ = v___y_2920_;
v___y_2887_ = v_a_2927_;
v___y_2888_ = v___x_2928_;
v___y_2889_ = v___y_2922_;
v___y_2890_ = v_a_2926_;
v___y_2891_ = v___x_2932_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_array_fget_borrowed(v_a_2824_, v___x_2929_);
lean_inc(v___x_2933_);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
v___y_2886_ = v___y_2920_;
v___y_2887_ = v_a_2927_;
v___y_2888_ = v___x_2928_;
v___y_2889_ = v___y_2922_;
v___y_2890_ = v_a_2926_;
v___y_2891_ = v___x_2934_;
goto v___jp_2885_;
}
}
else
{
lean_object* v_a_2935_; lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v___y_2920_);
lean_del_object(v___x_2827_);
lean_dec(v_a_2824_);
lean_dec_ref(v_ands_2806_);
lean_dec_ref(v_s_2805_);
v_a_2935_ = lean_ctor_get(v___x_2925_, 0);
v_a_2936_ = lean_ctor_get(v___x_2925_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2925_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_inc(v_a_2935_);
lean_dec(v___x_2925_);
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
v___jp_2945_:
{
lean_object* v___x_2947_; 
v___x_2947_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___x_2944_, v___y_2946_, v_a_2825_);
lean_dec(v___y_2946_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v_a_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
v_a_2949_ = lean_ctor_get(v___x_2947_, 1);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2947_, 2);
v___x_2950_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__10));
v___x_2951_ = lean_unsigned_to_nat(1u);
v___x_2952_ = lean_array_get_size(v_a_2824_);
v___x_2953_ = lean_nat_dec_lt(v___x_2951_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; 
v___x_2954_ = lean_box(0);
v___y_2920_ = v_a_2948_;
v___y_2921_ = v_a_2949_;
v___y_2922_ = v___x_2951_;
v___y_2923_ = v___x_2950_;
v___y_2924_ = v___x_2954_;
goto v___jp_2919_;
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_array_fget_borrowed(v_a_2824_, v___x_2951_);
lean_inc(v___x_2955_);
v___x_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
v___y_2920_ = v_a_2948_;
v___y_2921_ = v_a_2949_;
v___y_2922_ = v___x_2951_;
v___y_2923_ = v___x_2950_;
v___y_2924_ = v___x_2956_;
goto v___jp_2919_;
}
}
else
{
lean_object* v_a_2957_; lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_del_object(v___x_2827_);
lean_dec(v_a_2824_);
lean_dec_ref(v_ands_2806_);
lean_dec_ref(v_s_2805_);
v_a_2957_ = lean_ctor_get(v___x_2947_, 0);
v_a_2958_ = lean_ctor_get(v___x_2947_, 1);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2947_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_inc(v_a_2957_);
lean_dec(v___x_2947_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2957_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
}
lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(lean_object* v_s_2978_, uint8_t v_needsRange_2979_, lean_object* v_ors_2980_, lean_object* v_ands_2981_, lean_object* v_p_2982_){
_start:
{
lean_object* v___x_2989_; uint8_t v_decide_2990_; 
v___x_2989_ = lean_string_utf8_byte_size(v_s_2978_);
v_decide_2990_ = lean_nat_dec_eq(v_p_2982_, v___x_2989_);
if (v_decide_2990_ == 0)
{
uint32_t v_c_3005_; uint32_t v___x_3105_; uint8_t v___x_3106_; 
v_c_3005_ = lean_string_utf8_get_fast(v_s_2978_, v_p_2982_);
v___x_3105_ = 65;
v___x_3106_ = lean_uint32_dec_le(v___x_3105_, v_c_3005_);
if (v___x_3106_ == 0)
{
goto v___jp_3100_;
}
else
{
uint32_t v___x_3107_; uint8_t v___x_3108_; 
v___x_3107_ = 90;
v___x_3108_ = lean_uint32_dec_le(v_c_3005_, v___x_3107_);
if (v___x_3108_ == 0)
{
goto v___jp_3100_;
}
else
{
goto v___jp_2991_;
}
}
v___jp_3006_:
{
uint32_t v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = 42;
v___x_3008_ = lean_uint32_dec_eq(v_c_3005_, v___x_3007_);
if (v___x_3008_ == 0)
{
uint32_t v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = 94;
v___x_3010_ = lean_uint32_dec_eq(v_c_3005_, v___x_3009_);
if (v___x_3010_ == 0)
{
uint32_t v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = 126;
v___x_3012_ = lean_uint32_dec_eq(v_c_3005_, v___x_3011_);
if (v___x_3012_ == 0)
{
uint32_t v___x_3013_; uint8_t v___x_3014_; 
v___x_3013_ = 32;
v___x_3014_ = lean_uint32_dec_eq(v_c_3005_, v___x_3013_);
if (v___x_3014_ == 0)
{
uint32_t v___x_3015_; uint8_t v___x_3016_; 
v___x_3015_ = 9;
v___x_3016_ = lean_uint32_dec_eq(v_c_3005_, v___x_3015_);
if (v___x_3016_ == 0)
{
uint32_t v___x_3017_; uint8_t v___x_3018_; 
v___x_3017_ = 13;
v___x_3018_ = lean_uint32_dec_eq(v_c_3005_, v___x_3017_);
if (v___x_3018_ == 0)
{
uint32_t v___x_3019_; uint8_t v___x_3020_; 
v___x_3019_ = 10;
v___x_3020_ = lean_uint32_dec_eq(v_c_3005_, v___x_3019_);
if (v___x_3020_ == 0)
{
uint8_t v___x_3021_; uint32_t v___x_3022_; uint8_t v___x_3023_; 
v___x_3021_ = 1;
v___x_3022_ = 44;
v___x_3023_ = lean_uint32_dec_eq(v_c_3005_, v___x_3022_);
if (v___x_3023_ == 0)
{
uint32_t v___x_3024_; uint8_t v___x_3025_; 
v___x_3024_ = 124;
v___x_3025_ = lean_uint32_dec_eq(v_c_3005_, v___x_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; 
lean_inc_ref(v_s_2978_);
v___x_3026_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_2978_, v_p_2982_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v_a_3028_; lean_object* v___x_3029_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
v_a_3028_ = lean_ctor_get(v___x_3026_, 1);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3026_, 2);
v___x_3029_ = lean_array_push(v_ands_2981_, v_a_3027_);
v_needsRange_2979_ = v___x_3025_;
v_ands_2981_ = v___x_3029_;
v_p_2982_ = v_a_3028_;
goto _start;
}
else
{
lean_object* v_a_3031_; lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_ands_2981_);
lean_dec_ref(v_ors_2980_);
lean_dec_ref(v_s_2978_);
v_a_3031_ = lean_ctor_get(v___x_3026_, 0);
v_a_3032_ = lean_ctor_get(v___x_3026_, 1);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3026_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_inc(v_a_3031_);
lean_dec(v___x_3026_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3031_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_p_3040_; uint8_t v_decide_3041_; 
v_p_3040_ = lean_string_utf8_next_fast(v_s_2978_, v_p_2982_);
lean_dec(v_p_2982_);
v_decide_3041_ = lean_nat_dec_eq(v_p_3040_, v___x_2989_);
if (v_decide_3041_ == 0)
{
uint32_t v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = lean_string_utf8_get_fast(v_s_2978_, v_p_3040_);
v___x_3043_ = lean_uint32_dec_eq(v___x_3042_, v___x_3024_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_dec_ref(v_ands_2981_);
lean_dec_ref(v_ors_2980_);
lean_dec_ref(v_s_2978_);
v___x_3044_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v_p_3040_);
return v___x_3045_;
}
else
{
lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3046_ = lean_array_get_size(v_ands_2981_);
v___x_3047_ = lean_unsigned_to_nat(0u);
v___x_3048_ = lean_nat_dec_eq(v___x_3046_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = lean_array_push(v_ors_2980_, v_ands_2981_);
v___x_3050_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2));
v___x_3051_ = lean_string_utf8_next_fast(v_s_2978_, v_p_3040_);
v_needsRange_2979_ = v___x_3021_;
v_ors_2980_ = v___x_3049_;
v_ands_2981_ = v___x_3050_;
v_p_2982_ = v___x_3051_;
goto _start;
}
else
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
lean_dec_ref(v_ands_2981_);
lean_dec_ref(v_ors_2980_);
lean_dec_ref(v_s_2978_);
v___x_3053_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
lean_ctor_set(v___x_3054_, 1, v_p_3040_);
return v___x_3054_;
}
}
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_dec_ref(v_ands_2981_);
lean_dec_ref(v_ors_2980_);
lean_dec_ref(v_s_2978_);
v___x_3055_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v_p_3040_);
return v___x_3056_;
}
}
}
else
{
if (v_needsRange_2979_ == 0)
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_string_utf8_next_fast(v_s_2978_, v_p_2982_);
lean_dec(v_p_2982_);
v_needsRange_2979_ = v___x_3021_;
v_p_2982_ = v___x_3057_;
goto _start;
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
lean_dec_ref(v_ands_2981_);
lean_dec_ref(v_ors_2980_);
lean_dec_ref(v_s_2978_);
v___x_3059_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
lean_ctor_set(v___x_3060_, 1, v_p_2982_);
return v___x_3060_;
}
}
}
else
{
goto v___jp_2986_;
}
}
else
{
goto v___jp_2986_;
}
}
else
{
goto v___jp_2986_;
}
}
else
{
goto v___jp_2986_;
}
}
else
{
lean_object* v_p_3061_; uint8_t v_decide_3062_; 
v_p_3061_ = lean_string_utf8_next_fast(v_s_2978_, v_p_2982_);
lean_dec(v_p_2982_);
v_decide_3062_ = lean_nat_dec_eq(v_p_3061_, v___x_2989_);
if (v_decide_3062_ == 0)
{
lean_object* v___x_3063_; 
lean_inc_ref(v_s_2978_);
v___x_3063_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(v_s_2978_, v_ands_2981_, v_p_3061_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v_a_3065_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
v_a_3065_ = lean_ctor_get(v___x_3063_, 1);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3063_, 2);
v_needsRange_2979_ = v_decide_3062_;
v_ands_2981_ = v_a_3064_;
v_p_2982_ = v_a_3065_;
goto _start;
}
else
{
lean_object* v_a_3067_; lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v_ors_2980_);
lean_dec_ref(v_s_2978_);
v_a_3067_ = lean_ctor_get(v___x_3063_, 0);
v_a_3068_ = lean_ctor_get(v___x_3063_, 1);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3063_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_inc(v_a_3067_);
lean_dec(v___x_3063_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3067_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_dec_ref(v_ands_2981_);
lean_dec_ref(v_ors_2980_);
lean_dec_ref(v_s_2978_);
v___x_3076_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3));
v___x_3077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3076_);
lean_ctor_set(v___x_3077_, 1, v_p_3061_);
return v___x_3077_;
}
}
}
else
{
lean_object* v_p_3078_; uint8_t v_decide_3079_; 
v_p_3078_ = lean_string_utf8_next_fast(v_s_2978_, v_p_2982_);
lean_dec(v_p_2982_);
v_decide_3079_ = lean_nat_dec_eq(v_p_3078_, v___x_2989_);
if (v_decide_3079_ == 0)
{
lean_object* v___x_3080_; 
lean_inc_ref(v_s_2978_);
v___x_3080_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(v_s_2978_, v_ands_2981_, v_p_3078_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v_a_3082_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
v_a_3082_ = lean_ctor_get(v___x_3080_, 1);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3080_, 2);
v_needsRange_2979_ = v_decide_3079_;
v_ands_2981_ = v_a_3081_;
v_p_2982_ = v_a_3082_;
goto _start;
}
else
{
lean_object* v_a_3084_; lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec_ref(v_ors_2980_);
lean_dec_ref(v_s_2978_);
v_a_3084_ = lean_ctor_get(v___x_3080_, 0);
v_a_3085_ = lean_ctor_get(v___x_3080_, 1);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3080_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_inc(v_a_3084_);
lean_dec(v___x_3080_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3084_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec_ref(v_ands_2981_);
lean_dec_ref(v_ors_2980_);
lean_dec_ref(v_s_2978_);
v___x_3093_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4));
v___x_3094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v_p_3078_);
return v___x_3094_;
}
}
}
else
{
goto v___jp_2991_;
}
}
v___jp_3095_:
{
uint32_t v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = 48;
v___x_3097_ = lean_uint32_dec_le(v___x_3096_, v_c_3005_);
if (v___x_3097_ == 0)
{
goto v___jp_3006_;
}
else
{
uint32_t v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = 57;
v___x_3099_ = lean_uint32_dec_le(v_c_3005_, v___x_3098_);
if (v___x_3099_ == 0)
{
goto v___jp_3006_;
}
else
{
goto v___jp_2991_;
}
}
}
v___jp_3100_:
{
uint32_t v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = 97;
v___x_3102_ = lean_uint32_dec_le(v___x_3101_, v_c_3005_);
if (v___x_3102_ == 0)
{
goto v___jp_3095_;
}
else
{
uint32_t v___x_3103_; uint8_t v___x_3104_; 
v___x_3103_ = 122;
v___x_3104_ = lean_uint32_dec_le(v_c_3005_, v___x_3103_);
if (v___x_3104_ == 0)
{
goto v___jp_3095_;
}
else
{
goto v___jp_2991_;
}
}
}
}
else
{
lean_dec_ref(v_s_2978_);
if (v_needsRange_2979_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3109_ = lean_array_get_size(v_ands_2981_);
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_nat_dec_eq(v___x_3109_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = lean_array_push(v_ors_2980_, v_ands_2981_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
lean_ctor_set(v___x_3113_, 1, v_p_2982_);
return v___x_3113_;
}
else
{
lean_dec_ref(v_ands_2981_);
lean_dec_ref(v_ors_2980_);
goto v___jp_2983_;
}
}
else
{
lean_dec_ref(v_ands_2981_);
lean_dec_ref(v_ors_2980_);
goto v___jp_2983_;
}
}
v___jp_2983_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
lean_ctor_set(v___x_2985_, 1, v_p_2982_);
return v___x_2985_;
}
v___jp_2986_:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_string_utf8_next_fast(v_s_2978_, v_p_2982_);
lean_dec(v_p_2982_);
v_p_2982_ = v___x_2987_;
goto _start;
}
v___jp_2991_:
{
lean_object* v___x_2992_; 
lean_inc_ref(v_s_2978_);
v___x_2992_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(v_s_2978_, v_ands_2981_, v_p_2982_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v_a_2994_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
v_a_2994_ = lean_ctor_get(v___x_2992_, 1);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2992_, 2);
v_needsRange_2979_ = v_decide_2990_;
v_ands_2981_ = v_a_2993_;
v_p_2982_ = v_a_2994_;
goto _start;
}
else
{
lean_object* v_a_2996_; lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec_ref(v_ors_2980_);
lean_dec_ref(v_s_2978_);
v_a_2996_ = lean_ctor_get(v___x_2992_, 0);
v_a_2997_ = lean_ctor_get(v___x_2992_, 1);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2992_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_inc(v_a_2996_);
lean_dec(v___x_2992_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2996_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2978_ = stack[0].m_obj;
uint8_t v_needsRange_2979_ = stack[1].m_num;
lean_object* v_ors_2980_ = stack[2].m_obj;
lean_object* v_ands_2981_ = stack[3].m_obj;
lean_object* v_p_2982_ = stack[4].m_obj;
lean_object* v_res_3114_;
v_res_3114_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_2978_, v_needsRange_2979_, v_ors_2980_, v_ands_2981_, v_p_2982_);
stack->m_obj
 = v_res_3114_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(lean_object* v_s_3115_, lean_object* v_needsRange_3116_, lean_object* v_ors_3117_, lean_object* v_ands_3118_, lean_object* v_p_3119_){
_start:
{
uint8_t v_needsRange_boxed_3120_; lean_object* v_res_3121_; 
v_needsRange_boxed_3120_ = lean_unbox(v_needsRange_3116_);
v_res_3121_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3115_, v_needsRange_boxed_3120_, v_ors_3117_, v_ands_3118_, v_p_3119_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object* v_s_3124_, lean_object* v_a_3125_){
_start:
{
uint8_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = 1;
v___x_3127_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3124_);
v___x_3128_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3124_, v___x_3126_, v___x_3127_, v___x_3127_, v_a_3125_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3138_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_a_3130_ = lean_ctor_get(v___x_3128_, 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3132_ = v___x_3128_;
v_isShared_3133_ = v_isSharedCheck_3138_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3138_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v_s_3124_);
lean_ctor_set(v___x_3134_, 1, v_a_3129_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3134_);
v___x_3136_ = v___x_3132_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_a_3130_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v_s_3124_);
v_a_3139_ = lean_ctor_get(v___x_3128_, 0);
v_a_3140_ = lean_ctor_get(v___x_3128_, 1);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3128_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_inc(v_a_3139_);
lean_dec(v___x_3128_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3139_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_parse(lean_object* v_s_3148_){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3149_ = lean_unsigned_to_nat(0u);
v___x_3150_ = lean_string_utf8_byte_size(v_s_3148_);
v___x_3151_ = 1;
v___x_3152_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3148_);
v___x_3153_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3148_, v___x_3151_, v___x_3152_, v___x_3152_, v___x_3149_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3168_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_a_3155_ = lean_ctor_get(v___x_3153_, 1);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3157_ = v___x_3153_;
v_isShared_3158_ = v_isSharedCheck_3168_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3168_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
uint8_t v_decide_3159_; 
v_decide_3159_ = lean_nat_dec_eq(v_a_3155_, v___x_3150_);
if (v_decide_3159_ == 0)
{
lean_object* v_tail_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
lean_del_object(v___x_3157_);
lean_dec(v_a_3154_);
v_tail_3160_ = lean_string_utf8_extract(v_s_3148_, v_a_3155_, v___x_3150_);
lean_dec(v_a_3155_);
lean_dec_ref(v_s_3148_);
v___x_3161_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_3162_ = lean_string_append(v___x_3161_, v_tail_3160_);
lean_dec_ref(v_tail_3160_);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
else
{
lean_object* v___x_3165_; 
lean_dec(v_a_3155_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 1, v_a_3154_);
lean_ctor_set(v___x_3157_, 0, v_s_3148_);
v___x_3165_ = v___x_3157_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_s_3148_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v_a_3154_);
v___x_3165_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3166_; 
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3170_; 
lean_dec_ref(v_s_3148_);
v_a_3169_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3153_, 2);
v___x_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3170_, 0, v_a_3169_);
return v___x_3170_;
}
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(lean_object* v_ver_3173_, lean_object* v_as_3174_, size_t v_i_3175_, size_t v_stop_3176_){
_start:
{
uint8_t v___x_3177_; 
v___x_3177_ = lean_usize_dec_eq(v_i_3175_, v_stop_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; uint8_t v___x_3179_; 
v___x_3178_ = lean_array_uget_borrowed(v_as_3174_, v_i_3175_);
v___x_3179_ = l_Lake_VerComparator_test(v___x_3178_, v_ver_3173_);
if (v___x_3179_ == 0)
{
uint8_t v___x_3180_; 
v___x_3180_ = 1;
return v___x_3180_;
}
else
{
size_t v___x_3181_; size_t v___x_3182_; 
v___x_3181_ = ((size_t)1ULL);
v___x_3182_ = lean_usize_add(v_i_3175_, v___x_3181_);
v_i_3175_ = v___x_3182_;
goto _start;
}
}
else
{
uint8_t v___x_3184_; 
v___x_3184_ = 0;
return v___x_3184_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ver_3173_ = stack[0].m_obj;
lean_object* v_as_3174_ = stack[1].m_obj;
size_t v_i_3175_ = stack[2].m_num;
size_t v_stop_3176_ = stack[3].m_num;
uint8_t v_res_3185_;
v_res_3185_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3173_, v_as_3174_, v_i_3175_, v_stop_3176_);
stack->m_num = v_res_3185_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0___boxed(lean_object* v_ver_3186_, lean_object* v_as_3187_, lean_object* v_i_3188_, lean_object* v_stop_3189_){
_start:
{
size_t v_i_boxed_3190_; size_t v_stop_boxed_3191_; uint8_t v_res_3192_; lean_object* v_r_3193_; 
v_i_boxed_3190_ = lean_unbox_usize(v_i_3188_);
lean_dec(v_i_3188_);
v_stop_boxed_3191_ = lean_unbox_usize(v_stop_3189_);
lean_dec(v_stop_3189_);
v_res_3192_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3186_, v_as_3187_, v_i_boxed_3190_, v_stop_boxed_3191_);
lean_dec_ref(v_as_3187_);
lean_dec_ref(v_ver_3186_);
v_r_3193_ = lean_box(v_res_3192_);
return v_r_3193_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(lean_object* v_ver_3194_, lean_object* v_as_3195_, size_t v_i_3196_, size_t v_stop_3197_){
_start:
{
uint8_t v___x_3198_; 
v___x_3198_ = lean_usize_dec_eq(v_i_3196_, v_stop_3197_);
if (v___x_3198_ == 0)
{
uint8_t v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; uint8_t v___x_3203_; 
v___x_3199_ = 1;
v___x_3200_ = lean_array_uget_borrowed(v_as_3195_, v_i_3196_);
v___x_3201_ = lean_unsigned_to_nat(0u);
v___x_3202_ = lean_array_get_size(v___x_3200_);
v___x_3203_ = lean_nat_dec_lt(v___x_3201_, v___x_3202_);
if (v___x_3203_ == 0)
{
return v___x_3199_;
}
else
{
if (v___x_3203_ == 0)
{
return v___x_3199_;
}
else
{
size_t v___x_3204_; size_t v___x_3205_; uint8_t v___x_3206_; 
v___x_3204_ = ((size_t)0ULL);
v___x_3205_ = lean_usize_of_nat(v___x_3202_);
v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3194_, v___x_3200_, v___x_3204_, v___x_3205_);
if (v___x_3206_ == 0)
{
return v___x_3199_;
}
else
{
size_t v___x_3207_; size_t v___x_3208_; 
v___x_3207_ = ((size_t)1ULL);
v___x_3208_ = lean_usize_add(v_i_3196_, v___x_3207_);
v_i_3196_ = v___x_3208_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3210_; 
v___x_3210_ = 0;
return v___x_3210_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ver_3194_ = stack[0].m_obj;
lean_object* v_as_3195_ = stack[1].m_obj;
size_t v_i_3196_ = stack[2].m_num;
size_t v_stop_3197_ = stack[3].m_num;
uint8_t v_res_3211_;
v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3194_, v_as_3195_, v_i_3196_, v_stop_3197_);
stack->m_num = v_res_3211_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1___boxed(lean_object* v_ver_3212_, lean_object* v_as_3213_, lean_object* v_i_3214_, lean_object* v_stop_3215_){
_start:
{
size_t v_i_boxed_3216_; size_t v_stop_boxed_3217_; uint8_t v_res_3218_; lean_object* v_r_3219_; 
v_i_boxed_3216_ = lean_unbox_usize(v_i_3214_);
lean_dec(v_i_3214_);
v_stop_boxed_3217_ = lean_unbox_usize(v_stop_3215_);
lean_dec(v_stop_3215_);
v_res_3218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3212_, v_as_3213_, v_i_boxed_3216_, v_stop_boxed_3217_);
lean_dec_ref(v_as_3213_);
lean_dec_ref(v_ver_3212_);
v_r_3219_ = lean_box(v_res_3218_);
return v_r_3219_;
}
}
uint8_t l_Lake_VerRange_test(lean_object* v_self_3220_, lean_object* v_ver_3221_){
_start:
{
lean_object* v_clauses_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; uint8_t v___x_3225_; 
v_clauses_3222_ = lean_ctor_get(v_self_3220_, 1);
v___x_3223_ = lean_unsigned_to_nat(0u);
v___x_3224_ = lean_array_get_size(v_clauses_3222_);
v___x_3225_ = lean_nat_dec_lt(v___x_3223_, v___x_3224_);
if (v___x_3225_ == 0)
{
return v___x_3225_;
}
else
{
if (v___x_3225_ == 0)
{
return v___x_3225_;
}
else
{
size_t v___x_3226_; size_t v___x_3227_; uint8_t v___x_3228_; 
v___x_3226_ = ((size_t)0ULL);
v___x_3227_ = lean_usize_of_nat(v___x_3224_);
v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3221_, v_clauses_3222_, v___x_3226_, v___x_3227_);
return v___x_3228_;
}
}
}
}
LEAN_EXPORT void l_Lake_VerRange_test_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3220_ = stack[0].m_obj;
lean_object* v_ver_3221_ = stack[1].m_obj;
uint8_t v_res_3229_;
v_res_3229_ = l_Lake_VerRange_test(v_self_3220_, v_ver_3221_);
stack->m_num = v_res_3229_;
}
LEAN_EXPORT lean_object* l_Lake_VerRange_test___boxed(lean_object* v_self_3230_, lean_object* v_ver_3231_){
_start:
{
uint8_t v_res_3232_; lean_object* v_r_3233_; 
v_res_3232_ = l_Lake_VerRange_test(v_self_3230_, v_ver_3231_);
lean_dec_ref(v_ver_3231_);
lean_dec_ref(v_self_3230_);
v_r_3233_ = lean_box(v_res_3232_);
return v_r_3233_;
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
