// Lean compiler output
// Module: Lake.Util.Version
// Imports: public import Lean.Data.Json public import Lake.Util.Date public import Init.Control.Do import Init.Data.String.TakeDrop import Lean.Data.Trie import Init.Data.String.Search import Init.Omega
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
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
lean_object* lean_string_length(lean_object*);
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
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pr-release-"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lake_VerComparator_wild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedStdVer_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_VerComparator_wild___closed__0 = (const lean_object*)&l_Lake_VerComparator_wild___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_VerComparator_wild = (const lean_object*)&l_Lake_VerComparator_wild___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_VerComparator_instInhabited = (const lean_object*)&l_Lake_VerComparator_wild___closed__0_value;
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
lean_dec_ref(v___x_83_);
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
lean_dec_ref(v___x_106_);
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
lean_dec_ref(v_t_132_);
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
lean_dec_ref(v_a_264_);
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
lean_dec_ref(v___x_300_);
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
lean_dec_ref(v___x_300_);
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
lean_dec_ref(v___x_515_);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_array_fget_borrowed(v_a_501_, v___x_517_);
v___x_519_ = l_String_Slice_toNat_x3f(v___x_518_);
if (lean_obj_tag(v___x_519_) == 1)
{
lean_object* v_val_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_val_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_val_520_);
lean_dec_ref(v___x_519_);
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
lean_dec_ref(v___x_523_);
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
lean_dec_ref(v___x_581_);
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
v___x_700_ = lean_string_dec_lt(v_specialDescr_693_, v_specialDescr_695_);
if (v___x_700_ == 0)
{
uint8_t v___x_701_; 
v___x_701_ = lean_string_dec_eq(v_specialDescr_693_, v_specialDescr_695_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; 
v___x_702_ = 2;
return v___x_702_;
}
else
{
return v___x_696_;
}
}
else
{
uint8_t v___x_703_; 
v___x_703_ = 0;
return v___x_703_;
}
}
else
{
uint8_t v___x_704_; 
v___x_704_ = 0;
return v___x_704_;
}
}
else
{
uint8_t v___x_705_; 
v___x_705_ = lean_string_dec_eq(v_specialDescr_695_, v___x_697_);
if (v___x_705_ == 0)
{
uint8_t v___x_706_; 
v___x_706_ = 2;
return v___x_706_;
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
LEAN_EXPORT lean_object* l_Lake_StdVer_compare___boxed(lean_object* v_a_707_, lean_object* v_b_708_){
_start:
{
uint8_t v_res_709_; lean_object* v_r_710_; 
v_res_709_ = l_Lake_StdVer_compare(v_a_707_, v_b_708_);
lean_dec_ref(v_b_708_);
lean_dec_ref(v_a_707_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
static lean_object* _init_l_Lake_StdVer_instLT(void){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_box(0);
return v___x_713_;
}
}
static lean_object* _init_l_Lake_StdVer_instLE(void){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_box(0);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0(lean_object* v_x_715_, lean_object* v_y_716_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = l_Lake_StdVer_compare(v_x_715_, v_y_716_);
if (v___x_717_ == 2)
{
lean_inc_ref(v_y_716_);
return v_y_716_;
}
else
{
lean_inc_ref(v_x_715_);
return v_x_715_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0___boxed(lean_object* v_x_718_, lean_object* v_y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lake_StdVer_instMin___lam__0(v_x_718_, v_y_719_);
lean_dec_ref(v_y_719_);
lean_dec_ref(v_x_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0(lean_object* v_x_723_, lean_object* v_y_724_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = l_Lake_StdVer_compare(v_x_723_, v_y_724_);
if (v___x_725_ == 2)
{
lean_inc_ref(v_x_723_);
return v_x_723_;
}
else
{
lean_inc_ref(v_y_724_);
return v_y_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0___boxed(lean_object* v_x_726_, lean_object* v_y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lake_StdVer_instMax___lam__0(v_x_726_, v_y_727_);
lean_dec_ref(v_y_727_);
lean_dec_ref(v_x_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parseM(lean_object* v_s_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_733_; 
lean_inc_ref(v_s_731_);
v___x_733_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_731_, v_a_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
v_a_735_ = lean_ctor_get(v___x_733_, 1);
lean_inc(v_a_735_);
lean_dec_ref(v___x_733_);
v___x_736_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_731_, v_a_735_);
lean_dec_ref(v_s_731_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_746_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_a_738_ = lean_ctor_get(v___x_736_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_746_ == 0)
{
v___x_740_ = v___x_736_;
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v_a_734_);
lean_ctor_set(v___x_742_, 1, v_a_737_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_738_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
else
{
lean_object* v_a_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_a_734_);
v_a_747_ = lean_ctor_get(v___x_736_, 0);
v_a_748_ = lean_ctor_get(v___x_736_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_736_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_inc(v_a_747_);
lean_dec(v___x_736_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_747_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v_s_731_);
v_a_756_ = lean_ctor_get(v___x_733_, 0);
v_a_757_ = lean_ctor_get(v___x_733_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_733_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_inc(v_a_756_);
lean_dec(v___x_733_);
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
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parse(lean_object* v_s_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_767_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_string_utf8_byte_size(v_s_766_);
v___x_770_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_766_, v___x_767_, v___x_768_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_toString(lean_object* v_ver_772_){
_start:
{
lean_object* v_toSemVerCore_773_; lean_object* v_specialDescr_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_toSemVerCore_773_ = lean_ctor_get(v_ver_772_, 0);
lean_inc_ref(v_toSemVerCore_773_);
v_specialDescr_774_ = lean_ctor_get(v_ver_772_, 1);
lean_inc_ref(v_specialDescr_774_);
lean_dec_ref(v_ver_772_);
v___x_775_ = lean_string_utf8_byte_size(v_specialDescr_774_);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_nat_dec_eq(v___x_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_778_ = l_Lake_SemVerCore_toString(v_toSemVerCore_773_);
v___x_779_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_780_ = lean_string_append(v___x_778_, v___x_779_);
v___x_781_ = lean_string_append(v___x_780_, v_specialDescr_774_);
lean_dec_ref(v_specialDescr_774_);
return v___x_781_;
}
else
{
lean_object* v___x_782_; 
lean_dec_ref(v_specialDescr_774_);
v___x_782_ = l_Lake_SemVerCore_toString(v_toSemVerCore_773_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instToJson___lam__0(lean_object* v_x_785_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = l_Lake_StdVer_toString(v_x_785_);
v___x_787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instFromJson___lam__0(lean_object* v_x_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Json_getStr_x3f(v_x_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_a_800_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_791_);
v___x_801_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_string_utf8_byte_size(v_a_800_);
v___x_804_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_a_800_, v___x_801_, v___x_802_, v___x_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx(lean_object* v_x_813_){
_start:
{
switch(lean_obj_tag(v_x_813_))
{
case 0:
{
lean_object* v___x_814_; 
v___x_814_ = lean_unsigned_to_nat(0u);
return v___x_814_;
}
case 1:
{
lean_object* v___x_815_; 
v___x_815_ = lean_unsigned_to_nat(1u);
return v___x_815_;
}
case 2:
{
lean_object* v___x_816_; 
v___x_816_ = lean_unsigned_to_nat(2u);
return v___x_816_;
}
default: 
{
lean_object* v___x_817_; 
v___x_817_ = lean_unsigned_to_nat(3u);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___boxed(lean_object* v_x_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lake_ToolchainVer_ctorIdx(v_x_818_);
lean_dec_ref(v_x_818_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___redArg(lean_object* v_t_820_, lean_object* v_k_821_){
_start:
{
switch(lean_obj_tag(v_t_820_))
{
case 1:
{
lean_object* v_date_822_; lean_object* v_rev_823_; lean_object* v___x_824_; 
v_date_822_ = lean_ctor_get(v_t_820_, 0);
lean_inc_ref(v_date_822_);
v_rev_823_ = lean_ctor_get(v_t_820_, 1);
lean_inc(v_rev_823_);
lean_dec_ref(v_t_820_);
v___x_824_ = lean_apply_2(v_k_821_, v_date_822_, v_rev_823_);
return v___x_824_;
}
case 2:
{
lean_object* v_n_825_; lean_object* v___x_826_; 
v_n_825_ = lean_ctor_get(v_t_820_, 0);
lean_inc(v_n_825_);
lean_dec_ref(v_t_820_);
v___x_826_ = lean_apply_1(v_k_821_, v_n_825_);
return v___x_826_;
}
default: 
{
lean_object* v_ver_827_; lean_object* v___x_828_; 
v_ver_827_ = lean_ctor_get(v_t_820_, 0);
lean_inc_ref(v_ver_827_);
lean_dec_ref(v_t_820_);
v___x_828_ = lean_apply_1(v_k_821_, v_ver_827_);
return v___x_828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim(lean_object* v_motive_829_, lean_object* v_ctorIdx_830_, lean_object* v_t_831_, lean_object* v_h_832_, lean_object* v_k_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_831_, v_k_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___boxed(lean_object* v_motive_835_, lean_object* v_ctorIdx_836_, lean_object* v_t_837_, lean_object* v_h_838_, lean_object* v_k_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lake_ToolchainVer_ctorElim(v_motive_835_, v_ctorIdx_836_, v_t_837_, v_h_838_, v_k_839_);
lean_dec(v_ctorIdx_836_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim___redArg(lean_object* v_t_841_, lean_object* v_release_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_841_, v_release_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim(lean_object* v_motive_844_, lean_object* v_t_845_, lean_object* v_h_846_, lean_object* v_release_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_845_, v_release_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim___redArg(lean_object* v_t_849_, lean_object* v_nightly_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_849_, v_nightly_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim(lean_object* v_motive_852_, lean_object* v_t_853_, lean_object* v_h_854_, lean_object* v_nightly_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_853_, v_nightly_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim___redArg(lean_object* v_t_857_, lean_object* v_pr_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_857_, v_pr_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim(lean_object* v_motive_860_, lean_object* v_t_861_, lean_object* v_h_862_, lean_object* v_pr_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_861_, v_pr_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim___redArg(lean_object* v_t_865_, lean_object* v_other_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_865_, v_other_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim(lean_object* v_motive_868_, lean_object* v_t_869_, lean_object* v_h_870_, lean_object* v_other_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_869_, v_other_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override___redArg(lean_object* v_t_873_, lean_object* v_release_874_, lean_object* v_nightly_875_, lean_object* v_pr_876_, lean_object* v_other_877_){
_start:
{
switch(lean_obj_tag(v_t_873_))
{
case 0:
{
lean_object* v_ver_878_; lean_object* v___x_879_; 
lean_dec(v_other_877_);
lean_dec(v_pr_876_);
lean_dec(v_nightly_875_);
v_ver_878_ = lean_ctor_get(v_t_873_, 1);
lean_inc_ref(v_ver_878_);
lean_dec_ref(v_t_873_);
v___x_879_ = lean_apply_1(v_release_874_, v_ver_878_);
return v___x_879_;
}
case 1:
{
lean_object* v_date_880_; lean_object* v_rev_881_; lean_object* v___x_882_; 
lean_dec(v_other_877_);
lean_dec(v_pr_876_);
lean_dec(v_release_874_);
v_date_880_ = lean_ctor_get(v_t_873_, 1);
lean_inc_ref(v_date_880_);
v_rev_881_ = lean_ctor_get(v_t_873_, 2);
lean_inc(v_rev_881_);
lean_dec_ref(v_t_873_);
v___x_882_ = lean_apply_2(v_nightly_875_, v_date_880_, v_rev_881_);
return v___x_882_;
}
case 2:
{
lean_object* v_n_883_; lean_object* v___x_884_; 
lean_dec(v_other_877_);
lean_dec(v_nightly_875_);
lean_dec(v_release_874_);
v_n_883_ = lean_ctor_get(v_t_873_, 1);
lean_inc(v_n_883_);
lean_dec_ref(v_t_873_);
v___x_884_ = lean_apply_1(v_pr_876_, v_n_883_);
return v___x_884_;
}
default: 
{
lean_object* v_v_885_; lean_object* v___x_886_; 
lean_dec(v_pr_876_);
lean_dec(v_nightly_875_);
lean_dec(v_release_874_);
v_v_885_ = lean_ctor_get(v_t_873_, 1);
lean_inc_ref(v_v_885_);
lean_dec_ref(v_t_873_);
v___x_886_ = lean_apply_1(v_other_877_, v_v_885_);
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override(lean_object* v_motive_887_, lean_object* v_t_888_, lean_object* v_release_889_, lean_object* v_nightly_890_, lean_object* v_pr_891_, lean_object* v_other_892_){
_start:
{
switch(lean_obj_tag(v_t_888_))
{
case 0:
{
lean_object* v_ver_893_; lean_object* v___x_894_; 
lean_dec(v_other_892_);
lean_dec(v_pr_891_);
lean_dec(v_nightly_890_);
v_ver_893_ = lean_ctor_get(v_t_888_, 1);
lean_inc_ref(v_ver_893_);
lean_dec_ref(v_t_888_);
v___x_894_ = lean_apply_1(v_release_889_, v_ver_893_);
return v___x_894_;
}
case 1:
{
lean_object* v_date_895_; lean_object* v_rev_896_; lean_object* v___x_897_; 
lean_dec(v_other_892_);
lean_dec(v_pr_891_);
lean_dec(v_release_889_);
v_date_895_ = lean_ctor_get(v_t_888_, 1);
lean_inc_ref(v_date_895_);
v_rev_896_ = lean_ctor_get(v_t_888_, 2);
lean_inc(v_rev_896_);
lean_dec_ref(v_t_888_);
v___x_897_ = lean_apply_2(v_nightly_890_, v_date_895_, v_rev_896_);
return v___x_897_;
}
case 2:
{
lean_object* v_n_898_; lean_object* v___x_899_; 
lean_dec(v_other_892_);
lean_dec(v_nightly_890_);
lean_dec(v_release_889_);
v_n_898_ = lean_ctor_get(v_t_888_, 1);
lean_inc(v_n_898_);
lean_dec_ref(v_t_888_);
v___x_899_ = lean_apply_1(v_pr_891_, v_n_898_);
return v___x_899_;
}
default: 
{
lean_object* v_v_900_; lean_object* v___x_901_; 
lean_dec(v_pr_891_);
lean_dec(v_nightly_890_);
lean_dec(v_release_889_);
v_v_900_ = lean_ctor_get(v_t_888_, 1);
lean_inc_ref(v_v_900_);
lean_dec_ref(v_t_888_);
v___x_901_ = lean_apply_1(v_other_892_, v_v_900_);
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release___override(lean_object* v_ver_903_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_904_ = ((lean_object*)(l_Lake_ToolchainVer_release___override___closed__0));
lean_inc_ref(v_ver_903_);
v___x_905_ = l_Lake_StdVer_toString(v_ver_903_);
v___x_906_ = lean_string_append(v___x_904_, v___x_905_);
lean_dec_ref(v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v_ver_903_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly___override(lean_object* v_date_910_, lean_object* v_rev_911_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___y_916_; 
v___x_912_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__0));
lean_inc_ref(v_date_910_);
v___x_913_ = l_Lake_Date_toString(v_date_910_);
v___x_914_ = lean_string_append(v___x_912_, v___x_913_);
lean_dec_ref(v___x_913_);
if (lean_obj_tag(v_rev_911_) == 0)
{
lean_object* v___x_919_; 
v___x_919_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___y_916_ = v___x_919_;
goto v___jp_915_;
}
else
{
lean_object* v_val_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_val_920_ = lean_ctor_get(v_rev_911_, 0);
v___x_921_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
lean_inc(v_val_920_);
v___x_922_ = l_Nat_reprFast(v_val_920_);
v___x_923_ = lean_string_append(v___x_921_, v___x_922_);
lean_dec_ref(v___x_922_);
v___y_916_ = v___x_923_;
goto v___jp_915_;
}
v___jp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_string_append(v___x_914_, v___y_916_);
lean_dec_ref(v___y_916_);
v___x_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v_date_910_);
lean_ctor_set(v___x_918_, 2, v_rev_911_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr___override(lean_object* v_n_925_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_926_ = ((lean_object*)(l_Lake_ToolchainVer_pr___override___closed__0));
lean_inc(v_n_925_);
v___x_927_ = l_Nat_reprFast(v_n_925_);
v___x_928_ = lean_string_append(v___x_926_, v___x_927_);
lean_dec_ref(v___x_927_);
v___x_929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_n_925_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other___override(lean_object* v_v_930_){
_start:
{
lean_object* v___x_931_; 
lean_inc_ref(v_v_930_);
v___x_931_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_931_, 0, v_v_930_);
lean_ctor_set(v___x_931_, 1, v_v_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override(lean_object* v_x_932_){
_start:
{
lean_object* v_toString_933_; 
v_toString_933_ = lean_ctor_get(v_x_932_, 0);
lean_inc_ref(v_toString_933_);
return v_toString_933_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override___boxed(lean_object* v_x_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lake_ToolchainVer_toString___override(v_x_934_);
lean_dec_ref(v_x_934_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_942_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1));
return v___x_944_;
}
else
{
lean_object* v_val_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_956_; 
v_val_945_ = lean_ctor_get(v_x_942_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_x_942_);
if (v_isSharedCheck_956_ == 0)
{
v___x_947_ = v_x_942_;
v_isShared_948_ = v_isSharedCheck_956_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_val_945_);
lean_dec(v_x_942_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_956_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_949_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3));
v___x_950_ = l_Nat_reprFast(v_val_945_);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 3);
lean_ctor_set(v___x_947_, 0, v___x_950_);
v___x_952_ = v___x_947_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_955_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_949_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = l_Repr_addAppParen(v___x_953_, v_x_943_);
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___boxed(lean_object* v_x_957_, lean_object* v_x_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_x_957_, v_x_958_);
lean_dec(v_x_958_);
return v_res_959_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__3(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(2u);
v___x_967_ = lean_nat_to_int(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__4(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_to_int(v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr(lean_object* v_x_988_, lean_object* v_prec_989_){
_start:
{
switch(lean_obj_tag(v_x_988_))
{
case 0:
{
lean_object* v_ver_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1009_; 
v_ver_990_ = lean_ctor_get(v_x_988_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_x_988_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_x_988_, 0);
lean_dec(v_unused_1010_);
v___x_992_ = v_x_988_;
v_isShared_993_ = v_isSharedCheck_1009_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_ver_990_);
lean_dec(v_x_988_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1009_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___y_995_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = lean_unsigned_to_nat(1024u);
v___x_1006_ = lean_nat_dec_le(v___x_1005_, v_prec_989_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_995_ = v___x_1007_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_995_ = v___x_1008_;
goto v___jp_994_;
}
v___jp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_996_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__2));
v___x_997_ = l_Lake_instReprStdVer_repr___redArg(v_ver_990_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 5);
lean_ctor_set(v___x_992_, 1, v___x_997_);
lean_ctor_set(v___x_992_, 0, v___x_996_);
v___x_999_ = v___x_992_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1004_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_inc(v___y_995_);
v___x_1000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___y_995_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = 0;
v___x_1002_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*1, v___x_1001_);
v___x_1003_ = l_Repr_addAppParen(v___x_1002_, v_prec_989_);
return v___x_1003_;
}
}
}
}
case 1:
{
lean_object* v_date_1011_; lean_object* v_rev_1012_; lean_object* v___y_1014_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v_date_1011_ = lean_ctor_get(v_x_988_, 1);
lean_inc_ref(v_date_1011_);
v_rev_1012_ = lean_ctor_get(v_x_988_, 2);
lean_inc(v_rev_1012_);
lean_dec_ref(v_x_988_);
v___x_1027_ = lean_unsigned_to_nat(1024u);
v___x_1028_ = lean_nat_dec_le(v___x_1027_, v_prec_989_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1014_ = v___x_1029_;
goto v___jp_1013_;
}
else
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1014_ = v___x_1030_;
goto v___jp_1013_;
}
v___jp_1013_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1015_ = lean_box(1);
v___x_1016_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__7));
v___x_1017_ = lean_unsigned_to_nat(1024u);
v___x_1018_ = l_Lake_instReprDate_repr___redArg(v_date_1011_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1016_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_1015_);
v___x_1021_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_rev_1012_, v___x_1017_);
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
lean_inc(v___y_1014_);
v___x_1023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___y_1014_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = 0;
v___x_1025_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set_uint8(v___x_1025_, sizeof(void*)*1, v___x_1024_);
v___x_1026_ = l_Repr_addAppParen(v___x_1025_, v_prec_989_);
return v___x_1026_;
}
}
case 2:
{
lean_object* v_n_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1051_; 
v_n_1031_ = lean_ctor_get(v_x_988_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_x_988_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v_x_988_, 0);
lean_dec(v_unused_1052_);
v___x_1033_ = v_x_988_;
v_isShared_1034_ = v_isSharedCheck_1051_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_n_1031_);
lean_dec(v_x_988_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1051_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___y_1036_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = lean_unsigned_to_nat(1024u);
v___x_1048_ = lean_nat_dec_le(v___x_1047_, v_prec_989_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1036_ = v___x_1049_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1036_ = v___x_1050_;
goto v___jp_1035_;
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1037_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__10));
v___x_1038_ = l_Nat_reprFast(v_n_1031_);
v___x_1039_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set_tag(v___x_1033_, 5);
lean_ctor_set(v___x_1033_, 1, v___x_1039_);
lean_ctor_set(v___x_1033_, 0, v___x_1037_);
v___x_1041_ = v___x_1033_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_inc(v___y_1036_);
v___x_1042_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___y_1036_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = 0;
v___x_1044_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*1, v___x_1043_);
v___x_1045_ = l_Repr_addAppParen(v___x_1044_, v_prec_989_);
return v___x_1045_;
}
}
}
}
default: 
{
lean_object* v_v_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1073_; 
v_v_1053_ = lean_ctor_get(v_x_988_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_x_988_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v_x_988_, 0);
lean_dec(v_unused_1074_);
v___x_1055_ = v_x_988_;
v_isShared_1056_ = v_isSharedCheck_1073_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_v_1053_);
lean_dec(v_x_988_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1073_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___y_1058_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = lean_unsigned_to_nat(1024u);
v___x_1070_ = lean_nat_dec_le(v___x_1069_, v_prec_989_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1058_ = v___x_1071_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1058_ = v___x_1072_;
goto v___jp_1057_;
}
v___jp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1059_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__13));
v___x_1060_ = l_String_quote(v_v_1053_);
v___x_1061_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 5);
lean_ctor_set(v___x_1055_, 1, v___x_1061_);
lean_ctor_set(v___x_1055_, 0, v___x_1059_);
v___x_1063_ = v___x_1055_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_inc(v___y_1058_);
v___x_1064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___y_1058_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = 0;
v___x_1066_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*1, v___x_1065_);
v___x_1067_ = l_Repr_addAppParen(v___x_1066_, v_prec_989_);
return v___x_1067_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr___boxed(lean_object* v_x_1075_, lean_object* v_prec_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lake_instReprToolchainVer_repr(v_x_1075_, v_prec_1076_);
lean_dec(v_prec_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer_decEq(lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
switch(lean_obj_tag(v_x_1080_))
{
case 0:
{
if (lean_obj_tag(v_x_1081_) == 0)
{
lean_object* v_ver_1082_; lean_object* v_ver_1083_; uint8_t v___x_1084_; 
v_ver_1082_ = lean_ctor_get(v_x_1080_, 1);
lean_inc_ref(v_ver_1082_);
lean_dec_ref(v_x_1080_);
v_ver_1083_ = lean_ctor_get(v_x_1081_, 1);
lean_inc_ref(v_ver_1083_);
lean_dec_ref(v_x_1081_);
v___x_1084_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_1082_, v_ver_1083_);
lean_dec_ref(v_ver_1083_);
lean_dec_ref(v_ver_1082_);
return v___x_1084_;
}
else
{
uint8_t v___x_1085_; 
lean_dec_ref(v_x_1080_);
lean_dec_ref(v_x_1081_);
v___x_1085_ = 0;
return v___x_1085_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1081_) == 1)
{
lean_object* v_date_1086_; lean_object* v_rev_1087_; lean_object* v_date_1088_; lean_object* v_rev_1089_; uint8_t v___x_1090_; 
v_date_1086_ = lean_ctor_get(v_x_1080_, 1);
lean_inc_ref(v_date_1086_);
v_rev_1087_ = lean_ctor_get(v_x_1080_, 2);
lean_inc(v_rev_1087_);
lean_dec_ref(v_x_1080_);
v_date_1088_ = lean_ctor_get(v_x_1081_, 1);
lean_inc_ref(v_date_1088_);
v_rev_1089_ = lean_ctor_get(v_x_1081_, 2);
lean_inc(v_rev_1089_);
lean_dec_ref(v_x_1081_);
v___x_1090_ = l_Lake_instDecidableEqDate_decEq(v_date_1086_, v_date_1088_);
lean_dec_ref(v_date_1088_);
lean_dec_ref(v_date_1086_);
if (v___x_1090_ == 0)
{
lean_dec(v_rev_1089_);
lean_dec(v_rev_1087_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_1092_ = l_Option_instDecidableEq___redArg(v___x_1091_, v_rev_1087_, v_rev_1089_);
return v___x_1092_;
}
}
else
{
uint8_t v___x_1093_; 
lean_dec_ref(v_x_1080_);
lean_dec_ref(v_x_1081_);
v___x_1093_ = 0;
return v___x_1093_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1081_) == 2)
{
lean_object* v_n_1094_; lean_object* v_n_1095_; uint8_t v___x_1096_; 
v_n_1094_ = lean_ctor_get(v_x_1080_, 1);
lean_inc(v_n_1094_);
lean_dec_ref(v_x_1080_);
v_n_1095_ = lean_ctor_get(v_x_1081_, 1);
lean_inc(v_n_1095_);
lean_dec_ref(v_x_1081_);
v___x_1096_ = lean_nat_dec_eq(v_n_1094_, v_n_1095_);
lean_dec(v_n_1095_);
lean_dec(v_n_1094_);
return v___x_1096_;
}
else
{
uint8_t v___x_1097_; 
lean_dec_ref(v_x_1080_);
lean_dec_ref(v_x_1081_);
v___x_1097_ = 0;
return v___x_1097_;
}
}
default: 
{
if (lean_obj_tag(v_x_1081_) == 3)
{
lean_object* v_v_1098_; lean_object* v_v_1099_; uint8_t v___x_1100_; 
v_v_1098_ = lean_ctor_get(v_x_1080_, 1);
lean_inc_ref(v_v_1098_);
lean_dec_ref(v_x_1080_);
v_v_1099_ = lean_ctor_get(v_x_1081_, 1);
lean_inc_ref(v_v_1099_);
lean_dec_ref(v_x_1081_);
v___x_1100_ = lean_string_dec_eq(v_v_1098_, v_v_1099_);
lean_dec_ref(v_v_1099_);
lean_dec_ref(v_v_1098_);
return v___x_1100_;
}
else
{
uint8_t v___x_1101_; 
lean_dec_ref(v_x_1080_);
lean_dec_ref(v_x_1081_);
v___x_1101_ = 0;
return v___x_1101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer_decEq___boxed(lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
uint8_t v_res_1104_; lean_object* v_r_1105_; 
v_res_1104_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1102_, v_x_1103_);
v_r_1105_ = lean_box(v_res_1104_);
return v_r_1105_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer(lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
uint8_t v___x_1108_; 
v___x_1108_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1106_, v_x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer___boxed(lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Lake_instDecidableEqToolchainVer(v_x_1109_, v_x_1110_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1117_ = lean_string_utf8_byte_size(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(lean_object* v_s_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1119_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1120_ = lean_string_utf8_byte_size(v_s_1118_);
v___x_1121_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1);
v___x_1122_ = lean_nat_dec_le(v___x_1121_, v___x_1120_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v_s_1118_);
v___x_1123_ = lean_box(0);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_string_memcmp(v_s_1118_, v___x_1119_, v___x_1124_, v___x_1124_, v___x_1121_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_dec_ref(v_s_1118_);
v___x_1126_ = lean_box(0);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_inc_ref(v_s_1118_);
v___x_1127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1127_, 0, v_s_1118_);
lean_ctor_set(v___x_1127_, 1, v___x_1124_);
lean_ctor_set(v___x_1127_, 2, v___x_1120_);
v___x_1128_ = l_String_Slice_pos_x21(v___x_1127_, v___x_1121_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1129_, 0, v_s_1118_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
lean_ctor_set(v___x_1129_, 2, v___x_1120_);
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(lean_object* v_s_1131_, lean_object* v_pat_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v_s_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(lean_object* v_s_1134_, lean_object* v_pat_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(v_s_1134_, v_pat_1135_);
lean_dec_ref(v_pat_1135_);
return v_res_1136_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1138_ = lean_string_utf8_byte_size(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(lean_object* v_s_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1140_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1141_ = lean_string_utf8_byte_size(v_s_1139_);
v___x_1142_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0);
v___x_1143_ = lean_nat_dec_le(v___x_1142_, v___x_1141_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref(v_s_1139_);
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = lean_string_memcmp(v_s_1139_, v___x_1140_, v___x_1145_, v___x_1145_, v___x_1142_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_dec_ref(v_s_1139_);
v___x_1147_ = lean_box(0);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_inc_ref(v_s_1139_);
v___x_1148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1148_, 0, v_s_1139_);
lean_ctor_set(v___x_1148_, 1, v___x_1145_);
lean_ctor_set(v___x_1148_, 2, v___x_1141_);
v___x_1149_ = l_String_Slice_pos_x21(v___x_1148_, v___x_1142_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1150_, 0, v_s_1139_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
lean_ctor_set(v___x_1150_, 2, v___x_1141_);
v___x_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(lean_object* v_s_1152_, lean_object* v_pat_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v_s_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(lean_object* v_s_1155_, lean_object* v_pat_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(v_s_1155_, v_pat_1156_);
lean_dec_ref(v_pat_1156_);
return v_res_1157_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__0));
v___x_1160_ = lean_string_utf8_byte_size(v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object* v_s_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1162_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__0));
v___x_1163_ = lean_string_utf8_byte_size(v_s_1161_);
v___x_1164_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1);
v___x_1165_ = lean_nat_dec_le(v___x_1164_, v___x_1163_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec_ref(v_s_1161_);
v___x_1166_ = lean_box(0);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = lean_string_memcmp(v_s_1161_, v___x_1162_, v___x_1167_, v___x_1167_, v___x_1164_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
lean_dec_ref(v_s_1161_);
v___x_1169_ = lean_box(0);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_inc_ref(v_s_1161_);
v___x_1170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1170_, 0, v_s_1161_);
lean_ctor_set(v___x_1170_, 1, v___x_1167_);
lean_ctor_set(v___x_1170_, 2, v___x_1163_);
v___x_1171_ = l_String_Slice_pos_x21(v___x_1170_, v___x_1164_);
lean_dec_ref(v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1172_, 0, v_s_1161_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
lean_ctor_set(v___x_1172_, 2, v___x_1163_);
v___x_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2(lean_object* v_s_1174_, lean_object* v_pat_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v_s_1174_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object* v_s_1177_, lean_object* v_pat_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2(v_s_1177_, v_pat_1178_);
lean_dec_ref(v_pat_1178_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object* v___x_1180_, lean_object* v_ver_1181_, lean_object* v_a_1182_, lean_object* v_b_1183_){
_start:
{
lean_object* v_startInclusive_1184_; lean_object* v_endExclusive_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v_startInclusive_1184_ = lean_ctor_get(v___x_1180_, 1);
v_endExclusive_1185_ = lean_ctor_get(v___x_1180_, 2);
v___x_1186_ = lean_nat_sub(v_endExclusive_1185_, v_startInclusive_1184_);
v___x_1187_ = lean_nat_dec_eq(v_a_1182_, v___x_1186_);
lean_dec(v___x_1186_);
if (v___x_1187_ == 0)
{
uint32_t v___x_1188_; uint32_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1188_ = lean_string_utf8_get_fast(v_ver_1181_, v_a_1182_);
v___x_1189_ = 58;
v___x_1190_ = lean_uint32_dec_eq(v___x_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_string_utf8_next_fast(v_ver_1181_, v_a_1182_);
lean_dec(v_a_1182_);
v_a_1182_ = v___x_1192_;
v_b_1183_ = v___x_1191_;
goto _start;
}
else
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_a_1182_);
return v___x_1194_;
}
}
else
{
lean_dec(v_a_1182_);
lean_inc(v_b_1183_);
return v_b_1183_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg___boxed(lean_object* v___x_1195_, lean_object* v_ver_1196_, lean_object* v_a_1197_, lean_object* v_b_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___x_1195_, v_ver_1196_, v_a_1197_, v_b_1198_);
lean_dec(v_b_1198_);
lean_dec_ref(v_ver_1196_);
lean_dec_ref(v___x_1195_);
return v_res_1199_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__1(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1202_ = lean_string_utf8_byte_size(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__2(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1204_ = lean_string_utf8_byte_size(v___x_1203_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__4(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__3));
v___x_1207_ = lean_string_utf8_byte_size(v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofString(lean_object* v_ver_1208_){
_start:
{
lean_object* v___y_1210_; uint8_t v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1231_; uint8_t v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1242_; uint8_t v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; uint8_t v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___y_1328_; lean_object* v_searcher_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_searcher_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_string_utf8_byte_size(v_ver_1208_);
lean_inc_ref(v_ver_1208_);
v___x_1338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1338_, 0, v_ver_1208_);
lean_ctor_set(v___x_1338_, 1, v_searcher_1336_);
lean_ctor_set(v___x_1338_, 2, v___x_1337_);
v___x_1339_ = lean_box(0);
v___x_1340_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___x_1338_, v_ver_1208_, v_searcher_1336_, v___x_1339_);
lean_dec_ref(v___x_1338_);
if (lean_obj_tag(v___x_1340_) == 0)
{
v___y_1328_ = v___x_1337_;
goto v___jp_1327_;
}
else
{
lean_object* v_val_1341_; 
v_val_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_val_1341_);
lean_dec_ref(v___x_1340_);
v___y_1328_ = v_val_1341_;
goto v___jp_1327_;
}
v___jp_1209_:
{
if (v___y_1211_ == 0)
{
lean_object* v___x_1215_; 
v___x_1215_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v___y_1212_);
if (lean_obj_tag(v___x_1215_) == 1)
{
lean_object* v_val_1216_; lean_object* v_startInclusive_1217_; lean_object* v_endExclusive_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_val_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_val_1216_);
lean_dec_ref(v___x_1215_);
v_startInclusive_1217_ = lean_ctor_get(v_val_1216_, 1);
v_endExclusive_1218_ = lean_ctor_get(v_val_1216_, 2);
v___x_1219_ = lean_nat_sub(v_endExclusive_1218_, v_startInclusive_1217_);
v___x_1220_ = lean_nat_dec_eq(v___x_1219_, v___y_1214_);
lean_dec(v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1221_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1222_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__1, &l_Lake_ToolchainVer_ofString___closed__1_once, _init_l_Lake_ToolchainVer_ofString___closed__1);
v___x_1223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v___y_1214_);
lean_ctor_set(v___x_1223_, 2, v___x_1222_);
v___x_1224_ = l_String_Slice_beq(v_val_1216_, v___x_1223_);
lean_dec_ref(v___x_1223_);
lean_dec(v_val_1216_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1210_);
lean_inc_ref(v_ver_1208_);
v___x_1225_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1225_, 0, v_ver_1208_);
lean_ctor_set(v___x_1225_, 1, v_ver_1208_);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; 
lean_dec_ref(v_ver_1208_);
v___x_1226_ = l_Lake_ToolchainVer_nightly___override(v___y_1210_, v___y_1213_);
return v___x_1226_;
}
}
else
{
lean_object* v___x_1227_; 
lean_dec(v_val_1216_);
lean_dec(v___y_1214_);
lean_dec_ref(v_ver_1208_);
v___x_1227_ = l_Lake_ToolchainVer_nightly___override(v___y_1210_, v___y_1213_);
return v___x_1227_;
}
}
else
{
lean_object* v___x_1228_; 
lean_dec(v___x_1215_);
lean_dec(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1210_);
lean_inc_ref(v_ver_1208_);
v___x_1228_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_ver_1208_);
lean_ctor_set(v___x_1228_, 1, v_ver_1208_);
return v___x_1228_;
}
}
else
{
lean_object* v___x_1229_; 
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_ver_1208_);
v___x_1229_ = l_Lake_ToolchainVer_nightly___override(v___y_1210_, v___y_1213_);
return v___x_1229_;
}
}
v___jp_1230_:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_string_length(v___y_1234_);
lean_dec_ref(v___y_1234_);
v___x_1239_ = lean_nat_dec_le(v___x_1238_, v___y_1235_);
lean_dec(v___y_1235_);
if (v___x_1239_ == 0)
{
if (lean_obj_tag(v___y_1237_) == 0)
{
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1233_);
lean_dec_ref(v___y_1231_);
lean_inc_ref(v_ver_1208_);
v___x_1240_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_ver_1208_);
lean_ctor_set(v___x_1240_, 1, v_ver_1208_);
return v___x_1240_;
}
else
{
v___y_1210_ = v___y_1231_;
v___y_1211_ = v___y_1232_;
v___y_1212_ = v___y_1233_;
v___y_1213_ = v___y_1237_;
v___y_1214_ = v___y_1236_;
goto v___jp_1209_;
}
}
else
{
v___y_1210_ = v___y_1231_;
v___y_1211_ = v___y_1232_;
v___y_1212_ = v___y_1233_;
v___y_1213_ = v___y_1237_;
v___y_1214_ = v___y_1236_;
goto v___jp_1209_;
}
}
else
{
v___y_1210_ = v___y_1231_;
v___y_1211_ = v___y_1232_;
v___y_1212_ = v___y_1233_;
v___y_1213_ = v___y_1237_;
v___y_1214_ = v___y_1236_;
goto v___jp_1209_;
}
}
v___jp_1241_:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_box(0);
v___y_1231_ = v___y_1242_;
v___y_1232_ = v___y_1243_;
v___y_1233_ = v___y_1244_;
v___y_1234_ = v___y_1245_;
v___y_1235_ = v___y_1246_;
v___y_1236_ = v___y_1247_;
v___y_1237_ = v___x_1248_;
goto v___jp_1230_;
}
v___jp_1249_:
{
lean_object* v___x_1254_; 
lean_inc_ref(v___y_1251_);
v___x_1254_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v___y_1251_);
if (lean_obj_tag(v___x_1254_) == 1)
{
lean_object* v_val_1255_; lean_object* v_rest_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec_ref(v___y_1251_);
v_val_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1255_);
lean_dec_ref(v___x_1254_);
v_rest_1256_ = l_String_Slice_toString(v_val_1255_);
lean_dec(v_val_1255_);
v___x_1257_ = lean_unsigned_to_nat(10u);
v___x_1258_ = lean_string_utf8_byte_size(v_rest_1256_);
lean_inc_n(v___y_1253_, 3);
lean_inc_ref_n(v_rest_1256_, 2);
v___x_1259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1259_, 0, v_rest_1256_);
lean_ctor_set(v___x_1259_, 1, v___y_1253_);
lean_ctor_set(v___x_1259_, 2, v___x_1258_);
v___x_1260_ = l_String_Slice_Pos_nextn(v___x_1259_, v___y_1253_, v___x_1257_);
lean_dec_ref(v___x_1259_);
lean_inc(v___x_1260_);
v___x_1261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1261_, 0, v_rest_1256_);
lean_ctor_set(v___x_1261_, 1, v___y_1253_);
lean_ctor_set(v___x_1261_, 2, v___x_1260_);
v___x_1262_ = l_String_Slice_toString(v___x_1261_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = l_Lake_Date_ofString_x3f(v___x_1262_);
if (lean_obj_tag(v___x_1263_) == 1)
{
lean_object* v_val_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_val_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_val_1264_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1266_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__2, &l_Lake_ToolchainVer_ofString___closed__2_once, _init_l_Lake_ToolchainVer_ofString___closed__2);
v___x_1267_ = lean_nat_sub(v___x_1258_, v___x_1260_);
v___x_1268_ = lean_nat_dec_le(v___x_1266_, v___x_1267_);
lean_dec(v___x_1267_);
if (v___x_1268_ == 0)
{
lean_dec(v___x_1260_);
v___y_1242_ = v_val_1264_;
v___y_1243_ = v___y_1250_;
v___y_1244_ = v___y_1252_;
v___y_1245_ = v_rest_1256_;
v___y_1246_ = v___x_1257_;
v___y_1247_ = v___y_1253_;
goto v___jp_1241_;
}
else
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_string_memcmp(v_rest_1256_, v___x_1265_, v___x_1260_, v___y_1253_, v___x_1266_);
if (v___x_1269_ == 0)
{
lean_dec(v___x_1260_);
v___y_1242_ = v_val_1264_;
v___y_1243_ = v___y_1250_;
v___y_1244_ = v___y_1252_;
v___y_1245_ = v_rest_1256_;
v___y_1246_ = v___x_1257_;
v___y_1247_ = v___y_1253_;
goto v___jp_1241_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_inc(v___x_1260_);
lean_inc_ref_n(v_rest_1256_, 2);
v___x_1270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1270_, 0, v_rest_1256_);
lean_ctor_set(v___x_1270_, 1, v___x_1260_);
lean_ctor_set(v___x_1270_, 2, v___x_1258_);
v___x_1271_ = l_String_Slice_pos_x21(v___x_1270_, v___x_1266_);
lean_dec_ref(v___x_1270_);
v___x_1272_ = lean_nat_add(v___x_1260_, v___x_1271_);
lean_dec(v___x_1271_);
lean_dec(v___x_1260_);
v___x_1273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1273_, 0, v_rest_1256_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
lean_ctor_set(v___x_1273_, 2, v___x_1258_);
v___x_1274_ = l_String_Slice_toString(v___x_1273_);
lean_dec_ref(v___x_1273_);
v___x_1275_ = lean_string_utf8_byte_size(v___x_1274_);
lean_inc(v___y_1253_);
v___x_1276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___y_1253_);
lean_ctor_set(v___x_1276_, 2, v___x_1275_);
v___x_1277_ = l_String_Slice_toNat_x3f(v___x_1276_);
lean_dec_ref(v___x_1276_);
v___y_1231_ = v_val_1264_;
v___y_1232_ = v___y_1250_;
v___y_1233_ = v___y_1252_;
v___y_1234_ = v_rest_1256_;
v___y_1235_ = v___x_1257_;
v___y_1236_ = v___y_1253_;
v___y_1237_ = v___x_1277_;
goto v___jp_1230_;
}
}
}
else
{
lean_object* v___x_1278_; 
lean_dec(v___x_1263_);
lean_dec(v___x_1260_);
lean_dec_ref(v_rest_1256_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_inc_ref(v_ver_1208_);
v___x_1278_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1278_, 0, v_ver_1208_);
lean_ctor_set(v___x_1278_, 1, v_ver_1208_);
return v___x_1278_;
}
}
else
{
lean_object* v___x_1279_; 
lean_dec(v___x_1254_);
v___x_1279_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___y_1251_);
if (lean_obj_tag(v___x_1279_) == 1)
{
lean_object* v_val_1280_; lean_object* v___x_1281_; 
lean_dec(v___y_1253_);
v_val_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1280_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = l_String_Slice_toNat_x3f(v_val_1280_);
lean_dec(v_val_1280_);
if (lean_obj_tag(v___x_1281_) == 1)
{
if (v___y_1250_ == 0)
{
lean_object* v_val_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_val_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_val_1282_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = ((lean_object*)(l_Lake_ToolchainVer_prOrigin___closed__0));
v___x_1284_ = lean_string_dec_eq(v___y_1252_, v___x_1283_);
lean_dec_ref(v___y_1252_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
lean_dec(v_val_1282_);
lean_inc_ref(v_ver_1208_);
v___x_1285_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1285_, 0, v_ver_1208_);
lean_ctor_set(v___x_1285_, 1, v_ver_1208_);
return v___x_1285_;
}
else
{
lean_object* v___x_1286_; 
lean_dec_ref(v_ver_1208_);
v___x_1286_ = l_Lake_ToolchainVer_pr___override(v_val_1282_);
return v___x_1286_;
}
}
else
{
lean_object* v_val_1287_; lean_object* v___x_1288_; 
lean_dec_ref(v___y_1252_);
lean_dec_ref(v_ver_1208_);
v_val_1287_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_val_1287_);
lean_dec_ref(v___x_1281_);
v___x_1288_ = l_Lake_ToolchainVer_pr___override(v_val_1287_);
return v___x_1288_;
}
}
else
{
lean_object* v___x_1289_; 
lean_dec(v___x_1281_);
lean_dec_ref(v___y_1252_);
lean_inc_ref(v_ver_1208_);
v___x_1289_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1289_, 0, v_ver_1208_);
lean_ctor_set(v___x_1289_, 1, v_ver_1208_);
return v___x_1289_;
}
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec(v___x_1279_);
v___x_1290_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_1291_ = lean_string_utf8_byte_size(v_ver_1208_);
lean_inc_ref(v_ver_1208_);
v___x_1292_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_ver_1208_, v___x_1290_, v___y_1253_, v___x_1291_);
if (lean_obj_tag(v___x_1292_) == 1)
{
if (v___y_1250_ == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1295_ = lean_string_dec_eq(v___y_1252_, v___x_1294_);
lean_dec_ref(v___y_1252_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
lean_dec(v_a_1293_);
lean_inc_ref(v_ver_1208_);
v___x_1296_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1296_, 0, v_ver_1208_);
lean_ctor_set(v___x_1296_, 1, v_ver_1208_);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; 
lean_dec_ref(v_ver_1208_);
v___x_1297_ = l_Lake_ToolchainVer_release___override(v_a_1293_);
return v___x_1297_;
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1299_; 
lean_dec_ref(v___y_1252_);
lean_dec_ref(v_ver_1208_);
v_a_1298_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1292_);
v___x_1299_ = l_Lake_ToolchainVer_release___override(v_a_1298_);
return v___x_1299_;
}
}
else
{
lean_object* v___x_1300_; 
lean_dec_ref(v___x_1292_);
lean_dec_ref(v___y_1252_);
lean_inc_ref(v_ver_1208_);
v___x_1300_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_ver_1208_);
lean_ctor_set(v___x_1300_, 1, v_ver_1208_);
return v___x_1300_;
}
}
}
}
v___jp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v_noOrigin_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1304_ = lean_string_utf8_byte_size(v_fst_1302_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v_noOrigin_1306_ = lean_nat_dec_eq(v___x_1304_, v___x_1305_);
v___x_1307_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__3));
v___x_1308_ = lean_string_utf8_byte_size(v_snd_1303_);
v___x_1309_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__4, &l_Lake_ToolchainVer_ofString___closed__4_once, _init_l_Lake_ToolchainVer_ofString___closed__4);
v___x_1310_ = lean_nat_dec_le(v___x_1309_, v___x_1308_);
if (v___x_1310_ == 0)
{
v___y_1250_ = v_noOrigin_1306_;
v___y_1251_ = v_snd_1303_;
v___y_1252_ = v_fst_1302_;
v___y_1253_ = v___x_1305_;
goto v___jp_1249_;
}
else
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_string_memcmp(v_snd_1303_, v___x_1307_, v___x_1305_, v___x_1305_, v___x_1309_);
if (v___x_1311_ == 0)
{
v___y_1250_ = v_noOrigin_1306_;
v___y_1251_ = v_snd_1303_;
v___y_1252_ = v_fst_1302_;
v___y_1253_ = v___x_1305_;
goto v___jp_1249_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1312_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_snd_1303_);
v___x_1313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1313_, 0, v_snd_1303_);
lean_ctor_set(v___x_1313_, 1, v___x_1305_);
lean_ctor_set(v___x_1313_, 2, v___x_1308_);
v___x_1314_ = l_String_Slice_Pos_nextn(v___x_1313_, v___x_1305_, v___x_1312_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = lean_string_utf8_extract(v_snd_1303_, v___x_1314_, v___x_1308_);
lean_dec(v___x_1314_);
lean_dec_ref(v_snd_1303_);
v___x_1316_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_1317_ = lean_string_utf8_byte_size(v___x_1315_);
v___x_1318_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v___x_1315_, v___x_1316_, v___x_1305_, v___x_1317_);
if (lean_obj_tag(v___x_1318_) == 1)
{
if (v_noOrigin_1306_ == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref(v___x_1318_);
v___x_1320_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1321_ = lean_string_dec_eq(v_fst_1302_, v___x_1320_);
lean_dec_ref(v_fst_1302_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_dec(v_a_1319_);
lean_inc_ref(v_ver_1208_);
v___x_1322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_ver_1208_);
lean_ctor_set(v___x_1322_, 1, v_ver_1208_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; 
lean_dec_ref(v_ver_1208_);
v___x_1323_ = l_Lake_ToolchainVer_release___override(v_a_1319_);
return v___x_1323_;
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1325_; 
lean_dec_ref(v_fst_1302_);
lean_dec_ref(v_ver_1208_);
v_a_1324_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1324_);
lean_dec_ref(v___x_1318_);
v___x_1325_ = l_Lake_ToolchainVer_release___override(v_a_1324_);
return v___x_1325_;
}
}
else
{
lean_object* v___x_1326_; 
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_fst_1302_);
lean_inc_ref(v_ver_1208_);
v___x_1326_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1326_, 0, v_ver_1208_);
lean_ctor_set(v___x_1326_, 1, v_ver_1208_);
return v___x_1326_;
}
}
}
}
v___jp_1327_:
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = lean_string_utf8_byte_size(v_ver_1208_);
v___x_1330_ = lean_nat_dec_eq(v___y_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v_pos_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_pos_1331_ = lean_string_utf8_next_fast(v_ver_1208_, v___y_1328_);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = lean_string_utf8_extract(v_ver_1208_, v___x_1332_, v___y_1328_);
lean_dec(v___y_1328_);
v___x_1334_ = lean_string_utf8_extract(v_ver_1208_, v_pos_1331_, v___x_1329_);
v_fst_1302_ = v___x_1333_;
v_snd_1303_ = v___x_1334_;
goto v___jp_1301_;
}
else
{
lean_object* v___x_1335_; 
lean_dec(v___y_1328_);
v___x_1335_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
lean_inc_ref(v_ver_1208_);
v_fst_1302_ = v___x_1335_;
v_snd_1303_ = v_ver_1208_;
goto v___jp_1301_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3(lean_object* v___x_1342_, lean_object* v_ver_1343_, lean_object* v_inst_1344_, lean_object* v_R_1345_, lean_object* v_a_1346_, lean_object* v_b_1347_, lean_object* v_c_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___x_1342_, v_ver_1343_, v_a_1346_, v_b_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object* v___x_1350_, lean_object* v_ver_1351_, lean_object* v_inst_1352_, lean_object* v_R_1353_, lean_object* v_a_1354_, lean_object* v_b_1355_, lean_object* v_c_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3(v___x_1350_, v_ver_1351_, v_inst_1352_, v_R_1353_, v_a_1354_, v_b_1355_, v_c_1356_);
lean_dec(v_b_1355_);
lean_dec_ref(v_ver_1351_);
lean_dec_ref(v___x_1350_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object* v_toolchainFile_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_IO_FS_readFile(v_toolchainFile_1358_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1378_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1378_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1378_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_str_1369_; lean_object* v_startInclusive_1370_; lean_object* v_endExclusive_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = lean_string_utf8_byte_size(v_a_1361_);
v___x_1367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1367_, 0, v_a_1361_);
lean_ctor_set(v___x_1367_, 1, v___x_1365_);
lean_ctor_set(v___x_1367_, 2, v___x_1366_);
v___x_1368_ = l_String_Slice_trimAscii(v___x_1367_);
v_str_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc_ref(v_str_1369_);
v_startInclusive_1370_ = lean_ctor_get(v___x_1368_, 1);
lean_inc(v_startInclusive_1370_);
v_endExclusive_1371_ = lean_ctor_get(v___x_1368_, 2);
lean_inc(v_endExclusive_1371_);
lean_dec_ref(v___x_1368_);
v___x_1372_ = lean_string_utf8_extract(v_str_1369_, v_startInclusive_1370_, v_endExclusive_1371_);
lean_dec(v_endExclusive_1371_);
lean_dec(v_startInclusive_1370_);
lean_dec_ref(v_str_1369_);
v___x_1373_ = l_Lake_ToolchainVer_ofString(v___x_1372_);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1374_);
v___x_1376_ = v___x_1363_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1390_; 
v_a_1379_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1381_ = v___x_1360_;
v_isShared_1382_ = v_isSharedCheck_1390_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1360_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1390_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
if (lean_obj_tag(v_a_1379_) == 11)
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
lean_dec_ref(v_a_1379_);
v___x_1383_ = lean_box(0);
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1383_);
v___x_1385_ = v___x_1381_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
else
{
lean_object* v___x_1388_; 
if (v_isShared_1382_ == 0)
{
v___x_1388_ = v___x_1381_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1379_);
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
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f___boxed(lean_object* v_toolchainFile_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lake_ToolchainVer_ofFile_x3f(v_toolchainFile_1391_);
lean_dec_ref(v_toolchainFile_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f(lean_object* v_dir_1394_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = ((lean_object*)(l_Lake_toolchainFileName___closed__0));
v___x_1397_ = l_System_FilePath_join(v_dir_1394_, v___x_1396_);
v___x_1398_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1397_);
lean_dec_ref(v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f___boxed(lean_object* v_dir_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lake_ToolchainVer_ofDir_x3f(v_dir_1399_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0(lean_object* v_x_1404_){
_start:
{
lean_object* v_toString_1405_; lean_object* v___x_1406_; 
v_toString_1405_ = lean_ctor_get(v_x_1404_, 0);
lean_inc_ref(v_toString_1405_);
v___x_1406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_toString_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0___boxed(lean_object* v_x_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lake_ToolchainVer_instToJson___lam__0(v_x_1407_);
lean_dec_ref(v_x_1407_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instFromJson___lam__0(lean_object* v_x_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Json_getStr_x3f(v_x_1411_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1429_; 
v_a_1421_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1423_ = v___x_1412_;
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1412_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = l_Lake_ToolchainVer_ofString(v_a_1421_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_blt(lean_object* v_a_1432_, lean_object* v_b_1433_){
_start:
{
switch(lean_obj_tag(v_a_1432_))
{
case 0:
{
if (lean_obj_tag(v_b_1433_) == 0)
{
lean_object* v_ver_1434_; lean_object* v_ver_1435_; uint8_t v___x_1436_; 
v_ver_1434_ = lean_ctor_get(v_a_1432_, 1);
v_ver_1435_ = lean_ctor_get(v_b_1433_, 1);
v___x_1436_ = l_Lake_StdVer_compare(v_ver_1434_, v_ver_1435_);
if (v___x_1436_ == 0)
{
uint8_t v___x_1437_; 
v___x_1437_ = 1;
return v___x_1437_;
}
else
{
uint8_t v___x_1438_; 
v___x_1438_ = 0;
return v___x_1438_;
}
}
else
{
uint8_t v___x_1439_; 
v___x_1439_ = 0;
return v___x_1439_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1433_) == 1)
{
lean_object* v_date_1440_; lean_object* v_rev_1441_; lean_object* v_date_1442_; lean_object* v_rev_1443_; lean_object* v___y_1445_; uint8_t v___x_1450_; 
v_date_1440_ = lean_ctor_get(v_a_1432_, 1);
v_rev_1441_ = lean_ctor_get(v_a_1432_, 2);
v_date_1442_ = lean_ctor_get(v_b_1433_, 1);
v_rev_1443_ = lean_ctor_get(v_b_1433_, 2);
v___x_1450_ = l_Lake_instOrdDate_ord(v_date_1440_, v_date_1442_);
if (v___x_1450_ == 0)
{
uint8_t v___x_1451_; 
v___x_1451_ = 1;
return v___x_1451_;
}
else
{
uint8_t v___x_1452_; 
v___x_1452_ = l_Lake_instDecidableEqDate_decEq(v_date_1440_, v_date_1442_);
if (v___x_1452_ == 0)
{
return v___x_1452_;
}
else
{
if (lean_obj_tag(v_rev_1441_) == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
v___y_1445_ = v___x_1453_;
goto v___jp_1444_;
}
else
{
lean_object* v_val_1454_; 
v_val_1454_ = lean_ctor_get(v_rev_1441_, 0);
v___y_1445_ = v_val_1454_;
goto v___jp_1444_;
}
}
}
v___jp_1444_:
{
if (lean_obj_tag(v_rev_1443_) == 0)
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = lean_nat_dec_lt(v___y_1445_, v___x_1446_);
return v___x_1447_;
}
else
{
lean_object* v_val_1448_; uint8_t v___x_1449_; 
v_val_1448_ = lean_ctor_get(v_rev_1443_, 0);
v___x_1449_ = lean_nat_dec_lt(v___y_1445_, v_val_1448_);
return v___x_1449_;
}
}
}
else
{
uint8_t v___x_1455_; 
v___x_1455_ = 0;
return v___x_1455_;
}
}
default: 
{
uint8_t v___x_1456_; 
v___x_1456_ = 0;
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_blt___boxed(lean_object* v_a_1457_, lean_object* v_b_1458_){
_start:
{
uint8_t v_res_1459_; lean_object* v_r_1460_; 
v_res_1459_ = l_Lake_ToolchainVer_blt(v_a_1457_, v_b_1458_);
lean_dec_ref(v_b_1458_);
lean_dec_ref(v_a_1457_);
v_r_1460_ = lean_box(v_res_1459_);
return v_r_1460_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLT(void){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_box(0);
return v___x_1461_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLt(lean_object* v_a_1462_, lean_object* v_b_1463_){
_start:
{
uint8_t v___x_1464_; 
v___x_1464_ = l_Lake_ToolchainVer_blt(v_a_1462_, v_b_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLt___boxed(lean_object* v_a_1465_, lean_object* v_b_1466_){
_start:
{
uint8_t v_res_1467_; lean_object* v_r_1468_; 
v_res_1467_ = l_Lake_ToolchainVer_decLt(v_a_1465_, v_b_1466_);
lean_dec_ref(v_b_1466_);
lean_dec_ref(v_a_1465_);
v_r_1468_ = lean_box(v_res_1467_);
return v_r_1468_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_ble(lean_object* v_a_1469_, lean_object* v_b_1470_){
_start:
{
switch(lean_obj_tag(v_a_1469_))
{
case 0:
{
if (lean_obj_tag(v_b_1470_) == 0)
{
lean_object* v_ver_1471_; lean_object* v_ver_1472_; uint8_t v___x_1473_; 
v_ver_1471_ = lean_ctor_get(v_a_1469_, 1);
v_ver_1472_ = lean_ctor_get(v_b_1470_, 1);
v___x_1473_ = l_Lake_StdVer_compare(v_ver_1471_, v_ver_1472_);
if (v___x_1473_ == 2)
{
uint8_t v___x_1474_; 
v___x_1474_ = 0;
return v___x_1474_;
}
else
{
uint8_t v___x_1475_; 
v___x_1475_ = 1;
return v___x_1475_;
}
}
else
{
uint8_t v___x_1476_; 
v___x_1476_ = 0;
return v___x_1476_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1470_) == 1)
{
lean_object* v_date_1477_; lean_object* v_rev_1478_; lean_object* v_date_1479_; lean_object* v_rev_1480_; lean_object* v___y_1482_; uint8_t v___x_1487_; 
v_date_1477_ = lean_ctor_get(v_a_1469_, 1);
v_rev_1478_ = lean_ctor_get(v_a_1469_, 2);
v_date_1479_ = lean_ctor_get(v_b_1470_, 1);
v_rev_1480_ = lean_ctor_get(v_b_1470_, 2);
v___x_1487_ = l_Lake_instOrdDate_ord(v_date_1477_, v_date_1479_);
if (v___x_1487_ == 0)
{
uint8_t v___x_1488_; 
v___x_1488_ = 1;
return v___x_1488_;
}
else
{
uint8_t v___x_1489_; 
v___x_1489_ = l_Lake_instDecidableEqDate_decEq(v_date_1477_, v_date_1479_);
if (v___x_1489_ == 0)
{
return v___x_1489_;
}
else
{
if (lean_obj_tag(v_rev_1478_) == 0)
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_unsigned_to_nat(0u);
v___y_1482_ = v___x_1490_;
goto v___jp_1481_;
}
else
{
lean_object* v_val_1491_; 
v_val_1491_ = lean_ctor_get(v_rev_1478_, 0);
v___y_1482_ = v_val_1491_;
goto v___jp_1481_;
}
}
}
v___jp_1481_:
{
if (lean_obj_tag(v_rev_1480_) == 0)
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_nat_dec_le(v___y_1482_, v___x_1483_);
return v___x_1484_;
}
else
{
lean_object* v_val_1485_; uint8_t v___x_1486_; 
v_val_1485_ = lean_ctor_get(v_rev_1480_, 0);
v___x_1486_ = lean_nat_dec_le(v___y_1482_, v_val_1485_);
return v___x_1486_;
}
}
}
else
{
uint8_t v___x_1492_; 
v___x_1492_ = 0;
return v___x_1492_;
}
}
case 2:
{
if (lean_obj_tag(v_b_1470_) == 2)
{
lean_object* v_n_1493_; lean_object* v_n_1494_; uint8_t v___x_1495_; 
v_n_1493_ = lean_ctor_get(v_a_1469_, 1);
v_n_1494_ = lean_ctor_get(v_b_1470_, 1);
v___x_1495_ = lean_nat_dec_eq(v_n_1493_, v_n_1494_);
return v___x_1495_;
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
if (lean_obj_tag(v_b_1470_) == 3)
{
lean_object* v_v_1497_; lean_object* v_v_1498_; uint8_t v___x_1499_; 
v_v_1497_ = lean_ctor_get(v_a_1469_, 1);
v_v_1498_ = lean_ctor_get(v_b_1470_, 1);
v___x_1499_ = lean_string_dec_eq(v_v_1497_, v_v_1498_);
return v___x_1499_;
}
else
{
uint8_t v___x_1500_; 
v___x_1500_ = 0;
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ble___boxed(lean_object* v_a_1501_, lean_object* v_b_1502_){
_start:
{
uint8_t v_res_1503_; lean_object* v_r_1504_; 
v_res_1503_ = l_Lake_ToolchainVer_ble(v_a_1501_, v_b_1502_);
lean_dec_ref(v_b_1502_);
lean_dec_ref(v_a_1501_);
v_r_1504_ = lean_box(v_res_1503_);
return v_r_1504_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLE(void){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_box(0);
return v___x_1505_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLe(lean_object* v_a_1506_, lean_object* v_b_1507_){
_start:
{
uint8_t v___x_1508_; 
v___x_1508_ = l_Lake_ToolchainVer_ble(v_a_1506_, v_b_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLe___boxed(lean_object* v_a_1509_, lean_object* v_b_1510_){
_start:
{
uint8_t v_res_1511_; lean_object* v_r_1512_; 
v_res_1511_ = l_Lake_ToolchainVer_decLe(v_a_1509_, v_b_1510_);
lean_dec_ref(v_b_1510_);
lean_dec_ref(v_a_1509_);
v_r_1512_ = lean_box(v_res_1511_);
return v_r_1512_;
}
}
LEAN_EXPORT lean_object* l_Lake_normalizeToolchain(lean_object* v_s_1513_){
_start:
{
lean_object* v___x_1514_; lean_object* v_toString_1515_; 
v___x_1514_ = l_Lake_ToolchainVer_ofString(v_s_1513_);
v_toString_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc_ref(v_toString_1515_);
lean_dec_ref(v___x_1514_);
return v_toString_1515_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeVersionToolchainVer___lam__0(lean_object* v_x_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = l_Lake_ToolchainVer_ofString(v_x_1520_);
v___x_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx(uint8_t v_x_1525_){
_start:
{
switch(v_x_1525_)
{
case 0:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_unsigned_to_nat(0u);
return v___x_1526_;
}
case 1:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_unsigned_to_nat(1u);
return v___x_1527_;
}
case 2:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_unsigned_to_nat(2u);
return v___x_1528_;
}
case 3:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_unsigned_to_nat(3u);
return v___x_1529_;
}
case 4:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_unsigned_to_nat(4u);
return v___x_1530_;
}
default: 
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_unsigned_to_nat(5u);
return v___x_1531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___boxed(lean_object* v_x_1532_){
_start:
{
uint8_t v_x_boxed_1533_; lean_object* v_res_1534_; 
v_x_boxed_1533_ = lean_unbox(v_x_1532_);
v_res_1534_ = l_Lake_ComparatorOp_ctorIdx(v_x_boxed_1533_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx(uint8_t v_x_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lake_ComparatorOp_ctorIdx(v_x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx___boxed(lean_object* v_x_1537_){
_start:
{
uint8_t v_x_4__boxed_1538_; lean_object* v_res_1539_; 
v_x_4__boxed_1538_ = lean_unbox(v_x_1537_);
v_res_1539_ = l_Lake_ComparatorOp_toCtorIdx(v_x_4__boxed_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg(lean_object* v_k_1540_){
_start:
{
lean_inc(v_k_1540_);
return v_k_1540_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg___boxed(lean_object* v_k_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lake_ComparatorOp_ctorElim___redArg(v_k_1541_);
lean_dec(v_k_1541_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim(lean_object* v_motive_1543_, lean_object* v_ctorIdx_1544_, uint8_t v_t_1545_, lean_object* v_h_1546_, lean_object* v_k_1547_){
_start:
{
lean_inc(v_k_1547_);
return v_k_1547_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___boxed(lean_object* v_motive_1548_, lean_object* v_ctorIdx_1549_, lean_object* v_t_1550_, lean_object* v_h_1551_, lean_object* v_k_1552_){
_start:
{
uint8_t v_t_boxed_1553_; lean_object* v_res_1554_; 
v_t_boxed_1553_ = lean_unbox(v_t_1550_);
v_res_1554_ = l_Lake_ComparatorOp_ctorElim(v_motive_1548_, v_ctorIdx_1549_, v_t_boxed_1553_, v_h_1551_, v_k_1552_);
lean_dec(v_k_1552_);
lean_dec(v_ctorIdx_1549_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg(lean_object* v_lt_1555_){
_start:
{
lean_inc(v_lt_1555_);
return v_lt_1555_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg___boxed(lean_object* v_lt_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lake_ComparatorOp_lt_elim___redArg(v_lt_1556_);
lean_dec(v_lt_1556_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim(lean_object* v_motive_1558_, uint8_t v_t_1559_, lean_object* v_h_1560_, lean_object* v_lt_1561_){
_start:
{
lean_inc(v_lt_1561_);
return v_lt_1561_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___boxed(lean_object* v_motive_1562_, lean_object* v_t_1563_, lean_object* v_h_1564_, lean_object* v_lt_1565_){
_start:
{
uint8_t v_t_boxed_1566_; lean_object* v_res_1567_; 
v_t_boxed_1566_ = lean_unbox(v_t_1563_);
v_res_1567_ = l_Lake_ComparatorOp_lt_elim(v_motive_1562_, v_t_boxed_1566_, v_h_1564_, v_lt_1565_);
lean_dec(v_lt_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg(lean_object* v_le_1568_){
_start:
{
lean_inc(v_le_1568_);
return v_le_1568_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg___boxed(lean_object* v_le_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lake_ComparatorOp_le_elim___redArg(v_le_1569_);
lean_dec(v_le_1569_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim(lean_object* v_motive_1571_, uint8_t v_t_1572_, lean_object* v_h_1573_, lean_object* v_le_1574_){
_start:
{
lean_inc(v_le_1574_);
return v_le_1574_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___boxed(lean_object* v_motive_1575_, lean_object* v_t_1576_, lean_object* v_h_1577_, lean_object* v_le_1578_){
_start:
{
uint8_t v_t_boxed_1579_; lean_object* v_res_1580_; 
v_t_boxed_1579_ = lean_unbox(v_t_1576_);
v_res_1580_ = l_Lake_ComparatorOp_le_elim(v_motive_1575_, v_t_boxed_1579_, v_h_1577_, v_le_1578_);
lean_dec(v_le_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg(lean_object* v_gt_1581_){
_start:
{
lean_inc(v_gt_1581_);
return v_gt_1581_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg___boxed(lean_object* v_gt_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lake_ComparatorOp_gt_elim___redArg(v_gt_1582_);
lean_dec(v_gt_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim(lean_object* v_motive_1584_, uint8_t v_t_1585_, lean_object* v_h_1586_, lean_object* v_gt_1587_){
_start:
{
lean_inc(v_gt_1587_);
return v_gt_1587_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___boxed(lean_object* v_motive_1588_, lean_object* v_t_1589_, lean_object* v_h_1590_, lean_object* v_gt_1591_){
_start:
{
uint8_t v_t_boxed_1592_; lean_object* v_res_1593_; 
v_t_boxed_1592_ = lean_unbox(v_t_1589_);
v_res_1593_ = l_Lake_ComparatorOp_gt_elim(v_motive_1588_, v_t_boxed_1592_, v_h_1590_, v_gt_1591_);
lean_dec(v_gt_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg(lean_object* v_ge_1594_){
_start:
{
lean_inc(v_ge_1594_);
return v_ge_1594_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg___boxed(lean_object* v_ge_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lake_ComparatorOp_ge_elim___redArg(v_ge_1595_);
lean_dec(v_ge_1595_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim(lean_object* v_motive_1597_, uint8_t v_t_1598_, lean_object* v_h_1599_, lean_object* v_ge_1600_){
_start:
{
lean_inc(v_ge_1600_);
return v_ge_1600_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___boxed(lean_object* v_motive_1601_, lean_object* v_t_1602_, lean_object* v_h_1603_, lean_object* v_ge_1604_){
_start:
{
uint8_t v_t_boxed_1605_; lean_object* v_res_1606_; 
v_t_boxed_1605_ = lean_unbox(v_t_1602_);
v_res_1606_ = l_Lake_ComparatorOp_ge_elim(v_motive_1601_, v_t_boxed_1605_, v_h_1603_, v_ge_1604_);
lean_dec(v_ge_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg(lean_object* v_eq_1607_){
_start:
{
lean_inc(v_eq_1607_);
return v_eq_1607_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg___boxed(lean_object* v_eq_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lake_ComparatorOp_eq_elim___redArg(v_eq_1608_);
lean_dec(v_eq_1608_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim(lean_object* v_motive_1610_, uint8_t v_t_1611_, lean_object* v_h_1612_, lean_object* v_eq_1613_){
_start:
{
lean_inc(v_eq_1613_);
return v_eq_1613_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___boxed(lean_object* v_motive_1614_, lean_object* v_t_1615_, lean_object* v_h_1616_, lean_object* v_eq_1617_){
_start:
{
uint8_t v_t_boxed_1618_; lean_object* v_res_1619_; 
v_t_boxed_1618_ = lean_unbox(v_t_1615_);
v_res_1619_ = l_Lake_ComparatorOp_eq_elim(v_motive_1614_, v_t_boxed_1618_, v_h_1616_, v_eq_1617_);
lean_dec(v_eq_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg(lean_object* v_ne_1620_){
_start:
{
lean_inc(v_ne_1620_);
return v_ne_1620_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg___boxed(lean_object* v_ne_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lake_ComparatorOp_ne_elim___redArg(v_ne_1621_);
lean_dec(v_ne_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim(lean_object* v_motive_1623_, uint8_t v_t_1624_, lean_object* v_h_1625_, lean_object* v_ne_1626_){
_start:
{
lean_inc(v_ne_1626_);
return v_ne_1626_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___boxed(lean_object* v_motive_1627_, lean_object* v_t_1628_, lean_object* v_h_1629_, lean_object* v_ne_1630_){
_start:
{
uint8_t v_t_boxed_1631_; lean_object* v_res_1632_; 
v_t_boxed_1631_ = lean_unbox(v_t_1628_);
v_res_1632_ = l_Lake_ComparatorOp_ne_elim(v_motive_1627_, v_t_boxed_1631_, v_h_1629_, v_ne_1630_);
lean_dec(v_ne_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr(uint8_t v_x_1651_, lean_object* v_prec_1652_){
_start:
{
lean_object* v___y_1654_; lean_object* v___y_1661_; lean_object* v___y_1668_; lean_object* v___y_1675_; lean_object* v___y_1682_; lean_object* v___y_1689_; 
switch(v_x_1651_)
{
case 0:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = lean_unsigned_to_nat(1024u);
v___x_1696_ = lean_nat_dec_le(v___x_1695_, v_prec_1652_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1654_ = v___x_1697_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1654_ = v___x_1698_;
goto v___jp_1653_;
}
}
case 1:
{
lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1699_ = lean_unsigned_to_nat(1024u);
v___x_1700_ = lean_nat_dec_le(v___x_1699_, v_prec_1652_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1661_ = v___x_1701_;
goto v___jp_1660_;
}
else
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1661_ = v___x_1702_;
goto v___jp_1660_;
}
}
case 2:
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = lean_unsigned_to_nat(1024u);
v___x_1704_ = lean_nat_dec_le(v___x_1703_, v_prec_1652_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1668_ = v___x_1705_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1668_ = v___x_1706_;
goto v___jp_1667_;
}
}
case 3:
{
lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = lean_unsigned_to_nat(1024u);
v___x_1708_ = lean_nat_dec_le(v___x_1707_, v_prec_1652_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1675_ = v___x_1709_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1675_ = v___x_1710_;
goto v___jp_1674_;
}
}
case 4:
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = lean_unsigned_to_nat(1024u);
v___x_1712_ = lean_nat_dec_le(v___x_1711_, v_prec_1652_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1682_ = v___x_1713_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1682_ = v___x_1714_;
goto v___jp_1681_;
}
}
default: 
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = lean_unsigned_to_nat(1024u);
v___x_1716_ = lean_nat_dec_le(v___x_1715_, v_prec_1652_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1689_ = v___x_1717_;
goto v___jp_1688_;
}
else
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1689_ = v___x_1718_;
goto v___jp_1688_;
}
}
}
v___jp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1655_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__1));
lean_inc(v___y_1654_);
v___x_1656_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___y_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = 0;
v___x_1658_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*1, v___x_1657_);
v___x_1659_ = l_Repr_addAppParen(v___x_1658_, v_prec_1652_);
return v___x_1659_;
}
v___jp_1660_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1662_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__3));
lean_inc(v___y_1661_);
v___x_1663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___y_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = 0;
v___x_1665_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*1, v___x_1664_);
v___x_1666_ = l_Repr_addAppParen(v___x_1665_, v_prec_1652_);
return v___x_1666_;
}
v___jp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1669_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__5));
lean_inc(v___y_1668_);
v___x_1670_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___y_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = 0;
v___x_1672_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*1, v___x_1671_);
v___x_1673_ = l_Repr_addAppParen(v___x_1672_, v_prec_1652_);
return v___x_1673_;
}
v___jp_1674_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1676_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__7));
lean_inc(v___y_1675_);
v___x_1677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = 0;
v___x_1679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*1, v___x_1678_);
v___x_1680_ = l_Repr_addAppParen(v___x_1679_, v_prec_1652_);
return v___x_1680_;
}
v___jp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1683_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__9));
lean_inc(v___y_1682_);
v___x_1684_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___y_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = 0;
v___x_1686_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set_uint8(v___x_1686_, sizeof(void*)*1, v___x_1685_);
v___x_1687_ = l_Repr_addAppParen(v___x_1686_, v_prec_1652_);
return v___x_1687_;
}
v___jp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1690_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__11));
lean_inc(v___y_1689_);
v___x_1691_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___y_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = 0;
v___x_1693_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*1, v___x_1692_);
v___x_1694_ = l_Repr_addAppParen(v___x_1693_, v_prec_1652_);
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr___boxed(lean_object* v_x_1719_, lean_object* v_prec_1720_){
_start:
{
uint8_t v_x_341__boxed_1721_; lean_object* v_res_1722_; 
v_x_341__boxed_1721_ = lean_unbox(v_x_1719_);
v_res_1722_ = l_Lake_instReprComparatorOp_repr(v_x_341__boxed_1721_, v_prec_1720_);
lean_dec(v_prec_1720_);
return v_res_1722_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp_default(void){
_start:
{
uint8_t v___x_1725_; 
v___x_1725_ = 0;
return v___x_1725_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp(void){
_start:
{
uint8_t v___x_1726_; 
v___x_1726_ = 0;
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(lean_object* v_sym_1727_, uint8_t v_cmp_1728_, lean_object* v_t_1729_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1730_ = lean_box(v_cmp_1728_);
lean_inc_ref(v_sym_1727_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_sym_1727_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = l_Lean_Data_Trie_insert___redArg(v_t_1729_, v_sym_1727_, v___x_1731_);
lean_dec_ref(v_sym_1727_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0___boxed(lean_object* v_sym_1733_, lean_object* v_cmp_1734_, lean_object* v_t_1735_){
_start:
{
uint8_t v_cmp_boxed_1736_; lean_object* v_res_1737_; 
v_cmp_boxed_1736_ = lean_unbox(v_cmp_1734_);
v_res_1737_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v_sym_1733_, v_cmp_boxed_1736_, v_t_1735_);
return v_res_1737_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9(void){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_1747_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10(void){
_start:
{
lean_object* v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1748_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9);
v___x_1749_ = 0;
v___x_1750_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
v___x_1751_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1750_, v___x_1749_, v___x_1748_);
return v___x_1751_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11(void){
_start:
{
lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1752_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10);
v___x_1753_ = 1;
v___x_1754_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7));
v___x_1755_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1754_, v___x_1753_, v___x_1752_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12(void){
_start:
{
lean_object* v___x_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1756_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11);
v___x_1757_ = 1;
v___x_1758_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
v___x_1759_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1758_, v___x_1757_, v___x_1756_);
return v___x_1759_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13(void){
_start:
{
lean_object* v___x_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12);
v___x_1761_ = 2;
v___x_1762_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
v___x_1763_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1762_, v___x_1761_, v___x_1760_);
return v___x_1763_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14(void){
_start:
{
lean_object* v___x_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1764_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13);
v___x_1765_ = 3;
v___x_1766_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4));
v___x_1767_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1766_, v___x_1765_, v___x_1764_);
return v___x_1767_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15(void){
_start:
{
lean_object* v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1768_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14);
v___x_1769_ = 3;
v___x_1770_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
v___x_1771_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1770_, v___x_1769_, v___x_1768_);
return v___x_1771_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16(void){
_start:
{
lean_object* v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1772_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15);
v___x_1773_ = 4;
v___x_1774_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
v___x_1775_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1774_, v___x_1773_, v___x_1772_);
return v___x_1775_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17(void){
_start:
{
lean_object* v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16);
v___x_1777_ = 5;
v___x_1778_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1));
v___x_1779_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1778_, v___x_1777_, v___x_1776_);
return v___x_1779_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18(void){
_start:
{
lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1780_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17);
v___x_1781_ = 5;
v___x_1782_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
v___x_1783_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1782_, v___x_1781_, v___x_1780_);
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie(void){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(lean_object* v_s_1787_, lean_object* v_p_1788_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie;
v___x_1790_ = lean_string_utf8_byte_size(v_s_1787_);
lean_inc(v_p_1788_);
v___x_1791_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_1787_, v___x_1789_, v_p_1788_, v___x_1790_);
if (lean_obj_tag(v___x_1791_) == 1)
{
lean_object* v_val_1792_; lean_object* v_fst_1793_; lean_object* v_snd_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1808_; 
v_val_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_val_1792_);
lean_dec_ref(v___x_1791_);
v_fst_1793_ = lean_ctor_get(v_val_1792_, 0);
v_snd_1794_ = lean_ctor_get(v_val_1792_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_val_1792_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1796_ = v_val_1792_;
v_isShared_1797_ = v_isSharedCheck_1808_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_snd_1794_);
lean_inc(v_fst_1793_);
lean_dec(v_val_1792_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1808_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v_p_x27_1799_; uint8_t v___x_1800_; 
v___x_1798_ = lean_string_utf8_byte_size(v_fst_1793_);
lean_dec(v_fst_1793_);
v_p_x27_1799_ = lean_nat_add(v_p_1788_, v___x_1798_);
v___x_1800_ = lean_string_is_valid_pos(v_s_1787_, v_p_x27_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_dec(v_p_x27_1799_);
lean_dec(v_snd_1794_);
v___x_1801_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0));
if (v_isShared_1797_ == 0)
{
lean_ctor_set_tag(v___x_1796_, 1);
lean_ctor_set(v___x_1796_, 1, v_p_1788_);
lean_ctor_set(v___x_1796_, 0, v___x_1801_);
v___x_1803_ = v___x_1796_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_p_1788_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
else
{
lean_object* v___x_1806_; 
lean_dec(v_p_1788_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 1, v_p_x27_1799_);
lean_ctor_set(v___x_1796_, 0, v_snd_1794_);
v___x_1806_ = v___x_1796_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_snd_1794_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_p_x27_1799_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v___x_1791_);
v___x_1809_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1));
v___x_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v_p_1788_);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___boxed(lean_object* v_s_1811_, lean_object* v_p_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1811_, v_p_1812_);
lean_dec_ref(v_s_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f(lean_object* v_s_1814_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1814_, v___x_1815_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v_a_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
v_a_1818_ = lean_ctor_get(v___x_1816_, 1);
lean_inc(v_a_1818_);
lean_dec_ref(v___x_1816_);
v___x_1819_ = lean_string_utf8_byte_size(v_s_1814_);
v___x_1820_ = lean_nat_dec_eq(v_a_1818_, v___x_1819_);
lean_dec(v_a_1818_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; 
lean_dec(v_a_1817_);
v___x_1821_ = lean_box(0);
return v___x_1821_;
}
else
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_a_1817_);
return v___x_1822_;
}
}
else
{
lean_object* v___x_1823_; 
lean_dec_ref(v___x_1816_);
v___x_1823_ = lean_box(0);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f___boxed(lean_object* v_s_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lake_ComparatorOp_ofString_x3f(v_s_1824_);
lean_dec_ref(v_s_1824_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString(uint8_t v_self_1826_){
_start:
{
switch(v_self_1826_)
{
case 0:
{
lean_object* v___x_1827_; 
v___x_1827_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
return v___x_1827_;
}
case 1:
{
lean_object* v___x_1828_; 
v___x_1828_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
return v___x_1828_;
}
case 2:
{
lean_object* v___x_1829_; 
v___x_1829_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
return v___x_1829_;
}
case 3:
{
lean_object* v___x_1830_; 
v___x_1830_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
return v___x_1830_;
}
case 4:
{
lean_object* v___x_1831_; 
v___x_1831_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
return v___x_1831_;
}
default: 
{
lean_object* v___x_1832_; 
v___x_1832_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
return v___x_1832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString___boxed(lean_object* v_self_1833_){
_start:
{
uint8_t v_self_boxed_1834_; lean_object* v_res_1835_; 
v_self_boxed_1834_ = lean_unbox(v_self_1833_);
v_res_1835_ = l_Lake_ComparatorOp_toString(v_self_boxed_1834_);
return v_res_1835_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_unsigned_to_nat(7u);
v___x_1848_ = lean_nat_to_int(v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_unsigned_to_nat(6u);
v___x_1853_ = lean_nat_to_int(v___x_1852_);
return v___x_1853_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_unsigned_to_nat(19u);
v___x_1858_ = lean_nat_to_int(v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___redArg(lean_object* v_x_1859_){
_start:
{
lean_object* v_ver_1860_; uint8_t v_op_1861_; uint8_t v_includeSuffixes_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_ver_1860_ = lean_ctor_get(v_x_1859_, 0);
lean_inc_ref(v_ver_1860_);
v_op_1861_ = lean_ctor_get_uint8(v_x_1859_, sizeof(void*)*1);
v_includeSuffixes_1862_ = lean_ctor_get_uint8(v_x_1859_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_1859_);
v___x_1863_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_1864_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__3));
v___x_1865_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__4, &l_Lake_instReprVerComparator_repr___redArg___closed__4_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__4);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = l_Lake_instReprStdVer_repr___redArg(v_ver_1860_);
v___x_1868_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1865_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = 0;
v___x_1870_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set_uint8(v___x_1870_, sizeof(void*)*1, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1864_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_1873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = lean_box(1);
v___x_1875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__6));
v___x_1877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v___x_1863_);
v___x_1879_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__7, &l_Lake_instReprVerComparator_repr___redArg___closed__7_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__7);
v___x_1880_ = l_Lake_instReprComparatorOp_repr(v_op_1861_, v___x_1866_);
v___x_1881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set_uint8(v___x_1882_, sizeof(void*)*1, v___x_1869_);
v___x_1883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1878_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v___x_1872_);
v___x_1885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v___x_1874_);
v___x_1886_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__9));
v___x_1887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1885_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v___x_1863_);
v___x_1889_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__10, &l_Lake_instReprVerComparator_repr___redArg___closed__10_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__10);
v___x_1890_ = l_Bool_repr___redArg(v_includeSuffixes_1862_);
v___x_1891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*1, v___x_1869_);
v___x_1893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1888_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_1895_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_1896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v___x_1893_);
v___x_1897_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_1898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1894_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set_uint8(v___x_1900_, sizeof(void*)*1, v___x_1869_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr(lean_object* v_x_1901_, lean_object* v_prec_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lake_instReprVerComparator_repr___redArg(v_x_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___boxed(lean_object* v_x_1904_, lean_object* v_prec_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lake_instReprVerComparator_repr(v_x_1904_, v_prec_1905_);
lean_dec(v_prec_1905_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(lean_object* v_s_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1915_, v_a_1916_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v_a_1919_; lean_object* v___x_1920_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
v_a_1919_ = lean_ctor_get(v___x_1917_, 1);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1917_);
lean_inc_ref(v_s_1915_);
v___x_1920_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_1915_, v_a_1919_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v_a_1924_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
v_a_1922_ = lean_ctor_get(v___x_1920_, 1);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1920_);
v___x_1923_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_1915_, v_a_1922_);
lean_dec_ref(v_s_1915_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
if (lean_obj_tag(v_a_1924_) == 1)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1946_; 
v_a_1925_ = lean_ctor_get(v___x_1923_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v___x_1923_, 0);
lean_dec(v_unused_1947_);
v___x_1927_ = v___x_1923_;
v_isShared_1928_ = v_isSharedCheck_1946_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1923_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1946_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_val_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_val_1929_ = lean_ctor_get(v_a_1924_, 0);
lean_inc(v_val_1929_);
lean_dec_ref(v_a_1924_);
v___x_1930_ = lean_string_utf8_byte_size(v_val_1929_);
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = lean_nat_dec_eq(v___x_1930_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1937_; 
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v_a_1921_);
lean_ctor_set(v___x_1933_, 1, v_val_1929_);
v___x_1934_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
v___x_1935_ = lean_unbox(v_a_1918_);
lean_dec(v_a_1918_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*1, v___x_1935_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*1 + 1, v___x_1932_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1934_);
v___x_1937_ = v___x_1927_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_a_1925_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___x_1944_; 
lean_dec(v_val_1929_);
v___x_1939_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1921_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
v___x_1942_ = lean_unbox(v_a_1918_);
lean_dec(v_a_1918_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*1, v___x_1942_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*1 + 1, v___x_1932_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1941_);
v___x_1944_ = v___x_1927_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_a_1925_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_a_1924_);
v_a_1948_ = lean_ctor_get(v___x_1923_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; 
v_unused_1961_ = lean_ctor_get(v___x_1923_, 0);
lean_dec(v_unused_1961_);
v___x_1950_ = v___x_1923_;
v_isShared_1951_ = v_isSharedCheck_1960_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1923_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1960_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1958_; 
v___x_1952_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_a_1921_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = 0;
v___x_1955_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
v___x_1956_ = lean_unbox(v_a_1918_);
lean_dec(v_a_1918_);
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*1, v___x_1956_);
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*1 + 1, v___x_1954_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1955_);
v___x_1958_ = v___x_1950_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_a_1948_);
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
lean_object* v_a_1962_; lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_a_1918_);
lean_dec_ref(v_s_1915_);
v_a_1962_ = lean_ctor_get(v___x_1920_, 0);
v_a_1963_ = lean_ctor_get(v___x_1920_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1920_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_inc(v_a_1962_);
lean_dec(v___x_1920_);
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
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1962_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_a_1963_);
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
lean_object* v_a_1971_; lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v_s_1915_);
v_a_1971_ = lean_ctor_get(v___x_1917_, 0);
v_a_1972_ = lean_ctor_get(v___x_1917_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1917_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_inc(v_a_1971_);
lean_dec(v___x_1917_);
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
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1971_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_a_1972_);
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
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_parse(lean_object* v_s_1981_){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1982_ = ((lean_object*)(l_Lake_VerComparator_parse___closed__0));
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = lean_string_utf8_byte_size(v_s_1981_);
v___x_1985_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_1981_, v___x_1982_, v___x_1983_, v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT uint8_t l_Lake_VerComparator_test(lean_object* v_self_1986_, lean_object* v_ver_1987_){
_start:
{
lean_object* v___y_1989_; uint8_t v___y_1990_; uint8_t v___y_1991_; uint8_t v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_1994_; uint8_t v___y_1995_; lean_object* v___y_2000_; uint8_t v___y_2001_; uint8_t v___y_2002_; uint8_t v___y_2003_; lean_object* v___y_2004_; uint8_t v___y_2005_; lean_object* v___y_2010_; uint8_t v___y_2011_; uint8_t v___y_2012_; lean_object* v___y_2013_; uint8_t v___y_2014_; lean_object* v___y_2019_; uint8_t v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v_ver_2026_; uint8_t v_op_2027_; uint8_t v_includeSuffixes_2028_; lean_object* v_ver_2030_; 
v_ver_2026_ = lean_ctor_get(v_self_1986_, 0);
v_op_2027_ = lean_ctor_get_uint8(v_self_1986_, sizeof(void*)*1);
v_includeSuffixes_2028_ = lean_ctor_get_uint8(v_self_1986_, sizeof(void*)*1 + 1);
if (v_includeSuffixes_2028_ == 0)
{
lean_object* v_toSemVerCore_2034_; lean_object* v_specialDescr_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v_toSemVerCore_2034_ = lean_ctor_get(v_ver_1987_, 0);
v_specialDescr_2035_ = lean_ctor_get(v_ver_1987_, 1);
v___x_2036_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_2037_ = lean_string_dec_eq(v_specialDescr_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v_toSemVerCore_2038_; lean_object* v_specialDescr_2039_; uint8_t v___x_2040_; 
v_toSemVerCore_2038_ = lean_ctor_get(v_ver_2026_, 0);
v_specialDescr_2039_ = lean_ctor_get(v_ver_2026_, 1);
v___x_2040_ = lean_string_dec_eq(v_specialDescr_2039_, v___x_2036_);
if (v___x_2040_ == 0)
{
uint8_t v___x_2041_; 
v___x_2041_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_2038_, v_toSemVerCore_2034_);
if (v___x_2041_ == 0)
{
return v_includeSuffixes_2028_;
}
else
{
switch(v_op_2027_)
{
case 0:
{
uint8_t v___x_2042_; 
v___x_2042_ = lean_string_dec_lt(v_specialDescr_2035_, v_specialDescr_2039_);
return v___x_2042_;
}
case 1:
{
uint8_t v___x_2043_; 
v___x_2043_ = l_String_decLE(v_specialDescr_2035_, v_specialDescr_2039_);
return v___x_2043_;
}
case 2:
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_string_dec_lt(v_specialDescr_2039_, v_specialDescr_2035_);
return v___x_2044_;
}
case 3:
{
uint8_t v___x_2045_; 
v___x_2045_ = l_String_decLE(v_specialDescr_2039_, v_specialDescr_2035_);
return v___x_2045_;
}
case 4:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_string_dec_eq(v_specialDescr_2035_, v_specialDescr_2039_);
return v___x_2046_;
}
default: 
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_string_dec_eq(v_specialDescr_2035_, v_specialDescr_2039_);
if (v___x_2047_ == 0)
{
return v___x_2041_;
}
else
{
return v___x_2040_;
}
}
}
}
}
else
{
return v_includeSuffixes_2028_;
}
}
else
{
v_ver_2030_ = v_ver_1987_;
goto v___jp_2029_;
}
}
else
{
v_ver_2030_ = v_ver_1987_;
goto v___jp_2029_;
}
v___jp_1988_:
{
uint8_t v___x_1996_; 
v___x_1996_ = l_Lake_instDecidableEqStdVer_decEq(v___y_1989_, v___y_1994_);
switch(v___y_1991_)
{
case 0:
{
return v___y_1990_;
}
case 1:
{
return v___y_1993_;
}
case 2:
{
return v___y_1992_;
}
case 3:
{
return v___y_1995_;
}
case 4:
{
return v___x_1996_;
}
default: 
{
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = 1;
return v___x_1997_;
}
else
{
uint8_t v___x_1998_; 
v___x_1998_ = 0;
return v___x_1998_;
}
}
}
}
v___jp_1999_:
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lake_StdVer_compare(v___y_2004_, v___y_2000_);
if (v___x_2006_ == 2)
{
uint8_t v___x_2007_; 
v___x_2007_ = 0;
v___y_1989_ = v___y_2000_;
v___y_1990_ = v___y_2002_;
v___y_1991_ = v___y_2001_;
v___y_1992_ = v___y_2005_;
v___y_1993_ = v___y_2003_;
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___x_2007_;
goto v___jp_1988_;
}
else
{
uint8_t v___x_2008_; 
v___x_2008_ = 1;
v___y_1989_ = v___y_2000_;
v___y_1990_ = v___y_2002_;
v___y_1991_ = v___y_2001_;
v___y_1992_ = v___y_2005_;
v___y_1993_ = v___y_2003_;
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___x_2008_;
goto v___jp_1988_;
}
}
v___jp_2009_:
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lake_StdVer_compare(v___y_2013_, v___y_2010_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; 
v___x_2016_ = 1;
v___y_2000_ = v___y_2010_;
v___y_2001_ = v___y_2012_;
v___y_2002_ = v___y_2011_;
v___y_2003_ = v___y_2014_;
v___y_2004_ = v___y_2013_;
v___y_2005_ = v___x_2016_;
goto v___jp_1999_;
}
else
{
uint8_t v___x_2017_; 
v___x_2017_ = 0;
v___y_2000_ = v___y_2010_;
v___y_2001_ = v___y_2012_;
v___y_2002_ = v___y_2011_;
v___y_2003_ = v___y_2014_;
v___y_2004_ = v___y_2013_;
v___y_2005_ = v___x_2017_;
goto v___jp_1999_;
}
}
v___jp_2018_:
{
uint8_t v___x_2023_; 
v___x_2023_ = l_Lake_StdVer_compare(v___y_2019_, v___y_2021_);
if (v___x_2023_ == 2)
{
uint8_t v___x_2024_; 
v___x_2024_ = 0;
v___y_2010_ = v___y_2019_;
v___y_2011_ = v___y_2022_;
v___y_2012_ = v___y_2020_;
v___y_2013_ = v___y_2021_;
v___y_2014_ = v___x_2024_;
goto v___jp_2009_;
}
else
{
uint8_t v___x_2025_; 
v___x_2025_ = 1;
v___y_2010_ = v___y_2019_;
v___y_2011_ = v___y_2022_;
v___y_2012_ = v___y_2020_;
v___y_2013_ = v___y_2021_;
v___y_2014_ = v___x_2025_;
goto v___jp_2009_;
}
}
v___jp_2029_:
{
uint8_t v___x_2031_; 
v___x_2031_ = l_Lake_StdVer_compare(v_ver_2030_, v_ver_2026_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; 
v___x_2032_ = 1;
v___y_2019_ = v_ver_2030_;
v___y_2020_ = v_op_2027_;
v___y_2021_ = v_ver_2026_;
v___y_2022_ = v___x_2032_;
goto v___jp_2018_;
}
else
{
uint8_t v___x_2033_; 
v___x_2033_ = 0;
v___y_2019_ = v_ver_2030_;
v___y_2020_ = v_op_2027_;
v___y_2021_ = v_ver_2026_;
v___y_2022_ = v___x_2033_;
goto v___jp_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_test___boxed(lean_object* v_self_2048_, lean_object* v_ver_2049_){
_start:
{
uint8_t v_res_2050_; lean_object* v_r_2051_; 
v_res_2050_ = l_Lake_VerComparator_test(v_self_2048_, v_ver_2049_);
lean_dec_ref(v_ver_2049_);
lean_dec_ref(v_self_2048_);
v_r_2051_ = lean_box(v_res_2050_);
return v_r_2051_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_toString(lean_object* v_self_2052_){
_start:
{
lean_object* v_ver_2053_; uint8_t v_op_2054_; uint8_t v_includeSuffixes_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_ver_2053_ = lean_ctor_get(v_self_2052_, 0);
lean_inc_ref(v_ver_2053_);
v_op_2054_ = lean_ctor_get_uint8(v_self_2052_, sizeof(void*)*1);
v_includeSuffixes_2055_ = lean_ctor_get_uint8(v_self_2052_, sizeof(void*)*1 + 1);
lean_dec_ref(v_self_2052_);
v___x_2056_ = l_Lake_ComparatorOp_toString(v_op_2054_);
v___x_2057_ = l_Lake_StdVer_toString(v_ver_2053_);
v___x_2058_ = lean_string_append(v___x_2056_, v___x_2057_);
lean_dec_ref(v___x_2057_);
if (v_includeSuffixes_2055_ == 0)
{
return v___x_2058_;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_2060_ = lean_string_append(v___x_2058_, v___x_2059_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
if (lean_obj_tag(v_x_2065_) == 0)
{
lean_dec(v_x_2063_);
return v_x_2064_;
}
else
{
lean_object* v_head_2066_; lean_object* v_tail_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2077_; 
v_head_2066_ = lean_ctor_get(v_x_2065_, 0);
v_tail_2067_ = lean_ctor_get(v_x_2065_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_x_2065_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2069_ = v_x_2065_;
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_tail_2067_);
lean_inc(v_head_2066_);
lean_dec(v_x_2065_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
lean_inc(v_x_2063_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 5);
lean_ctor_set(v___x_2069_, 1, v_x_2063_);
lean_ctor_set(v___x_2069_, 0, v_x_2064_);
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_x_2064_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_x_2063_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2066_);
v___x_2074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v_x_2064_ = v___x_2074_;
v_x_2065_ = v_tail_2067_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2078_, lean_object* v_x_2079_, lean_object* v_x_2080_){
_start:
{
if (lean_obj_tag(v_x_2080_) == 0)
{
lean_dec(v_x_2078_);
return v_x_2079_;
}
else
{
lean_object* v_head_2081_; lean_object* v_tail_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2092_; 
v_head_2081_ = lean_ctor_get(v_x_2080_, 0);
v_tail_2082_ = lean_ctor_get(v_x_2080_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_x_2080_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2084_ = v_x_2080_;
v_isShared_2085_ = v_isSharedCheck_2092_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_tail_2082_);
lean_inc(v_head_2081_);
lean_dec(v_x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2092_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
lean_inc(v_x_2078_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 5);
lean_ctor_set(v___x_2084_, 1, v_x_2078_);
lean_ctor_set(v___x_2084_, 0, v_x_2079_);
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_x_2079_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_x_2078_);
v___x_2087_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2081_);
v___x_2089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_2078_, v___x_2089_, v_tail_2082_);
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(lean_object* v_x_2093_, lean_object* v_x_2094_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_object* v___x_2095_; 
lean_dec(v_x_2094_);
v___x_2095_ = lean_box(0);
return v___x_2095_;
}
else
{
lean_object* v_tail_2096_; 
v_tail_2096_ = lean_ctor_get(v_x_2093_, 1);
if (lean_obj_tag(v_tail_2096_) == 0)
{
lean_object* v_head_2097_; lean_object* v___x_2098_; 
lean_dec(v_x_2094_);
v_head_2097_ = lean_ctor_get(v_x_2093_, 0);
lean_inc(v_head_2097_);
lean_dec_ref(v_x_2093_);
v___x_2098_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2097_);
return v___x_2098_;
}
else
{
lean_object* v_head_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_inc(v_tail_2096_);
v_head_2099_ = lean_ctor_get(v_x_2093_, 0);
lean_inc(v_head_2099_);
lean_dec_ref(v_x_2093_);
v___x_2100_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2099_);
v___x_2101_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(v_x_2094_, v___x_2100_, v_tail_2096_);
return v___x_2101_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0));
v___x_2108_ = lean_string_length(v___x_2107_);
return v___x_2108_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3);
v___x_2110_ = lean_nat_to_int(v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(lean_object* v_xs_2118_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2119_ = lean_array_get_size(v_xs_2118_);
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_nat_dec_eq(v___x_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2122_ = lean_array_to_list(v_xs_2118_);
v___x_2123_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2124_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(v___x_2122_, v___x_2123_);
v___x_2125_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2126_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2124_);
v___x_2128_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2125_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Std_Format_fill(v___x_2130_);
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; 
lean_dec_ref(v_xs_2118_);
v___x_2132_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(lean_object* v_x_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 0)
{
lean_dec(v_x_2133_);
return v_x_2134_;
}
else
{
lean_object* v_head_2136_; lean_object* v_tail_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2147_; 
v_head_2136_ = lean_ctor_get(v_x_2135_, 0);
v_tail_2137_ = lean_ctor_get(v_x_2135_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_x_2135_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2139_ = v_x_2135_;
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_tail_2137_);
lean_inc(v_head_2136_);
lean_dec(v_x_2135_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
lean_inc(v_x_2133_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set_tag(v___x_2139_, 5);
lean_ctor_set(v___x_2139_, 1, v_x_2133_);
lean_ctor_set(v___x_2139_, 0, v_x_2134_);
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_x_2134_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_x_2133_);
v___x_2142_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2136_);
v___x_2144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2142_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v_x_2134_ = v___x_2144_;
v_x_2135_ = v_tail_2137_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
if (lean_obj_tag(v_x_2148_) == 0)
{
lean_object* v___x_2150_; 
lean_dec(v_x_2149_);
v___x_2150_ = lean_box(0);
return v___x_2150_;
}
else
{
lean_object* v_tail_2151_; 
v_tail_2151_ = lean_ctor_get(v_x_2148_, 1);
if (lean_obj_tag(v_tail_2151_) == 0)
{
lean_object* v_head_2152_; lean_object* v___x_2153_; 
lean_dec(v_x_2149_);
v_head_2152_ = lean_ctor_get(v_x_2148_, 0);
lean_inc(v_head_2152_);
lean_dec_ref(v_x_2148_);
v___x_2153_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2152_);
return v___x_2153_;
}
else
{
lean_object* v_head_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_inc(v_tail_2151_);
v_head_2154_ = lean_ctor_get(v_x_2148_, 0);
lean_inc(v_head_2154_);
lean_dec_ref(v_x_2148_);
v___x_2155_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2154_);
v___x_2156_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(v_x_2149_, v___x_2155_, v_tail_2151_);
return v___x_2156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(lean_object* v_xs_2157_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2158_ = lean_array_get_size(v_xs_2157_);
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = lean_nat_dec_eq(v___x_2158_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2161_ = lean_array_to_list(v_xs_2157_);
v___x_2162_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2163_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(v___x_2161_, v___x_2162_);
v___x_2164_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2165_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___x_2163_);
v___x_2167_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2164_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = l_Std_Format_fill(v___x_2169_);
return v___x_2170_;
}
else
{
lean_object* v___x_2171_; 
lean_dec_ref(v_xs_2157_);
v___x_2171_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2171_;
}
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_unsigned_to_nat(12u);
v___x_2182_ = lean_nat_to_int(v___x_2181_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_unsigned_to_nat(11u);
v___x_2187_ = lean_nat_to_int(v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object* v_x_2188_){
_start:
{
lean_object* v_toString_2189_; lean_object* v_clauses_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2224_; 
v_toString_2189_ = lean_ctor_get(v_x_2188_, 0);
v_clauses_2190_ = lean_ctor_get(v_x_2188_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_x_2188_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2192_ = v_x_2188_;
v_isShared_2193_ = v_isSharedCheck_2224_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_clauses_2190_);
lean_inc(v_toString_2189_);
lean_dec(v_x_2188_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2224_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2194_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_2195_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__3));
v___x_2196_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__4, &l_Lake_instReprVerRange_repr___redArg___closed__4_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__4);
v___x_2197_ = l_String_quote(v_toString_2189_);
v___x_2198_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set_tag(v___x_2192_, 4);
lean_ctor_set(v___x_2192_, 1, v___x_2198_);
lean_ctor_set(v___x_2192_, 0, v___x_2196_);
v___x_2200_ = v___x_2192_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2201_ = 0;
v___x_2202_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*1, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2195_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_2205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_box(1);
v___x_2207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__6));
v___x_2209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2194_);
v___x_2211_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__7, &l_Lake_instReprVerRange_repr___redArg___closed__7_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__7);
v___x_2212_ = l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(v_clauses_2190_);
v___x_2213_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*1, v___x_2201_);
v___x_2215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2210_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_2217_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_2218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v___x_2215_);
v___x_2219_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_2220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2216_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*1, v___x_2201_);
return v___x_2222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr(lean_object* v_x_2225_, lean_object* v_prec_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lake_instReprVerRange_repr___redArg(v_x_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___boxed(lean_object* v_x_2228_, lean_object* v_prec_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lake_instReprVerRange_repr(v_x_2228_, v_prec_2229_);
lean_dec(v_prec_2229_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0(lean_object* v_self_2240_){
_start:
{
lean_object* v_toString_2241_; 
v_toString_2241_ = lean_ctor_get(v_self_2240_, 0);
lean_inc_ref(v_toString_2241_);
return v_toString_2241_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0___boxed(lean_object* v_self_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lake_VerRange_instToString___lam__0(v_self_2242_);
lean_dec_ref(v_self_2242_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(lean_object* v_as_2247_, size_t v_i_2248_, size_t v_stop_2249_, lean_object* v_b_2250_){
_start:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_usize_dec_eq(v_i_2248_, v_stop_2249_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; size_t v___x_2257_; size_t v___x_2258_; 
v___x_2252_ = lean_array_uget_borrowed(v_as_2247_, v_i_2248_);
v___x_2253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0));
v___x_2254_ = lean_string_append(v_b_2250_, v___x_2253_);
lean_inc(v___x_2252_);
v___x_2255_ = l_Lake_VerComparator_toString(v___x_2252_);
v___x_2256_ = lean_string_append(v___x_2254_, v___x_2255_);
lean_dec_ref(v___x_2255_);
v___x_2257_ = ((size_t)1ULL);
v___x_2258_ = lean_usize_add(v_i_2248_, v___x_2257_);
v_i_2248_ = v___x_2258_;
v_b_2250_ = v___x_2256_;
goto _start;
}
else
{
return v_b_2250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___boxed(lean_object* v_as_2260_, lean_object* v_i_2261_, lean_object* v_stop_2262_, lean_object* v_b_2263_){
_start:
{
size_t v_i_boxed_2264_; size_t v_stop_boxed_2265_; lean_object* v_res_2266_; 
v_i_boxed_2264_ = lean_unbox_usize(v_i_2261_);
lean_dec(v_i_2261_);
v_stop_boxed_2265_ = lean_unbox_usize(v_stop_2262_);
lean_dec(v_stop_2262_);
v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_as_2260_, v_i_boxed_2264_, v_stop_boxed_2265_, v_b_2263_);
lean_dec_ref(v_as_2260_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(lean_object* v_ands_2268_){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2269_ = lean_array_get_size(v_ands_2268_);
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = lean_nat_dec_eq(v___x_2269_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v___x_2272_ = lean_array_fget_borrowed(v_ands_2268_, v___x_2270_);
lean_inc(v___x_2272_);
v___x_2273_ = l_Lake_VerComparator_toString(v___x_2272_);
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = lean_nat_dec_lt(v___x_2274_, v___x_2269_);
if (v___x_2275_ == 0)
{
return v___x_2273_;
}
else
{
uint8_t v___x_2276_; 
v___x_2276_ = lean_nat_dec_le(v___x_2269_, v___x_2269_);
if (v___x_2276_ == 0)
{
if (v___x_2275_ == 0)
{
return v___x_2273_;
}
else
{
size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = ((size_t)1ULL);
v___x_2278_ = lean_usize_of_nat(v___x_2269_);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2268_, v___x_2277_, v___x_2278_, v___x_2273_);
return v___x_2279_;
}
}
else
{
size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = ((size_t)1ULL);
v___x_2281_ = lean_usize_of_nat(v___x_2269_);
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2268_, v___x_2280_, v___x_2281_, v___x_2273_);
return v___x_2282_;
}
}
}
else
{
lean_object* v___x_2283_; 
v___x_2283_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0));
return v___x_2283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___boxed(lean_object* v_ands_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v_ands_2284_);
lean_dec_ref(v_ands_2284_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(lean_object* v_as_2287_, size_t v_i_2288_, size_t v_stop_2289_, lean_object* v_b_2290_){
_start:
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_usize_dec_eq(v_i_2288_, v_stop_2289_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; size_t v___x_2297_; size_t v___x_2298_; 
v___x_2292_ = lean_array_uget_borrowed(v_as_2287_, v_i_2288_);
v___x_2293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0));
v___x_2294_ = lean_string_append(v_b_2290_, v___x_2293_);
v___x_2295_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2292_);
v___x_2296_ = lean_string_append(v___x_2294_, v___x_2295_);
lean_dec_ref(v___x_2295_);
v___x_2297_ = ((size_t)1ULL);
v___x_2298_ = lean_usize_add(v_i_2288_, v___x_2297_);
v_i_2288_ = v___x_2298_;
v_b_2290_ = v___x_2296_;
goto _start;
}
else
{
return v_b_2290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___boxed(lean_object* v_as_2300_, lean_object* v_i_2301_, lean_object* v_stop_2302_, lean_object* v_b_2303_){
_start:
{
size_t v_i_boxed_2304_; size_t v_stop_boxed_2305_; lean_object* v_res_2306_; 
v_i_boxed_2304_ = lean_unbox_usize(v_i_2301_);
lean_dec(v_i_2301_);
v_stop_boxed_2305_ = lean_unbox_usize(v_stop_2302_);
lean_dec(v_stop_2302_);
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_as_2300_, v_i_boxed_2304_, v_stop_boxed_2305_, v_b_2303_);
lean_dec_ref(v_as_2300_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(lean_object* v_ors_2307_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2308_ = lean_array_get_size(v_ors_2307_);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_nat_dec_eq(v___x_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2311_ = lean_array_fget_borrowed(v_ors_2307_, v___x_2309_);
v___x_2312_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2311_);
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_nat_dec_lt(v___x_2313_, v___x_2308_);
if (v___x_2314_ == 0)
{
return v___x_2312_;
}
else
{
uint8_t v___x_2315_; 
v___x_2315_ = lean_nat_dec_le(v___x_2308_, v___x_2308_);
if (v___x_2315_ == 0)
{
if (v___x_2314_ == 0)
{
return v___x_2312_;
}
else
{
size_t v___x_2316_; size_t v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = ((size_t)1ULL);
v___x_2317_ = lean_usize_of_nat(v___x_2308_);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2307_, v___x_2316_, v___x_2317_, v___x_2312_);
return v___x_2318_;
}
}
else
{
size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = ((size_t)1ULL);
v___x_2320_ = lean_usize_of_nat(v___x_2308_);
v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2307_, v___x_2319_, v___x_2320_, v___x_2312_);
return v___x_2321_;
}
}
}
else
{
lean_object* v___x_2322_; 
v___x_2322_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
return v___x_2322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs___boxed(lean_object* v_ors_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_ors_2323_);
lean_dec_ref(v_ors_2323_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_ofClauses(lean_object* v_clauses_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_clauses_2325_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v_clauses_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_appendRange(lean_object* v_ands_2328_, lean_object* v_minVer_2329_, lean_object* v_maxVer_2330_, lean_object* v_specialDescr_2331_){
_start:
{
lean_object* v_minVer_2332_; lean_object* v___x_2333_; lean_object* v_maxVer_2334_; uint8_t v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_minVer_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2332_, 0, v_minVer_2329_);
lean_ctor_set(v_minVer_2332_, 1, v_specialDescr_2331_);
v___x_2333_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2334_, 0, v_maxVer_2330_);
lean_ctor_set(v_maxVer_2334_, 1, v___x_2333_);
v___x_2335_ = 3;
v___x_2336_ = 0;
v___x_2337_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2337_, 0, v_minVer_2332_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1, v___x_2335_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1 + 1, v___x_2336_);
v___x_2338_ = lean_array_push(v_ands_2328_, v___x_2337_);
v___x_2339_ = 0;
v___x_2340_ = 1;
v___x_2341_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2341_, 0, v_maxVer_2334_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*1, v___x_2339_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*1 + 1, v___x_2340_);
v___x_2342_ = lean_array_push(v___x_2338_, v___x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(lean_object* v_s_2345_, lean_object* v_ands_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_a_2351_; lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2523_; 
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2347_);
lean_inc_ref(v_s_2345_);
v___x_2350_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2345_, v___x_2349_, v_a_2347_, v_a_2347_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_a_2352_ = lean_ctor_get(v___x_2350_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2354_ = v___x_2350_;
v_isShared_2355_ = v_isSharedCheck_2523_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2523_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; 
v___x_2356_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2345_, v_a_2352_);
lean_dec_ref(v_s_2345_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2513_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_a_2358_ = lean_ctor_get(v___x_2356_, 1);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2360_ = v___x_2356_;
v_isShared_2361_ = v_isSharedCheck_2513_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2513_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2362_ = lean_array_get_size(v_a_2351_);
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = lean_nat_dec_eq(v___x_2362_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = lean_unsigned_to_nat(2u);
v___x_2366_ = lean_nat_dec_eq(v___x_2362_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = lean_unsigned_to_nat(3u);
v___x_2368_ = lean_nat_dec_eq(v___x_2362_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec(v_a_2351_);
lean_dec_ref(v_ands_2346_);
v___x_2369_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0));
v___x_2370_ = l_Nat_reprFast(v___x_2362_);
v___x_2371_ = lean_string_append(v___x_2369_, v___x_2370_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2373_ = lean_string_append(v___x_2371_, v___x_2372_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2373_);
v___x_2375_ = v___x_2360_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_a_2358_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_array_fget_borrowed(v_a_2351_, v___x_2348_);
v___x_2378_ = l_String_Slice_toNat_x3f(v___x_2377_);
if (lean_obj_tag(v___x_2378_) == 1)
{
lean_object* v_val_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v_val_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_val_2379_);
lean_dec_ref(v___x_2378_);
v___x_2380_ = lean_array_fget_borrowed(v_a_2351_, v___x_2363_);
v___x_2381_ = l_String_Slice_toNat_x3f(v___x_2380_);
if (lean_obj_tag(v___x_2381_) == 1)
{
lean_object* v_val_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_val_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_val_2382_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = lean_array_fget(v_a_2351_, v___x_2365_);
lean_dec(v_a_2351_);
v___x_2384_ = l_String_Slice_toNat_x3f(v___x_2383_);
if (lean_obj_tag(v___x_2384_) == 1)
{
lean_object* v_val_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v_minVer_2390_; 
lean_dec(v___x_2383_);
v_val_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_val_2385_);
lean_dec_ref(v___x_2384_);
lean_inc(v_val_2382_);
lean_inc(v_val_2379_);
v___x_2386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2386_, 0, v_val_2379_);
lean_ctor_set(v___x_2386_, 1, v_val_2382_);
lean_ctor_set(v___x_2386_, 2, v_val_2385_);
v___x_2387_ = lean_nat_add(v_val_2382_, v___x_2363_);
lean_dec(v_val_2382_);
v___x_2388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2388_, 0, v_val_2379_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
lean_ctor_set(v___x_2388_, 2, v___x_2348_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 1, v_a_2357_);
lean_ctor_set(v___x_2354_, 0, v___x_2386_);
v_minVer_2390_ = v___x_2354_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_a_2357_);
v_minVer_2390_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v_maxVer_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2391_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2392_, 0, v___x_2388_);
lean_ctor_set(v_maxVer_2392_, 1, v___x_2391_);
v___x_2393_ = 3;
v___x_2394_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2394_, 0, v_minVer_2390_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*1, v___x_2393_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*1 + 1, v___x_2366_);
v___x_2395_ = lean_array_push(v_ands_2346_, v___x_2394_);
v___x_2396_ = 0;
v___x_2397_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2397_, 0, v_maxVer_2392_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1, v___x_2396_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1 + 1, v___x_2368_);
v___x_2398_ = lean_array_push(v___x_2395_, v___x_2397_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2398_);
v___x_2400_ = v___x_2360_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_a_2358_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
else
{
lean_object* v_str_2403_; lean_object* v_startInclusive_2404_; lean_object* v_endExclusive_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
lean_dec(v___x_2384_);
lean_dec(v_val_2382_);
lean_dec(v_val_2379_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_ands_2346_);
v_str_2403_ = lean_ctor_get(v___x_2383_, 0);
lean_inc_ref(v_str_2403_);
v_startInclusive_2404_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_startInclusive_2404_);
v_endExclusive_2405_ = lean_ctor_get(v___x_2383_, 2);
lean_inc(v_endExclusive_2405_);
lean_dec(v___x_2383_);
v___x_2406_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2407_ = lean_string_utf8_extract(v_str_2403_, v_startInclusive_2404_, v_endExclusive_2405_);
lean_dec(v_endExclusive_2405_);
lean_dec(v_startInclusive_2404_);
lean_dec_ref(v_str_2403_);
v___x_2408_ = lean_string_append(v___x_2406_, v___x_2407_);
lean_dec_ref(v___x_2407_);
v___x_2409_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2410_ = lean_string_append(v___x_2408_, v___x_2409_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2410_);
v___x_2412_ = v___x_2360_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_a_2358_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
else
{
lean_object* v_str_2414_; lean_object* v_startInclusive_2415_; lean_object* v_endExclusive_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
lean_inc(v___x_2380_);
lean_dec(v___x_2381_);
lean_dec(v_val_2379_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec(v_a_2351_);
lean_dec_ref(v_ands_2346_);
v_str_2414_ = lean_ctor_get(v___x_2380_, 0);
lean_inc_ref(v_str_2414_);
v_startInclusive_2415_ = lean_ctor_get(v___x_2380_, 1);
lean_inc(v_startInclusive_2415_);
v_endExclusive_2416_ = lean_ctor_get(v___x_2380_, 2);
lean_inc(v_endExclusive_2416_);
lean_dec(v___x_2380_);
v___x_2417_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2418_ = lean_string_utf8_extract(v_str_2414_, v_startInclusive_2415_, v_endExclusive_2416_);
lean_dec(v_endExclusive_2416_);
lean_dec(v_startInclusive_2415_);
lean_dec_ref(v_str_2414_);
v___x_2419_ = lean_string_append(v___x_2417_, v___x_2418_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2421_ = lean_string_append(v___x_2419_, v___x_2420_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2421_);
v___x_2423_ = v___x_2360_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_a_2358_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
lean_object* v_str_2425_; lean_object* v_startInclusive_2426_; lean_object* v_endExclusive_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
lean_inc(v___x_2377_);
lean_dec(v___x_2378_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec(v_a_2351_);
lean_dec_ref(v_ands_2346_);
v_str_2425_ = lean_ctor_get(v___x_2377_, 0);
lean_inc_ref(v_str_2425_);
v_startInclusive_2426_ = lean_ctor_get(v___x_2377_, 1);
lean_inc(v_startInclusive_2426_);
v_endExclusive_2427_ = lean_ctor_get(v___x_2377_, 2);
lean_inc(v_endExclusive_2427_);
lean_dec(v___x_2377_);
v___x_2428_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2429_ = lean_string_utf8_extract(v_str_2425_, v_startInclusive_2426_, v_endExclusive_2427_);
lean_dec(v_endExclusive_2427_);
lean_dec(v_startInclusive_2426_);
lean_dec_ref(v_str_2425_);
v___x_2430_ = lean_string_append(v___x_2428_, v___x_2429_);
lean_dec_ref(v___x_2429_);
v___x_2431_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2432_ = lean_string_append(v___x_2430_, v___x_2431_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2432_);
v___x_2434_ = v___x_2360_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_a_2358_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_array_fget_borrowed(v_a_2351_, v___x_2348_);
v___x_2437_ = l_String_Slice_toNat_x3f(v___x_2436_);
if (lean_obj_tag(v___x_2437_) == 1)
{
lean_object* v_val_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_val_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_val_2438_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = lean_array_fget(v_a_2351_, v___x_2363_);
lean_dec(v_a_2351_);
v___x_2440_ = l_String_Slice_toNat_x3f(v___x_2439_);
if (lean_obj_tag(v___x_2440_) == 1)
{
lean_object* v_val_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_minVer_2446_; 
lean_dec(v___x_2439_);
v_val_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc_n(v_val_2441_, 2);
lean_dec_ref(v___x_2440_);
lean_inc(v_val_2438_);
v___x_2442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2442_, 0, v_val_2438_);
lean_ctor_set(v___x_2442_, 1, v_val_2441_);
lean_ctor_set(v___x_2442_, 2, v___x_2348_);
v___x_2443_ = lean_nat_add(v_val_2441_, v___x_2363_);
lean_dec(v_val_2441_);
v___x_2444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2444_, 0, v_val_2438_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
lean_ctor_set(v___x_2444_, 2, v___x_2348_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 1, v_a_2357_);
lean_ctor_set(v___x_2354_, 0, v___x_2442_);
v_minVer_2446_ = v___x_2354_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_a_2357_);
v_minVer_2446_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v_maxVer_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2447_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2448_, 0, v___x_2444_);
lean_ctor_set(v_maxVer_2448_, 1, v___x_2447_);
v___x_2449_ = 3;
v___x_2450_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2450_, 0, v_minVer_2446_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*1, v___x_2449_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*1 + 1, v___x_2364_);
v___x_2451_ = lean_array_push(v_ands_2346_, v___x_2450_);
v___x_2452_ = 0;
v___x_2453_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2453_, 0, v_maxVer_2448_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*1, v___x_2452_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*1 + 1, v___x_2366_);
v___x_2454_ = lean_array_push(v___x_2451_, v___x_2453_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2454_);
v___x_2456_ = v___x_2360_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_a_2358_);
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
lean_object* v_str_2459_; lean_object* v_startInclusive_2460_; lean_object* v_endExclusive_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
lean_dec(v___x_2440_);
lean_dec(v_val_2438_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_ands_2346_);
v_str_2459_ = lean_ctor_get(v___x_2439_, 0);
lean_inc_ref(v_str_2459_);
v_startInclusive_2460_ = lean_ctor_get(v___x_2439_, 1);
lean_inc(v_startInclusive_2460_);
v_endExclusive_2461_ = lean_ctor_get(v___x_2439_, 2);
lean_inc(v_endExclusive_2461_);
lean_dec(v___x_2439_);
v___x_2462_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2463_ = lean_string_utf8_extract(v_str_2459_, v_startInclusive_2460_, v_endExclusive_2461_);
lean_dec(v_endExclusive_2461_);
lean_dec(v_startInclusive_2460_);
lean_dec_ref(v_str_2459_);
v___x_2464_ = lean_string_append(v___x_2462_, v___x_2463_);
lean_dec_ref(v___x_2463_);
v___x_2465_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2466_ = lean_string_append(v___x_2464_, v___x_2465_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2466_);
v___x_2468_ = v___x_2360_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_a_2358_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
else
{
lean_object* v_str_2470_; lean_object* v_startInclusive_2471_; lean_object* v_endExclusive_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
lean_inc(v___x_2436_);
lean_dec(v___x_2437_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec(v_a_2351_);
lean_dec_ref(v_ands_2346_);
v_str_2470_ = lean_ctor_get(v___x_2436_, 0);
lean_inc_ref(v_str_2470_);
v_startInclusive_2471_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_startInclusive_2471_);
v_endExclusive_2472_ = lean_ctor_get(v___x_2436_, 2);
lean_inc(v_endExclusive_2472_);
lean_dec(v___x_2436_);
v___x_2473_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2474_ = lean_string_utf8_extract(v_str_2470_, v_startInclusive_2471_, v_endExclusive_2472_);
lean_dec(v_endExclusive_2472_);
lean_dec(v_startInclusive_2471_);
lean_dec_ref(v_str_2470_);
v___x_2475_ = lean_string_append(v___x_2473_, v___x_2474_);
lean_dec_ref(v___x_2474_);
v___x_2476_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2477_ = lean_string_append(v___x_2475_, v___x_2476_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2477_);
v___x_2479_ = v___x_2360_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_a_2358_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_array_fget(v_a_2351_, v___x_2348_);
lean_dec(v_a_2351_);
v___x_2482_ = l_String_Slice_toNat_x3f(v___x_2481_);
if (lean_obj_tag(v___x_2482_) == 1)
{
lean_object* v_val_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v_minVer_2488_; 
lean_dec(v___x_2481_);
v_val_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc_n(v_val_2483_, 2);
lean_dec_ref(v___x_2482_);
v___x_2484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2484_, 0, v_val_2483_);
lean_ctor_set(v___x_2484_, 1, v___x_2348_);
lean_ctor_set(v___x_2484_, 2, v___x_2348_);
v___x_2485_ = lean_nat_add(v_val_2483_, v___x_2363_);
lean_dec(v_val_2483_);
v___x_2486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_2348_);
lean_ctor_set(v___x_2486_, 2, v___x_2348_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 1, v_a_2357_);
lean_ctor_set(v___x_2354_, 0, v___x_2484_);
v_minVer_2488_ = v___x_2354_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_a_2357_);
v_minVer_2488_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v_maxVer_2490_; uint8_t v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2489_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2490_, 0, v___x_2486_);
lean_ctor_set(v_maxVer_2490_, 1, v___x_2489_);
v___x_2491_ = 3;
v___x_2492_ = 0;
v___x_2493_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2493_, 0, v_minVer_2488_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*1, v___x_2491_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*1 + 1, v___x_2492_);
v___x_2494_ = lean_array_push(v_ands_2346_, v___x_2493_);
v___x_2495_ = 0;
v___x_2496_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2496_, 0, v_maxVer_2490_);
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*1, v___x_2495_);
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*1 + 1, v___x_2364_);
v___x_2497_ = lean_array_push(v___x_2494_, v___x_2496_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2497_);
v___x_2499_ = v___x_2360_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_a_2358_);
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
lean_object* v_str_2502_; lean_object* v_startInclusive_2503_; lean_object* v_endExclusive_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
lean_dec(v___x_2482_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_ands_2346_);
v_str_2502_ = lean_ctor_get(v___x_2481_, 0);
lean_inc_ref(v_str_2502_);
v_startInclusive_2503_ = lean_ctor_get(v___x_2481_, 1);
lean_inc(v_startInclusive_2503_);
v_endExclusive_2504_ = lean_ctor_get(v___x_2481_, 2);
lean_inc(v_endExclusive_2504_);
lean_dec(v___x_2481_);
v___x_2505_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2506_ = lean_string_utf8_extract(v_str_2502_, v_startInclusive_2503_, v_endExclusive_2504_);
lean_dec(v_endExclusive_2504_);
lean_dec(v_startInclusive_2503_);
lean_dec_ref(v_str_2502_);
v___x_2507_ = lean_string_append(v___x_2505_, v___x_2506_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2509_ = lean_string_append(v___x_2507_, v___x_2508_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2509_);
v___x_2511_ = v___x_2360_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_a_2358_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_del_object(v___x_2354_);
lean_dec(v_a_2351_);
lean_dec_ref(v_ands_2346_);
v_a_2514_ = lean_ctor_get(v___x_2356_, 0);
v_a_2515_ = lean_ctor_get(v___x_2356_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2356_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_inc(v_a_2514_);
lean_dec(v___x_2356_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2514_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(lean_object* v_s_2526_, lean_object* v_ands_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_a_2532_; lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2755_; 
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2528_);
lean_inc_ref(v_s_2526_);
v___x_2531_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2526_, v___x_2530_, v_a_2528_, v_a_2528_);
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_a_2533_ = lean_ctor_get(v___x_2531_, 1);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2535_ = v___x_2531_;
v_isShared_2536_ = v_isSharedCheck_2755_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2755_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; 
v___x_2537_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2526_, v_a_2533_);
lean_dec_ref(v_s_2526_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2745_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_a_2539_ = lean_ctor_get(v___x_2537_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2541_ = v___x_2537_;
v_isShared_2542_ = v_isSharedCheck_2745_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2745_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2543_ = lean_array_get_size(v_a_2532_);
v___x_2544_ = lean_unsigned_to_nat(1u);
v___x_2545_ = lean_nat_dec_eq(v___x_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2546_ = lean_unsigned_to_nat(2u);
v___x_2547_ = lean_nat_dec_eq(v___x_2543_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2548_ = lean_unsigned_to_nat(3u);
v___x_2549_ = lean_nat_dec_eq(v___x_2543_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
lean_dec(v_a_2538_);
lean_del_object(v___x_2535_);
lean_dec(v_a_2532_);
lean_dec_ref(v_ands_2527_);
v___x_2550_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0));
v___x_2551_ = l_Nat_reprFast(v___x_2543_);
v___x_2552_ = lean_string_append(v___x_2550_, v___x_2551_);
lean_dec_ref(v___x_2551_);
v___x_2553_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2554_ = lean_string_append(v___x_2552_, v___x_2553_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2554_);
v___x_2556_ = v___x_2541_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_a_2539_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_array_fget_borrowed(v_a_2532_, v___x_2529_);
v___x_2559_ = l_String_Slice_toNat_x3f(v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 1)
{
lean_object* v_val_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_val_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_val_2560_);
lean_dec_ref(v___x_2559_);
v___x_2561_ = lean_array_fget_borrowed(v_a_2532_, v___x_2544_);
v___x_2562_ = l_String_Slice_toNat_x3f(v___x_2561_);
if (lean_obj_tag(v___x_2562_) == 1)
{
lean_object* v_val_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_val_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_val_2563_);
lean_dec_ref(v___x_2562_);
v___x_2564_ = lean_array_fget(v_a_2532_, v___x_2546_);
lean_dec(v_a_2532_);
v___x_2565_ = l_String_Slice_toNat_x3f(v___x_2564_);
if (lean_obj_tag(v___x_2565_) == 1)
{
lean_object* v_val_2566_; uint8_t v___y_2568_; uint8_t v___x_2588_; 
lean_dec(v___x_2564_);
v_val_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_val_2566_);
lean_dec_ref(v___x_2565_);
v___x_2588_ = lean_nat_dec_eq(v_val_2560_, v___x_2529_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v_minVer_2592_; lean_object* v___x_2593_; lean_object* v_maxVer_2594_; uint8_t v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_del_object(v___x_2541_);
lean_inc(v_val_2560_);
v___x_2589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2589_, 0, v_val_2560_);
lean_ctor_set(v___x_2589_, 1, v_val_2563_);
lean_ctor_set(v___x_2589_, 2, v_val_2566_);
v___x_2590_ = lean_nat_add(v_val_2560_, v___x_2544_);
lean_dec(v_val_2560_);
v___x_2591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v___x_2529_);
lean_ctor_set(v___x_2591_, 2, v___x_2529_);
v_minVer_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2592_, 0, v___x_2589_);
lean_ctor_set(v_minVer_2592_, 1, v_a_2538_);
v___x_2593_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2594_, 0, v___x_2591_);
lean_ctor_set(v_maxVer_2594_, 1, v___x_2593_);
v___x_2595_ = 3;
v___x_2596_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2596_, 0, v_minVer_2592_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*1, v___x_2595_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*1 + 1, v___x_2588_);
v___x_2597_ = lean_array_push(v_ands_2527_, v___x_2596_);
v___x_2598_ = 0;
v___x_2599_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2599_, 0, v_maxVer_2594_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*1, v___x_2598_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*1 + 1, v___x_2549_);
v___x_2600_ = lean_array_push(v___x_2597_, v___x_2599_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 1, v_a_2539_);
lean_ctor_set(v___x_2535_, 0, v___x_2600_);
v___x_2602_ = v___x_2535_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_a_2539_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
else
{
uint8_t v___x_2604_; 
v___x_2604_ = lean_nat_dec_eq(v_val_2563_, v___x_2529_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v_minVer_2608_; lean_object* v___x_2609_; lean_object* v_maxVer_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_del_object(v___x_2541_);
lean_inc(v_val_2563_);
lean_inc(v_val_2560_);
v___x_2605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2605_, 0, v_val_2560_);
lean_ctor_set(v___x_2605_, 1, v_val_2563_);
lean_ctor_set(v___x_2605_, 2, v_val_2566_);
v___x_2606_ = lean_nat_add(v_val_2563_, v___x_2544_);
lean_dec(v_val_2563_);
v___x_2607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2607_, 0, v_val_2560_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
lean_ctor_set(v___x_2607_, 2, v___x_2529_);
v_minVer_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2608_, 0, v___x_2605_);
lean_ctor_set(v_minVer_2608_, 1, v_a_2538_);
v___x_2609_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2610_, 0, v___x_2607_);
lean_ctor_set(v_maxVer_2610_, 1, v___x_2609_);
v___x_2611_ = 3;
v___x_2612_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2612_, 0, v_minVer_2608_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*1, v___x_2611_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*1 + 1, v___x_2604_);
v___x_2613_ = lean_array_push(v_ands_2527_, v___x_2612_);
v___x_2614_ = 0;
v___x_2615_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2615_, 0, v_maxVer_2610_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*1, v___x_2614_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*1 + 1, v___x_2588_);
v___x_2616_ = lean_array_push(v___x_2613_, v___x_2615_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 1, v_a_2539_);
lean_ctor_set(v___x_2535_, 0, v___x_2616_);
v___x_2618_ = v___x_2535_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_a_2539_);
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
uint8_t v___x_2620_; 
lean_del_object(v___x_2535_);
v___x_2620_ = lean_nat_dec_eq(v_val_2566_, v___x_2529_);
if (v___x_2620_ == 0)
{
v___y_2568_ = v___x_2620_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = lean_string_utf8_byte_size(v_a_2538_);
v___x_2622_ = lean_nat_dec_eq(v___x_2621_, v___x_2529_);
v___y_2568_ = v___x_2622_;
goto v___jp_2567_;
}
}
}
v___jp_2567_:
{
if (v___y_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v_minVer_2572_; lean_object* v___x_2573_; lean_object* v_maxVer_2574_; uint8_t v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
lean_inc(v_val_2566_);
lean_inc(v_val_2563_);
lean_inc(v_val_2560_);
v___x_2569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2569_, 0, v_val_2560_);
lean_ctor_set(v___x_2569_, 1, v_val_2563_);
lean_ctor_set(v___x_2569_, 2, v_val_2566_);
v___x_2570_ = lean_nat_add(v_val_2566_, v___x_2544_);
lean_dec(v_val_2566_);
v___x_2571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2571_, 0, v_val_2560_);
lean_ctor_set(v___x_2571_, 1, v_val_2563_);
lean_ctor_set(v___x_2571_, 2, v___x_2570_);
v_minVer_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2572_, 0, v___x_2569_);
lean_ctor_set(v_minVer_2572_, 1, v_a_2538_);
v___x_2573_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2574_, 0, v___x_2571_);
lean_ctor_set(v_maxVer_2574_, 1, v___x_2573_);
v___x_2575_ = 3;
v___x_2576_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2576_, 0, v_minVer_2572_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*1, v___x_2575_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*1 + 1, v___y_2568_);
v___x_2577_ = lean_array_push(v_ands_2527_, v___x_2576_);
v___x_2578_ = 0;
v___x_2579_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2579_, 0, v_maxVer_2574_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*1, v___x_2578_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*1 + 1, v___x_2549_);
v___x_2580_ = lean_array_push(v___x_2577_, v___x_2579_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2580_);
v___x_2582_ = v___x_2541_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_a_2539_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
lean_dec(v_val_2566_);
lean_dec(v_val_2563_);
lean_dec(v_val_2560_);
lean_dec(v_a_2538_);
lean_dec_ref(v_ands_2527_);
v___x_2584_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1));
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2584_);
v___x_2586_ = v___x_2541_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_a_2539_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_str_2623_; lean_object* v_startInclusive_2624_; lean_object* v_endExclusive_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
lean_dec(v___x_2565_);
lean_dec(v_val_2563_);
lean_dec(v_val_2560_);
lean_dec(v_a_2538_);
lean_del_object(v___x_2535_);
lean_dec_ref(v_ands_2527_);
v_str_2623_ = lean_ctor_get(v___x_2564_, 0);
lean_inc_ref(v_str_2623_);
v_startInclusive_2624_ = lean_ctor_get(v___x_2564_, 1);
lean_inc(v_startInclusive_2624_);
v_endExclusive_2625_ = lean_ctor_get(v___x_2564_, 2);
lean_inc(v_endExclusive_2625_);
lean_dec(v___x_2564_);
v___x_2626_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2627_ = lean_string_utf8_extract(v_str_2623_, v_startInclusive_2624_, v_endExclusive_2625_);
lean_dec(v_endExclusive_2625_);
lean_dec(v_startInclusive_2624_);
lean_dec_ref(v_str_2623_);
v___x_2628_ = lean_string_append(v___x_2626_, v___x_2627_);
lean_dec_ref(v___x_2627_);
v___x_2629_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2630_ = lean_string_append(v___x_2628_, v___x_2629_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2630_);
v___x_2632_ = v___x_2541_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_a_2539_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
else
{
lean_object* v_str_2634_; lean_object* v_startInclusive_2635_; lean_object* v_endExclusive_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_inc(v___x_2561_);
lean_dec(v___x_2562_);
lean_dec(v_val_2560_);
lean_dec(v_a_2538_);
lean_del_object(v___x_2535_);
lean_dec(v_a_2532_);
lean_dec_ref(v_ands_2527_);
v_str_2634_ = lean_ctor_get(v___x_2561_, 0);
lean_inc_ref(v_str_2634_);
v_startInclusive_2635_ = lean_ctor_get(v___x_2561_, 1);
lean_inc(v_startInclusive_2635_);
v_endExclusive_2636_ = lean_ctor_get(v___x_2561_, 2);
lean_inc(v_endExclusive_2636_);
lean_dec(v___x_2561_);
v___x_2637_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2638_ = lean_string_utf8_extract(v_str_2634_, v_startInclusive_2635_, v_endExclusive_2636_);
lean_dec(v_endExclusive_2636_);
lean_dec(v_startInclusive_2635_);
lean_dec_ref(v_str_2634_);
v___x_2639_ = lean_string_append(v___x_2637_, v___x_2638_);
lean_dec_ref(v___x_2638_);
v___x_2640_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2641_ = lean_string_append(v___x_2639_, v___x_2640_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2641_);
v___x_2643_ = v___x_2541_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_a_2539_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
else
{
lean_object* v_str_2645_; lean_object* v_startInclusive_2646_; lean_object* v_endExclusive_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_inc(v___x_2558_);
lean_dec(v___x_2559_);
lean_dec(v_a_2538_);
lean_del_object(v___x_2535_);
lean_dec(v_a_2532_);
lean_dec_ref(v_ands_2527_);
v_str_2645_ = lean_ctor_get(v___x_2558_, 0);
lean_inc_ref(v_str_2645_);
v_startInclusive_2646_ = lean_ctor_get(v___x_2558_, 1);
lean_inc(v_startInclusive_2646_);
v_endExclusive_2647_ = lean_ctor_get(v___x_2558_, 2);
lean_inc(v_endExclusive_2647_);
lean_dec(v___x_2558_);
v___x_2648_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2649_ = lean_string_utf8_extract(v_str_2645_, v_startInclusive_2646_, v_endExclusive_2647_);
lean_dec(v_endExclusive_2647_);
lean_dec(v_startInclusive_2646_);
lean_dec_ref(v_str_2645_);
v___x_2650_ = lean_string_append(v___x_2648_, v___x_2649_);
lean_dec_ref(v___x_2649_);
v___x_2651_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2652_ = lean_string_append(v___x_2650_, v___x_2651_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2652_);
v___x_2654_ = v___x_2541_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_a_2539_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_del_object(v___x_2535_);
v___x_2656_ = lean_array_fget_borrowed(v_a_2532_, v___x_2529_);
v___x_2657_ = l_String_Slice_toNat_x3f(v___x_2656_);
if (lean_obj_tag(v___x_2657_) == 1)
{
lean_object* v_val_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v_val_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_val_2658_);
lean_dec_ref(v___x_2657_);
v___x_2659_ = lean_array_fget(v_a_2532_, v___x_2544_);
lean_dec(v_a_2532_);
v___x_2660_ = l_String_Slice_toNat_x3f(v___x_2659_);
if (lean_obj_tag(v___x_2660_) == 1)
{
lean_object* v_val_2661_; uint8_t v___x_2662_; 
lean_dec(v___x_2659_);
v_val_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_val_2661_);
lean_dec_ref(v___x_2660_);
v___x_2662_ = lean_nat_dec_eq(v_val_2658_, v___x_2529_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v_minVer_2666_; lean_object* v___x_2667_; lean_object* v_maxVer_2668_; uint8_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_inc(v_val_2658_);
v___x_2663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2663_, 0, v_val_2658_);
lean_ctor_set(v___x_2663_, 1, v_val_2661_);
lean_ctor_set(v___x_2663_, 2, v___x_2529_);
v___x_2664_ = lean_nat_add(v_val_2658_, v___x_2544_);
lean_dec(v_val_2658_);
v___x_2665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
lean_ctor_set(v___x_2665_, 1, v___x_2529_);
lean_ctor_set(v___x_2665_, 2, v___x_2529_);
v_minVer_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2666_, 0, v___x_2663_);
lean_ctor_set(v_minVer_2666_, 1, v_a_2538_);
v___x_2667_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2668_, 0, v___x_2665_);
lean_ctor_set(v_maxVer_2668_, 1, v___x_2667_);
v___x_2669_ = 3;
v___x_2670_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2670_, 0, v_minVer_2666_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*1, v___x_2669_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*1 + 1, v___x_2662_);
v___x_2671_ = lean_array_push(v_ands_2527_, v___x_2670_);
v___x_2672_ = 0;
v___x_2673_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2673_, 0, v_maxVer_2668_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*1, v___x_2672_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*1 + 1, v___x_2547_);
v___x_2674_ = lean_array_push(v___x_2671_, v___x_2673_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2674_);
v___x_2676_ = v___x_2541_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2539_);
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
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v_minVer_2681_; lean_object* v___x_2682_; lean_object* v_maxVer_2683_; uint8_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
lean_inc(v_val_2661_);
lean_inc(v_val_2658_);
v___x_2678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2678_, 0, v_val_2658_);
lean_ctor_set(v___x_2678_, 1, v_val_2661_);
lean_ctor_set(v___x_2678_, 2, v___x_2529_);
v___x_2679_ = lean_nat_add(v_val_2661_, v___x_2544_);
lean_dec(v_val_2661_);
v___x_2680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2680_, 0, v_val_2658_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
lean_ctor_set(v___x_2680_, 2, v___x_2529_);
v_minVer_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2681_, 0, v___x_2678_);
lean_ctor_set(v_minVer_2681_, 1, v_a_2538_);
v___x_2682_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2683_, 0, v___x_2680_);
lean_ctor_set(v_maxVer_2683_, 1, v___x_2682_);
v___x_2684_ = 3;
v___x_2685_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2685_, 0, v_minVer_2681_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*1, v___x_2684_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*1 + 1, v___x_2545_);
v___x_2686_ = lean_array_push(v_ands_2527_, v___x_2685_);
v___x_2687_ = 0;
v___x_2688_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2688_, 0, v_maxVer_2683_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*1, v___x_2687_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*1 + 1, v___x_2662_);
v___x_2689_ = lean_array_push(v___x_2686_, v___x_2688_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2689_);
v___x_2691_ = v___x_2541_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_a_2539_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_str_2693_; lean_object* v_startInclusive_2694_; lean_object* v_endExclusive_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_dec(v___x_2660_);
lean_dec(v_val_2658_);
lean_dec(v_a_2538_);
lean_dec_ref(v_ands_2527_);
v_str_2693_ = lean_ctor_get(v___x_2659_, 0);
lean_inc_ref(v_str_2693_);
v_startInclusive_2694_ = lean_ctor_get(v___x_2659_, 1);
lean_inc(v_startInclusive_2694_);
v_endExclusive_2695_ = lean_ctor_get(v___x_2659_, 2);
lean_inc(v_endExclusive_2695_);
lean_dec(v___x_2659_);
v___x_2696_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2697_ = lean_string_utf8_extract(v_str_2693_, v_startInclusive_2694_, v_endExclusive_2695_);
lean_dec(v_endExclusive_2695_);
lean_dec(v_startInclusive_2694_);
lean_dec_ref(v_str_2693_);
v___x_2698_ = lean_string_append(v___x_2696_, v___x_2697_);
lean_dec_ref(v___x_2697_);
v___x_2699_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2700_ = lean_string_append(v___x_2698_, v___x_2699_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2700_);
v___x_2702_ = v___x_2541_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_a_2539_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
else
{
lean_object* v_str_2704_; lean_object* v_startInclusive_2705_; lean_object* v_endExclusive_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; 
lean_inc(v___x_2656_);
lean_dec(v___x_2657_);
lean_dec(v_a_2538_);
lean_dec(v_a_2532_);
lean_dec_ref(v_ands_2527_);
v_str_2704_ = lean_ctor_get(v___x_2656_, 0);
lean_inc_ref(v_str_2704_);
v_startInclusive_2705_ = lean_ctor_get(v___x_2656_, 1);
lean_inc(v_startInclusive_2705_);
v_endExclusive_2706_ = lean_ctor_get(v___x_2656_, 2);
lean_inc(v_endExclusive_2706_);
lean_dec(v___x_2656_);
v___x_2707_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2708_ = lean_string_utf8_extract(v_str_2704_, v_startInclusive_2705_, v_endExclusive_2706_);
lean_dec(v_endExclusive_2706_);
lean_dec(v_startInclusive_2705_);
lean_dec_ref(v_str_2704_);
v___x_2709_ = lean_string_append(v___x_2707_, v___x_2708_);
lean_dec_ref(v___x_2708_);
v___x_2710_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2711_ = lean_string_append(v___x_2709_, v___x_2710_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2711_);
v___x_2713_ = v___x_2541_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2711_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_a_2539_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
else
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_del_object(v___x_2535_);
v___x_2715_ = lean_array_fget(v_a_2532_, v___x_2529_);
lean_dec(v_a_2532_);
v___x_2716_ = l_String_Slice_toNat_x3f(v___x_2715_);
if (lean_obj_tag(v___x_2716_) == 1)
{
lean_object* v_val_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v_minVer_2721_; lean_object* v___x_2722_; lean_object* v_maxVer_2723_; uint8_t v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
lean_dec(v___x_2715_);
v_val_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc_n(v_val_2717_, 2);
lean_dec_ref(v___x_2716_);
v___x_2718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2718_, 0, v_val_2717_);
lean_ctor_set(v___x_2718_, 1, v___x_2529_);
lean_ctor_set(v___x_2718_, 2, v___x_2529_);
v___x_2719_ = lean_nat_add(v_val_2717_, v___x_2544_);
lean_dec(v_val_2717_);
v___x_2720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v___x_2529_);
lean_ctor_set(v___x_2720_, 2, v___x_2529_);
v_minVer_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2721_, 0, v___x_2718_);
lean_ctor_set(v_minVer_2721_, 1, v_a_2538_);
v___x_2722_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2723_, 0, v___x_2720_);
lean_ctor_set(v_maxVer_2723_, 1, v___x_2722_);
v___x_2724_ = 3;
v___x_2725_ = 0;
v___x_2726_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2726_, 0, v_minVer_2721_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*1, v___x_2724_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*1 + 1, v___x_2725_);
v___x_2727_ = lean_array_push(v_ands_2527_, v___x_2726_);
v___x_2728_ = 0;
v___x_2729_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2729_, 0, v_maxVer_2723_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*1, v___x_2728_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*1 + 1, v___x_2545_);
v___x_2730_ = lean_array_push(v___x_2727_, v___x_2729_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2730_);
v___x_2732_ = v___x_2541_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_a_2539_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
else
{
lean_object* v_str_2734_; lean_object* v_startInclusive_2735_; lean_object* v_endExclusive_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_dec(v___x_2716_);
lean_dec(v_a_2538_);
lean_dec_ref(v_ands_2527_);
v_str_2734_ = lean_ctor_get(v___x_2715_, 0);
lean_inc_ref(v_str_2734_);
v_startInclusive_2735_ = lean_ctor_get(v___x_2715_, 1);
lean_inc(v_startInclusive_2735_);
v_endExclusive_2736_ = lean_ctor_get(v___x_2715_, 2);
lean_inc(v_endExclusive_2736_);
lean_dec(v___x_2715_);
v___x_2737_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2738_ = lean_string_utf8_extract(v_str_2734_, v_startInclusive_2735_, v_endExclusive_2736_);
lean_dec(v_endExclusive_2736_);
lean_dec(v_startInclusive_2735_);
lean_dec_ref(v_str_2734_);
v___x_2739_ = lean_string_append(v___x_2737_, v___x_2738_);
lean_dec_ref(v___x_2738_);
v___x_2740_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2741_ = lean_string_append(v___x_2739_, v___x_2740_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2741_);
v___x_2743_ = v___x_2541_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_a_2539_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_del_object(v___x_2535_);
lean_dec(v_a_2532_);
lean_dec_ref(v_ands_2527_);
v_a_2746_ = lean_ctor_get(v___x_2537_, 0);
v_a_2747_ = lean_ctor_get(v___x_2537_, 1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2537_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_inc(v_a_2746_);
lean_dec(v___x_2537_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2746_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(lean_object* v_s_2761_, lean_object* v_ands_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___y_2765_; lean_object* v___y_2769_; lean_object* v___y_2774_; lean_object* v___x_2777_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; uint8_t v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v_a_2867_; lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2952_; 
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2865_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2763_);
lean_inc_ref(v_s_2761_);
v___x_2866_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2761_, v___x_2865_, v_a_2763_, v_a_2763_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_a_2868_ = lean_ctor_get(v___x_2866_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2870_ = v___x_2866_;
v_isShared_2871_ = v_isSharedCheck_2952_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2952_;
goto v_resetjp_2869_;
}
v___jp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0));
v___x_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v___y_2765_);
return v___x_2767_;
}
v___jp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2770_ = ((lean_object*)(l_Lake_VerComparator_wild));
v___x_2771_ = lean_array_push(v_ands_2762_, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v___y_2769_);
return v___x_2772_;
}
v___jp_2773_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1));
v___x_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
lean_ctor_set(v___x_2776_, 1, v___y_2774_);
return v___x_2776_;
}
v___jp_2778_:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2779_, v___y_2785_, v___y_2781_);
lean_dec(v___y_2785_);
if (lean_obj_tag(v___x_2786_) == 0)
{
switch(lean_obj_tag(v___y_2784_))
{
case 2:
{
switch(lean_obj_tag(v___y_2783_))
{
case 2:
{
lean_object* v_a_2787_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
if (lean_obj_tag(v_a_2787_) == 1)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2810_; 
v_a_2788_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2810_ == 0)
{
lean_object* v_unused_2811_; 
v_unused_2811_ = lean_ctor_get(v___x_2786_, 0);
lean_dec(v_unused_2811_);
v___x_2790_ = v___x_2786_;
v_isShared_2791_ = v_isSharedCheck_2810_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2786_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2810_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v_n_2792_; lean_object* v_n_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v_minVer_2798_; lean_object* v_maxVer_2799_; uint8_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
v_n_2792_ = lean_ctor_get(v___y_2784_, 0);
lean_inc_n(v_n_2792_, 2);
lean_dec_ref(v___y_2784_);
v_n_2793_ = lean_ctor_get(v___y_2783_, 0);
lean_inc_n(v_n_2793_, 2);
lean_dec_ref(v___y_2783_);
v___x_2794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2794_, 0, v_n_2792_);
lean_ctor_set(v___x_2794_, 1, v_n_2793_);
lean_ctor_set(v___x_2794_, 2, v___x_2777_);
v___x_2795_ = lean_nat_add(v_n_2793_, v___y_2780_);
lean_dec(v_n_2793_);
v___x_2796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2796_, 0, v_n_2792_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
lean_ctor_set(v___x_2796_, 2, v___x_2777_);
v___x_2797_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2798_, 0, v___x_2794_);
lean_ctor_set(v_minVer_2798_, 1, v___x_2797_);
v_maxVer_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2799_, 0, v___x_2796_);
lean_ctor_set(v_maxVer_2799_, 1, v___x_2797_);
v___x_2800_ = 3;
v___x_2801_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2801_, 0, v_minVer_2798_);
lean_ctor_set_uint8(v___x_2801_, sizeof(void*)*1, v___x_2800_);
lean_ctor_set_uint8(v___x_2801_, sizeof(void*)*1 + 1, v___y_2782_);
v___x_2802_ = lean_array_push(v_ands_2762_, v___x_2801_);
v___x_2803_ = 0;
v___x_2804_ = 1;
v___x_2805_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2805_, 0, v_maxVer_2799_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1, v___x_2803_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1 + 1, v___x_2804_);
v___x_2806_ = lean_array_push(v___x_2802_, v___x_2805_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2806_);
v___x_2808_ = v___x_2790_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_a_2788_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
else
{
lean_object* v_a_2812_; 
lean_dec_ref(v___y_2783_);
lean_dec(v_a_2787_);
lean_dec_ref(v___y_2784_);
lean_dec_ref(v_ands_2762_);
v_a_2812_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2812_);
lean_dec_ref(v___x_2786_);
v___y_2765_ = v_a_2812_;
goto v___jp_2764_;
}
}
case 1:
{
lean_object* v_a_2813_; 
v_a_2813_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2813_);
if (lean_obj_tag(v_a_2813_) == 2)
{
lean_object* v_a_2814_; 
lean_dec_ref(v_a_2813_);
lean_dec_ref(v___y_2784_);
lean_dec_ref(v_ands_2762_);
v_a_2814_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2814_);
lean_dec_ref(v___x_2786_);
v___y_2774_ = v_a_2814_;
goto v___jp_2773_;
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v_a_2813_);
v_a_2815_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2786_, 0);
lean_dec(v_unused_2837_);
v___x_2817_ = v___x_2786_;
v_isShared_2818_ = v_isSharedCheck_2836_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2786_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2836_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_n_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v_minVer_2824_; lean_object* v_maxVer_2825_; uint8_t v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v_n_2819_ = lean_ctor_get(v___y_2784_, 0);
lean_inc_n(v_n_2819_, 2);
lean_dec_ref(v___y_2784_);
v___x_2820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2820_, 0, v_n_2819_);
lean_ctor_set(v___x_2820_, 1, v___x_2777_);
lean_ctor_set(v___x_2820_, 2, v___x_2777_);
v___x_2821_ = lean_nat_add(v_n_2819_, v___y_2780_);
lean_dec(v_n_2819_);
v___x_2822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
lean_ctor_set(v___x_2822_, 1, v___x_2777_);
lean_ctor_set(v___x_2822_, 2, v___x_2777_);
v___x_2823_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2824_, 0, v___x_2820_);
lean_ctor_set(v_minVer_2824_, 1, v___x_2823_);
v_maxVer_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2825_, 0, v___x_2822_);
lean_ctor_set(v_maxVer_2825_, 1, v___x_2823_);
v___x_2826_ = 3;
v___x_2827_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2827_, 0, v_minVer_2824_);
lean_ctor_set_uint8(v___x_2827_, sizeof(void*)*1, v___x_2826_);
lean_ctor_set_uint8(v___x_2827_, sizeof(void*)*1 + 1, v___y_2782_);
v___x_2828_ = lean_array_push(v_ands_2762_, v___x_2827_);
v___x_2829_ = 0;
v___x_2830_ = 1;
v___x_2831_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2831_, 0, v_maxVer_2825_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*1, v___x_2829_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*1 + 1, v___x_2830_);
v___x_2832_ = lean_array_push(v___x_2828_, v___x_2831_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2832_);
v___x_2834_ = v___x_2817_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_a_2815_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
default: 
{
lean_object* v_a_2838_; 
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v_ands_2762_);
v_a_2838_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2838_);
lean_dec_ref(v___x_2786_);
v___y_2765_ = v_a_2838_;
goto v___jp_2764_;
}
}
}
case 1:
{
lean_object* v_a_2839_; 
v_a_2839_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2839_);
if (lean_obj_tag(v_a_2839_) == 2)
{
lean_object* v_a_2840_; 
lean_dec_ref(v_a_2839_);
lean_dec(v___y_2783_);
lean_dec_ref(v_ands_2762_);
v_a_2840_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2840_);
lean_dec_ref(v___x_2786_);
v___y_2774_ = v_a_2840_;
goto v___jp_2773_;
}
else
{
lean_dec(v_a_2839_);
if (lean_obj_tag(v___y_2783_) == 2)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref(v___y_2783_);
lean_dec_ref(v_ands_2762_);
v_a_2841_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v___x_2786_, 0);
lean_dec(v_unused_2850_);
v___x_2843_ = v___x_2786_;
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2786_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2845_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2));
if (v_isShared_2844_ == 0)
{
lean_ctor_set_tag(v___x_2843_, 1);
lean_ctor_set(v___x_2843_, 0, v___x_2845_);
v___x_2847_ = v___x_2843_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_a_2841_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
else
{
lean_object* v_a_2851_; 
lean_dec(v___y_2783_);
v_a_2851_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2851_);
lean_dec_ref(v___x_2786_);
v___y_2769_ = v_a_2851_;
goto v___jp_2768_;
}
}
}
default: 
{
lean_dec(v___y_2784_);
if (lean_obj_tag(v___y_2783_) == 1)
{
lean_object* v_a_2852_; 
v_a_2852_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2852_);
if (lean_obj_tag(v_a_2852_) == 2)
{
lean_object* v_a_2853_; 
lean_dec_ref(v_a_2852_);
lean_dec_ref(v_ands_2762_);
v_a_2853_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2853_);
lean_dec_ref(v___x_2786_);
v___y_2774_ = v_a_2853_;
goto v___jp_2773_;
}
else
{
lean_object* v_a_2854_; 
lean_dec(v_a_2852_);
v_a_2854_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2854_);
lean_dec_ref(v___x_2786_);
v___y_2769_ = v_a_2854_;
goto v___jp_2768_;
}
}
else
{
lean_object* v_a_2855_; 
lean_dec(v___y_2783_);
v_a_2855_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2855_);
lean_dec_ref(v___x_2786_);
v___y_2769_ = v_a_2855_;
goto v___jp_2768_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v_ands_2762_);
v_a_2856_ = lean_ctor_get(v___x_2786_, 0);
v_a_2857_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2786_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_inc(v_a_2856_);
lean_dec(v___x_2786_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2856_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
v_resetjp_2869_:
{
lean_object* v___y_2873_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2909_; lean_object* v___y_2910_; uint8_t v___y_2911_; lean_object* v___y_2912_; uint8_t v___y_2932_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2942_ = lean_string_utf8_byte_size(v_s_2761_);
v___x_2943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2943_, 0, v_s_2761_);
lean_ctor_set(v___x_2943_, 1, v___x_2777_);
lean_ctor_set(v___x_2943_, 2, v___x_2942_);
v___x_2944_ = l_String_Slice_Pos_get_x3f(v___x_2943_, v_a_2868_);
lean_dec_ref(v___x_2943_);
if (lean_obj_tag(v___x_2944_) == 0)
{
uint8_t v___x_2945_; 
v___x_2945_ = 0;
v___y_2932_ = v___x_2945_;
goto v___jp_2931_;
}
else
{
lean_object* v_val_2946_; uint32_t v___x_2947_; uint32_t v___x_2948_; uint8_t v___x_2949_; 
v_val_2946_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_val_2946_);
lean_dec_ref(v___x_2944_);
v___x_2947_ = 45;
v___x_2948_ = lean_unbox_uint32(v_val_2946_);
lean_dec(v_val_2946_);
v___x_2949_ = lean_uint32_dec_eq(v___x_2948_, v___x_2947_);
if (v___x_2949_ == 0)
{
v___y_2932_ = v___x_2949_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
lean_del_object(v___x_2870_);
lean_dec(v_a_2867_);
lean_dec_ref(v_ands_2762_);
v___x_2950_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4));
v___x_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v_a_2868_);
return v___x_2951_;
}
}
v___jp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2874_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3));
v___x_2875_ = l_Nat_reprFast(v___y_2873_);
v___x_2876_ = lean_string_append(v___x_2874_, v___x_2875_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2878_ = lean_string_append(v___x_2876_, v___x_2877_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 1);
lean_ctor_set(v___x_2870_, 0, v___x_2878_);
v___x_2880_ = v___x_2870_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_a_2868_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
v___jp_2882_:
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2886_, v___y_2889_, v___y_2885_);
lean_dec(v___y_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
v_a_2892_ = lean_ctor_get(v___x_2890_, 1);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2890_);
v___x_2893_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__12));
v___x_2894_ = lean_unsigned_to_nat(2u);
v___x_2895_ = lean_nat_dec_lt(v___x_2894_, v___y_2883_);
lean_dec(v___y_2883_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
lean_dec(v_a_2867_);
v___x_2896_ = lean_box(0);
v___y_2779_ = v___x_2893_;
v___y_2780_ = v___y_2884_;
v___y_2781_ = v_a_2892_;
v___y_2782_ = v___y_2887_;
v___y_2783_ = v_a_2891_;
v___y_2784_ = v___y_2888_;
v___y_2785_ = v___x_2896_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_array_fget(v_a_2867_, v___x_2894_);
lean_dec(v_a_2867_);
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
v___y_2779_ = v___x_2893_;
v___y_2780_ = v___y_2884_;
v___y_2781_ = v_a_2892_;
v___y_2782_ = v___y_2887_;
v___y_2783_ = v_a_2891_;
v___y_2784_ = v___y_2888_;
v___y_2785_ = v___x_2898_;
goto v___jp_2778_;
}
}
else
{
lean_object* v_a_2899_; lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v___y_2888_);
lean_dec(v___y_2883_);
lean_dec(v_a_2867_);
lean_dec_ref(v_ands_2762_);
v_a_2899_ = lean_ctor_get(v___x_2890_, 0);
v_a_2900_ = lean_ctor_get(v___x_2890_, 1);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2890_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_inc(v_a_2899_);
lean_dec(v___x_2890_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2899_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
v___jp_2908_:
{
lean_object* v___x_2913_; 
v___x_2913_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2909_, v___y_2912_, v_a_2868_);
lean_dec(v___y_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
v_a_2915_ = lean_ctor_get(v___x_2913_, 1);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2913_);
v___x_2916_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__10));
v___x_2917_ = lean_unsigned_to_nat(1u);
v___x_2918_ = lean_nat_dec_lt(v___x_2917_, v___y_2910_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_box(0);
v___y_2883_ = v___y_2910_;
v___y_2884_ = v___x_2917_;
v___y_2885_ = v_a_2915_;
v___y_2886_ = v___x_2916_;
v___y_2887_ = v___y_2911_;
v___y_2888_ = v_a_2914_;
v___y_2889_ = v___x_2919_;
goto v___jp_2882_;
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = lean_array_fget_borrowed(v_a_2867_, v___x_2917_);
lean_inc(v___x_2920_);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
v___y_2883_ = v___y_2910_;
v___y_2884_ = v___x_2917_;
v___y_2885_ = v_a_2915_;
v___y_2886_ = v___x_2916_;
v___y_2887_ = v___y_2911_;
v___y_2888_ = v_a_2914_;
v___y_2889_ = v___x_2921_;
goto v___jp_2882_;
}
}
else
{
lean_object* v_a_2922_; lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v___y_2910_);
lean_dec(v_a_2867_);
lean_dec_ref(v_ands_2762_);
v_a_2922_ = lean_ctor_get(v___x_2913_, 0);
v_a_2923_ = lean_ctor_get(v___x_2913_, 1);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2913_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_inc(v_a_2922_);
lean_dec(v___x_2913_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2922_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
v___jp_2931_:
{
lean_object* v___x_2933_; uint8_t v___x_2934_; 
v___x_2933_ = lean_array_get_size(v_a_2867_);
v___x_2934_ = lean_nat_dec_eq(v___x_2933_, v___x_2777_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = lean_unsigned_to_nat(3u);
v___x_2936_ = lean_nat_dec_lt(v___x_2935_, v___x_2933_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; uint8_t v___x_2938_; 
lean_del_object(v___x_2870_);
v___x_2937_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__1));
v___x_2938_ = lean_nat_dec_lt(v___x_2777_, v___x_2933_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_box(0);
v___y_2909_ = v___x_2937_;
v___y_2910_ = v___x_2933_;
v___y_2911_ = v___y_2932_;
v___y_2912_ = v___x_2939_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_array_fget_borrowed(v_a_2867_, v___x_2777_);
lean_inc(v___x_2940_);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
v___y_2909_ = v___x_2937_;
v___y_2910_ = v___x_2933_;
v___y_2911_ = v___y_2932_;
v___y_2912_ = v___x_2941_;
goto v___jp_2908_;
}
}
else
{
lean_dec(v_a_2867_);
lean_dec_ref(v_ands_2762_);
v___y_2873_ = v___x_2933_;
goto v___jp_2872_;
}
}
else
{
lean_dec(v_a_2867_);
lean_dec_ref(v_ands_2762_);
v___y_2873_ = v___x_2933_;
goto v___jp_2872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(lean_object* v_s_2957_, uint8_t v_needsRange_2958_, lean_object* v_ors_2959_, lean_object* v_ands_2960_, lean_object* v_p_2961_){
_start:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_string_utf8_byte_size(v_s_2957_);
v___x_2969_ = lean_nat_dec_eq(v_p_2961_, v___x_2968_);
if (v___x_2969_ == 0)
{
uint32_t v_c_2984_; uint8_t v___y_2986_; uint8_t v___y_2987_; uint8_t v___y_3028_; uint8_t v___y_3029_; uint8_t v___y_3035_; uint8_t v___y_3076_; uint32_t v___x_3086_; uint8_t v___x_3087_; 
v_c_2984_ = lean_string_utf8_get_fast(v_s_2957_, v_p_2961_);
v___x_3086_ = 65;
v___x_3087_ = lean_uint32_dec_le(v___x_3086_, v_c_2984_);
if (v___x_3087_ == 0)
{
goto v___jp_3081_;
}
else
{
uint32_t v___x_3088_; uint8_t v___x_3089_; 
v___x_3088_ = 90;
v___x_3089_ = lean_uint32_dec_le(v_c_2984_, v___x_3088_);
if (v___x_3089_ == 0)
{
goto v___jp_3081_;
}
else
{
goto v___jp_2970_;
}
}
v___jp_2985_:
{
if (v___y_2987_ == 0)
{
uint32_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2988_ = 44;
v___x_2989_ = lean_uint32_dec_eq(v_c_2984_, v___x_2988_);
if (v___x_2989_ == 0)
{
uint32_t v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = 124;
v___x_2991_ = lean_uint32_dec_eq(v_c_2984_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
lean_inc_ref(v_s_2957_);
v___x_2992_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_2957_, v_p_2961_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
v_a_2994_ = lean_ctor_get(v___x_2992_, 1);
lean_inc(v_a_2994_);
lean_dec_ref(v___x_2992_);
v___x_2995_ = lean_array_push(v_ands_2960_, v_a_2993_);
v_needsRange_2958_ = v___x_2991_;
v_ands_2960_ = v___x_2995_;
v_p_2961_ = v_a_2994_;
goto _start;
}
else
{
lean_object* v_a_2997_; lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v_a_2997_ = lean_ctor_get(v___x_2992_, 0);
v_a_2998_ = lean_ctor_get(v___x_2992_, 1);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2992_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_inc(v_a_2997_);
lean_dec(v___x_2992_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2997_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_p_3006_; uint8_t v___x_3007_; 
v_p_3006_ = lean_string_utf8_next_fast(v_s_2957_, v_p_2961_);
lean_dec(v_p_2961_);
v___x_3007_ = lean_nat_dec_eq(v_p_3006_, v___x_2968_);
if (v___x_3007_ == 0)
{
uint32_t v___x_3008_; uint8_t v___x_3009_; 
v___x_3008_ = lean_string_utf8_get_fast(v_s_2957_, v_p_3006_);
v___x_3009_ = lean_uint32_dec_eq(v___x_3008_, v___x_2990_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v___x_3010_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v_p_3006_);
return v___x_3011_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = lean_array_get_size(v_ands_2960_);
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = lean_nat_dec_eq(v___x_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_array_push(v_ors_2959_, v_ands_2960_);
v___x_3016_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2));
v___x_3017_ = lean_string_utf8_next_fast(v_s_2957_, v_p_3006_);
v_needsRange_2958_ = v___y_2986_;
v_ors_2959_ = v___x_3015_;
v_ands_2960_ = v___x_3016_;
v_p_2961_ = v___x_3017_;
goto _start;
}
else
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v___x_3019_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v_p_3006_);
return v___x_3020_;
}
}
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v___x_3021_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v_p_3006_);
return v___x_3022_;
}
}
}
else
{
if (v_needsRange_2958_ == 0)
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_string_utf8_next_fast(v_s_2957_, v_p_2961_);
lean_dec(v_p_2961_);
v_needsRange_2958_ = v___y_2986_;
v_p_2961_ = v___x_3023_;
goto _start;
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v___x_3025_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v_p_2961_);
return v___x_3026_;
}
}
}
else
{
goto v___jp_2965_;
}
}
v___jp_3027_:
{
if (v___y_3029_ == 0)
{
uint32_t v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = 13;
v___x_3031_ = lean_uint32_dec_eq(v_c_2984_, v___x_3030_);
if (v___x_3031_ == 0)
{
uint32_t v___x_3032_; uint8_t v___x_3033_; 
v___x_3032_ = 10;
v___x_3033_ = lean_uint32_dec_eq(v_c_2984_, v___x_3032_);
v___y_2986_ = v___y_3028_;
v___y_2987_ = v___x_3033_;
goto v___jp_2985_;
}
else
{
v___y_2986_ = v___y_3028_;
v___y_2987_ = v___x_3031_;
goto v___jp_2985_;
}
}
else
{
goto v___jp_2965_;
}
}
v___jp_3034_:
{
if (v___y_3035_ == 0)
{
uint32_t v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = 42;
v___x_3037_ = lean_uint32_dec_eq(v_c_2984_, v___x_3036_);
if (v___x_3037_ == 0)
{
uint32_t v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = 94;
v___x_3039_ = lean_uint32_dec_eq(v_c_2984_, v___x_3038_);
if (v___x_3039_ == 0)
{
uint32_t v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = 126;
v___x_3041_ = lean_uint32_dec_eq(v_c_2984_, v___x_3040_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; uint32_t v___x_3043_; uint8_t v___x_3044_; 
v___x_3042_ = 1;
v___x_3043_ = 32;
v___x_3044_ = lean_uint32_dec_eq(v_c_2984_, v___x_3043_);
if (v___x_3044_ == 0)
{
uint32_t v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = 9;
v___x_3046_ = lean_uint32_dec_eq(v_c_2984_, v___x_3045_);
v___y_3028_ = v___x_3042_;
v___y_3029_ = v___x_3046_;
goto v___jp_3027_;
}
else
{
v___y_3028_ = v___x_3042_;
v___y_3029_ = v___x_3044_;
goto v___jp_3027_;
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_string_utf8_next_fast(v_s_2957_, v_p_2961_);
lean_dec(v_p_2961_);
lean_inc_ref(v_s_2957_);
v___x_3048_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(v_s_2957_, v_ands_2960_, v___x_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v_a_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
v_a_3050_ = lean_ctor_get(v___x_3048_, 1);
lean_inc(v_a_3050_);
lean_dec_ref(v___x_3048_);
v_needsRange_2958_ = v___x_3039_;
v_ands_2960_ = v_a_3049_;
v_p_2961_ = v_a_3050_;
goto _start;
}
else
{
lean_object* v_a_3052_; lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v_a_3052_ = lean_ctor_get(v___x_3048_, 0);
v_a_3053_ = lean_ctor_get(v___x_3048_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3048_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_inc(v_a_3052_);
lean_dec(v___x_3048_);
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
}
else
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_string_utf8_next_fast(v_s_2957_, v_p_2961_);
lean_dec(v_p_2961_);
lean_inc_ref(v_s_2957_);
v___x_3062_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(v_s_2957_, v_ands_2960_, v___x_3061_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v_a_3064_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
v_a_3064_ = lean_ctor_get(v___x_3062_, 1);
lean_inc(v_a_3064_);
lean_dec_ref(v___x_3062_);
v_needsRange_2958_ = v___x_3037_;
v_ands_2960_ = v_a_3063_;
v_p_2961_ = v_a_3064_;
goto _start;
}
else
{
lean_object* v_a_3066_; lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v_a_3066_ = lean_ctor_get(v___x_3062_, 0);
v_a_3067_ = lean_ctor_get(v___x_3062_, 1);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3062_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_inc(v_a_3066_);
lean_dec(v___x_3062_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3066_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
else
{
goto v___jp_2970_;
}
}
else
{
goto v___jp_2970_;
}
}
v___jp_3075_:
{
if (v___y_3076_ == 0)
{
uint32_t v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = 48;
v___x_3078_ = lean_uint32_dec_le(v___x_3077_, v_c_2984_);
if (v___x_3078_ == 0)
{
v___y_3035_ = v___x_3078_;
goto v___jp_3034_;
}
else
{
uint32_t v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = 57;
v___x_3080_ = lean_uint32_dec_le(v_c_2984_, v___x_3079_);
v___y_3035_ = v___x_3080_;
goto v___jp_3034_;
}
}
else
{
goto v___jp_2970_;
}
}
v___jp_3081_:
{
uint32_t v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = 97;
v___x_3083_ = lean_uint32_dec_le(v___x_3082_, v_c_2984_);
if (v___x_3083_ == 0)
{
v___y_3076_ = v___x_3083_;
goto v___jp_3075_;
}
else
{
uint32_t v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = 122;
v___x_3085_ = lean_uint32_dec_le(v_c_2984_, v___x_3084_);
v___y_3076_ = v___x_3085_;
goto v___jp_3075_;
}
}
}
else
{
lean_dec_ref(v_s_2957_);
if (v_needsRange_2958_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3090_ = lean_array_get_size(v_ands_2960_);
v___x_3091_ = lean_unsigned_to_nat(0u);
v___x_3092_ = lean_nat_dec_eq(v___x_3090_, v___x_3091_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = lean_array_push(v_ors_2959_, v_ands_2960_);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v_p_2961_);
return v___x_3094_;
}
else
{
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
goto v___jp_2962_;
}
}
else
{
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
goto v___jp_2962_;
}
}
v___jp_2962_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_2964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v_p_2961_);
return v___x_2964_;
}
v___jp_2965_:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_string_utf8_next_fast(v_s_2957_, v_p_2961_);
lean_dec(v_p_2961_);
v_p_2961_ = v___x_2966_;
goto _start;
}
v___jp_2970_:
{
lean_object* v___x_2971_; 
lean_inc_ref(v_s_2957_);
v___x_2971_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(v_s_2957_, v_ands_2960_, v_p_2961_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v_a_2973_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
v_a_2973_ = lean_ctor_get(v___x_2971_, 1);
lean_inc(v_a_2973_);
lean_dec_ref(v___x_2971_);
v_needsRange_2958_ = v___x_2969_;
v_ands_2960_ = v_a_2972_;
v_p_2961_ = v_a_2973_;
goto _start;
}
else
{
lean_object* v_a_2975_; lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v_a_2975_ = lean_ctor_get(v___x_2971_, 0);
v_a_2976_ = lean_ctor_get(v___x_2971_, 1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2971_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_inc(v_a_2975_);
lean_dec(v___x_2971_);
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(lean_object* v_s_3095_, lean_object* v_needsRange_3096_, lean_object* v_ors_3097_, lean_object* v_ands_3098_, lean_object* v_p_3099_){
_start:
{
uint8_t v_needsRange_boxed_3100_; lean_object* v_res_3101_; 
v_needsRange_boxed_3100_ = lean_unbox(v_needsRange_3096_);
v_res_3101_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3095_, v_needsRange_boxed_3100_, v_ors_3097_, v_ands_3098_, v_p_3099_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object* v_s_3104_, lean_object* v_a_3105_){
_start:
{
uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = 1;
v___x_3107_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3104_);
v___x_3108_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3104_, v___x_3106_, v___x_3107_, v___x_3107_, v_a_3105_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3118_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_a_3110_ = lean_ctor_get(v___x_3108_, 1);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3112_ = v___x_3108_;
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v_s_3104_);
lean_ctor_set(v___x_3114_, 1, v_a_3109_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3114_);
v___x_3116_ = v___x_3112_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_a_3110_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v_s_3104_);
v_a_3119_ = lean_ctor_get(v___x_3108_, 0);
v_a_3120_ = lean_ctor_get(v___x_3108_, 1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3108_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_inc(v_a_3119_);
lean_dec(v___x_3108_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3119_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_parse(lean_object* v_s_3129_){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3130_ = ((lean_object*)(l_Lake_VerRange_parse___closed__0));
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = lean_string_utf8_byte_size(v_s_3129_);
v___x_3133_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_3129_, v___x_3130_, v___x_3131_, v___x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(lean_object* v_ver_3134_, lean_object* v_as_3135_, size_t v_i_3136_, size_t v_stop_3137_){
_start:
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_usize_dec_eq(v_i_3136_, v_stop_3137_);
if (v___x_3138_ == 0)
{
uint8_t v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3139_ = 1;
v___x_3140_ = lean_array_uget_borrowed(v_as_3135_, v_i_3136_);
v___x_3141_ = l_Lake_VerComparator_test(v___x_3140_, v_ver_3134_);
if (v___x_3141_ == 0)
{
return v___x_3139_;
}
else
{
if (v___x_3138_ == 0)
{
size_t v___x_3142_; size_t v___x_3143_; 
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_add(v_i_3136_, v___x_3142_);
v_i_3136_ = v___x_3143_;
goto _start;
}
else
{
return v___x_3139_;
}
}
}
else
{
uint8_t v___x_3145_; 
v___x_3145_ = 0;
return v___x_3145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0___boxed(lean_object* v_ver_3146_, lean_object* v_as_3147_, lean_object* v_i_3148_, lean_object* v_stop_3149_){
_start:
{
size_t v_i_boxed_3150_; size_t v_stop_boxed_3151_; uint8_t v_res_3152_; lean_object* v_r_3153_; 
v_i_boxed_3150_ = lean_unbox_usize(v_i_3148_);
lean_dec(v_i_3148_);
v_stop_boxed_3151_ = lean_unbox_usize(v_stop_3149_);
lean_dec(v_stop_3149_);
v_res_3152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3146_, v_as_3147_, v_i_boxed_3150_, v_stop_boxed_3151_);
lean_dec_ref(v_as_3147_);
lean_dec_ref(v_ver_3146_);
v_r_3153_ = lean_box(v_res_3152_);
return v_r_3153_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(lean_object* v_ver_3154_, lean_object* v_as_3155_, size_t v_i_3156_, size_t v_stop_3157_){
_start:
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_usize_dec_eq(v_i_3156_, v_stop_3157_);
if (v___x_3158_ == 0)
{
uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3159_ = 1;
v___x_3160_ = lean_array_uget_borrowed(v_as_3155_, v_i_3156_);
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = lean_array_get_size(v___x_3160_);
v___x_3163_ = lean_nat_dec_lt(v___x_3161_, v___x_3162_);
if (v___x_3163_ == 0)
{
return v___x_3159_;
}
else
{
if (v___x_3163_ == 0)
{
return v___x_3159_;
}
else
{
size_t v___x_3164_; size_t v___x_3165_; uint8_t v___x_3166_; 
v___x_3164_ = ((size_t)0ULL);
v___x_3165_ = lean_usize_of_nat(v___x_3162_);
v___x_3166_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3154_, v___x_3160_, v___x_3164_, v___x_3165_);
if (v___x_3166_ == 0)
{
return v___x_3159_;
}
else
{
if (v___x_3158_ == 0)
{
size_t v___x_3167_; size_t v___x_3168_; 
v___x_3167_ = ((size_t)1ULL);
v___x_3168_ = lean_usize_add(v_i_3156_, v___x_3167_);
v_i_3156_ = v___x_3168_;
goto _start;
}
else
{
return v___x_3159_;
}
}
}
}
}
else
{
uint8_t v___x_3170_; 
v___x_3170_ = 0;
return v___x_3170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1___boxed(lean_object* v_ver_3171_, lean_object* v_as_3172_, lean_object* v_i_3173_, lean_object* v_stop_3174_){
_start:
{
size_t v_i_boxed_3175_; size_t v_stop_boxed_3176_; uint8_t v_res_3177_; lean_object* v_r_3178_; 
v_i_boxed_3175_ = lean_unbox_usize(v_i_3173_);
lean_dec(v_i_3173_);
v_stop_boxed_3176_ = lean_unbox_usize(v_stop_3174_);
lean_dec(v_stop_3174_);
v_res_3177_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3171_, v_as_3172_, v_i_boxed_3175_, v_stop_boxed_3176_);
lean_dec_ref(v_as_3172_);
lean_dec_ref(v_ver_3171_);
v_r_3178_ = lean_box(v_res_3177_);
return v_r_3178_;
}
}
LEAN_EXPORT uint8_t l_Lake_VerRange_test(lean_object* v_self_3179_, lean_object* v_ver_3180_){
_start:
{
lean_object* v_clauses_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v_clauses_3181_ = lean_ctor_get(v_self_3179_, 1);
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = lean_array_get_size(v_clauses_3181_);
v___x_3184_ = lean_nat_dec_lt(v___x_3182_, v___x_3183_);
if (v___x_3184_ == 0)
{
return v___x_3184_;
}
else
{
if (v___x_3184_ == 0)
{
return v___x_3184_;
}
else
{
size_t v___x_3185_; size_t v___x_3186_; uint8_t v___x_3187_; 
v___x_3185_ = ((size_t)0ULL);
v___x_3186_ = lean_usize_of_nat(v___x_3183_);
v___x_3187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3180_, v_clauses_3181_, v___x_3185_, v___x_3186_);
return v___x_3187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_test___boxed(lean_object* v_self_3188_, lean_object* v_ver_3189_){
_start:
{
uint8_t v_res_3190_; lean_object* v_r_3191_; 
v_res_3190_ = l_Lake_VerRange_test(v_self_3188_, v_ver_3189_);
lean_dec_ref(v_ver_3189_);
lean_dec_ref(v_self_3188_);
v_r_3191_ = lean_box(v_res_3190_);
return v_r_3191_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Date(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Trie(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
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
