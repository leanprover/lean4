// Lean compiler output
// Module: Lean.DocString.View
// Imports: public import Lean.DocString.Types public import Lean.Parser.Term.Basic public import Lean.DocString.Syntax meta import Lean.DocString.Syntax
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoRefName(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
extern lean_object* l_Lean_Doc_versoCodeKind;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
extern lean_object* l_Lean_Doc_versoCodeLineKind;
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Doc_versoCodeBlockKind;
extern lean_object* l_Lean_Doc_versoLinkRefUrlKind;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l_Lean_Doc_versoImageAltKind;
lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object*);
extern lean_object* l_Lean_Doc_versoTextKind;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_Doc_versoRefKind;
lean_object* l_Lean_TSyntax_getVersoCode(lean_object*);
lean_object* l_Lean_TSyntax_getVersoTextSource(lean_object*);
lean_object* l_Lean_TSyntax_getVersoDelimiter(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
extern lean_object* l_Lean_Doc_versoLinkUrlKind;
lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object*);
lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_TSyntax_getVersoImageAlt(lean_object*);
lean_object* l_Lean_TSyntax_getVersoText(lean_object*);
lean_object* l_Lean_TSyntax_getVersoLinkRefUrl(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_name_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_name_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__0 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__1 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__2 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ArgVal"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__3 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__3_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__4 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__4_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__5_value_aux_3),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__4_value),LEAN_SCALAR_PTR_LITERAL(46, 191, 138, 67, 72, 90, 15, 127)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__5 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__5_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__6 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__6_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__7_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__7_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__7_value_aux_2),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__7_value_aux_3),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__6_value),LEAN_SCALAR_PTR_LITERAL(233, 188, 228, 197, 246, 25, 189, 153)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__7 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__7_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__8 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__8_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__9_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__9_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__9_value_aux_2),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__9_value_aux_3),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__8_value),LEAN_SCALAR_PTR_LITERAL(165, 66, 72, 255, 161, 123, 180, 197)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__9 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__9_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__8_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__10 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__10_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__11 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__11_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__12 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_ArgView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Arg"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__0 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value;
static const lean_string_object l_Lean_Doc_ArgView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "anon"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__1 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__1_value;
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_ArgView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 126, 223, 228, 215, 141, 22, 177)}};
static const lean_object* l_Lean_Doc_ArgView_of___closed__2 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__2_value;
static const lean_string_object l_Lean_Doc_ArgView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "named"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__3 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__3_value;
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__4_value_aux_3),((lean_object*)&l_Lean_Doc_ArgView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(195, 213, 136, 95, 26, 15, 91, 243)}};
static const lean_object* l_Lean_Doc_ArgView_of___closed__4 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__4_value;
static const lean_string_object l_Lean_Doc_ArgView_of___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "named_no_paren"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__5 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__5_value;
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__6_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__6_value_aux_3),((lean_object*)&l_Lean_Doc_ArgView_of___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 130, 4, 13, 153, 240, 131, 1)}};
static const lean_object* l_Lean_Doc_ArgView_of___closed__6 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__6_value;
static const lean_string_object l_Lean_Doc_ArgView_of___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "flag_on"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__7 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__7_value;
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__8_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__8_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__8_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__8_value_aux_3),((lean_object*)&l_Lean_Doc_ArgView_of___closed__7_value),LEAN_SCALAR_PTR_LITERAL(199, 11, 92, 179, 92, 210, 69, 32)}};
static const lean_object* l_Lean_Doc_ArgView_of___closed__8 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__8_value;
static const lean_string_object l_Lean_Doc_ArgView_of___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "flag_off"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__9 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__9_value;
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__10_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__10_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__10_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__10_value_aux_3),((lean_object*)&l_Lean_Doc_ArgView_of___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 14, 2, 143, 165, 169, 65, 229)}};
static const lean_object* l_Lean_Doc_ArgView_of___closed__10 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo___boxed(lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\\"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0_value),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__1 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_mkVersoCodeFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Doc_mkVersoCodeFrom___closed__0 = (const lean_object*)&l_Lean_Doc_mkVersoCodeFrom___closed__0_value;
static const lean_ctor_object l_Lean_Doc_mkVersoCodeFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_mkVersoCodeFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Doc_mkVersoCodeFrom___closed__1 = (const lean_object*)&l_Lean_Doc_mkVersoCodeFrom___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Inline"};
static const lean_object* l_Lean_Doc_mkVersoLinebreakFrom___closed__0 = (const lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value;
static const lean_string_object l_Lean_Doc_mkVersoLinebreakFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l_Lean_Doc_mkVersoLinebreakFrom___closed__1 = (const lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__1_value;
static const lean_ctor_object l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(175, 150, 35, 119, 78, 160, 253, 84)}};
static const lean_object* l_Lean_Doc_mkVersoLinebreakFrom___closed__2 = (const lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value;
static const lean_string_object l_Lean_Doc_mkVersoLinebreakFrom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Doc_mkVersoLinebreakFrom___closed__3 = (const lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_LinkTargetView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LinkTarget"};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__0 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__0_value;
static const lean_string_object l_Lean_Doc_LinkTargetView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "url"};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__1 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__1_value;
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(57, 222, 147, 211, 241, 202, 7, 251)}};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__2 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__2_value;
static const lean_string_object l_Lean_Doc_LinkTargetView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ref"};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__3 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__3_value;
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__4_value_aux_3),((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 54, 241, 38, 78, 206, 156, 5)}};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__4 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__4_value;
static const lean_string_object l_Lean_Doc_LinkTargetView_of___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "versoRef"};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__5 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__5_value;
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__6_value_aux_2),((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__5_value),LEAN_SCALAR_PTR_LITERAL(50, 44, 27, 25, 170, 146, 153, 245)}};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__6 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__6_value;
static const lean_string_object l_Lean_Doc_LinkTargetView_of___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "versoLinkUrl"};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__7 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__7_value;
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__8_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__8_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__8_value_aux_2),((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__7_value),LEAN_SCALAR_PTR_LITERAL(142, 188, 54, 130, 131, 60, 251, 148)}};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__8 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_of(lean_object*);
static const lean_ctor_object l_Lean_Doc_instInhabitedTextView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instInhabitedTextView_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedTextView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedTextView_default = (const lean_object*)&l_Lean_Doc_instInhabitedTextView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedTextView = (const lean_object*)&l_Lean_Doc_instInhabitedTextView_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_TextView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Doc_TextView_of___closed__0 = (const lean_object*)&l_Lean_Doc_TextView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_TextView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 133, 107, 199, 31, 216, 160, 200)}};
static const lean_object* l_Lean_Doc_TextView_of___closed__1 = (const lean_object*)&l_Lean_Doc_TextView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_TextView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoText"};
static const lean_object* l_Lean_Doc_TextView_of___closed__2 = (const lean_object*)&l_Lean_Doc_TextView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_TextView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 255, 240, 17, 75, 250, 253, 95)}};
static const lean_object* l_Lean_Doc_TextView_of___closed__3 = (const lean_object*)&l_Lean_Doc_TextView_of___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_of(lean_object*);
static const lean_string_object l_Lean_Doc_EmphView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "emph"};
static const lean_object* l_Lean_Doc_EmphView_of___closed__0 = (const lean_object*)&l_Lean_Doc_EmphView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_EmphView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_EmphView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_EmphView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_EmphView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_EmphView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_EmphView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_EmphView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_EmphView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_EmphView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_EmphView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 215, 18, 85, 144, 91, 153, 50)}};
static const lean_object* l_Lean_Doc_EmphView_of___closed__1 = (const lean_object*)&l_Lean_Doc_EmphView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_EmphView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "emphDelimiter"};
static const lean_object* l_Lean_Doc_EmphView_of___closed__2 = (const lean_object*)&l_Lean_Doc_EmphView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_EmphView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_EmphView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_EmphView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_EmphView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_EmphView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_EmphView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_EmphView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_EmphView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(14, 57, 61, 189, 31, 180, 10, 101)}};
static const lean_object* l_Lean_Doc_EmphView_of___closed__3 = (const lean_object*)&l_Lean_Doc_EmphView_of___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_EmphView_of(lean_object*);
static const lean_string_object l_Lean_Doc_BoldView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bold"};
static const lean_object* l_Lean_Doc_BoldView_of___closed__0 = (const lean_object*)&l_Lean_Doc_BoldView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_BoldView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_BoldView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BoldView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_BoldView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BoldView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_BoldView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BoldView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_BoldView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BoldView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_BoldView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 21, 54, 220, 135, 144, 211, 134)}};
static const lean_object* l_Lean_Doc_BoldView_of___closed__1 = (const lean_object*)&l_Lean_Doc_BoldView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_BoldView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "boldDelimiter"};
static const lean_object* l_Lean_Doc_BoldView_of___closed__2 = (const lean_object*)&l_Lean_Doc_BoldView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_BoldView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_BoldView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BoldView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_BoldView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BoldView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_BoldView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BoldView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_BoldView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(187, 9, 73, 54, 22, 222, 115, 214)}};
static const lean_object* l_Lean_Doc_BoldView_of___closed__3 = (const lean_object*)&l_Lean_Doc_BoldView_of___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_BoldView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_CodeView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_Lean_Doc_CodeView_of___closed__0 = (const lean_object*)&l_Lean_Doc_CodeView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_CodeView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 30, 73, 79, 76, 254, 8, 196)}};
static const lean_object* l_Lean_Doc_CodeView_of___closed__1 = (const lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_CodeView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "codeDelimiter"};
static const lean_object* l_Lean_Doc_CodeView_of___closed__2 = (const lean_object*)&l_Lean_Doc_CodeView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_CodeView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 116, 135, 82, 225, 37, 203, 104)}};
static const lean_object* l_Lean_Doc_CodeView_of___closed__3 = (const lean_object*)&l_Lean_Doc_CodeView_of___closed__3_value;
static const lean_string_object l_Lean_Doc_CodeView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoCode"};
static const lean_object* l_Lean_Doc_CodeView_of___closed__4 = (const lean_object*)&l_Lean_Doc_CodeView_of___closed__4_value;
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_CodeView_of___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 134, 52, 97, 245, 192, 23, 73)}};
static const lean_object* l_Lean_Doc_CodeView_of___closed__5 = (const lean_object*)&l_Lean_Doc_CodeView_of___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_MathView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inline_math"};
static const lean_object* l_Lean_Doc_MathView_of___closed__0 = (const lean_object*)&l_Lean_Doc_MathView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_MathView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 236, 9, 179, 133, 206, 252, 7)}};
static const lean_object* l_Lean_Doc_MathView_of___closed__1 = (const lean_object*)&l_Lean_Doc_MathView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_MathView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "display_math"};
static const lean_object* l_Lean_Doc_MathView_of___closed__2 = (const lean_object*)&l_Lean_Doc_MathView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__3_value_aux_3),((lean_object*)&l_Lean_Doc_MathView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 39, 73, 53, 10, 24, 181, 77)}};
static const lean_object* l_Lean_Doc_MathView_of___closed__3 = (const lean_object*)&l_Lean_Doc_MathView_of___closed__3_value;
static const lean_string_object l_Lean_Doc_MathView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "displayMathMarker"};
static const lean_object* l_Lean_Doc_MathView_of___closed__4 = (const lean_object*)&l_Lean_Doc_MathView_of___closed__4_value;
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_MathView_of___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 18, 116, 40, 86, 165, 207, 150)}};
static const lean_object* l_Lean_Doc_MathView_of___closed__5 = (const lean_object*)&l_Lean_Doc_MathView_of___closed__5_value;
static const lean_string_object l_Lean_Doc_MathView_of___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "inlineMathMarker"};
static const lean_object* l_Lean_Doc_MathView_of___closed__6 = (const lean_object*)&l_Lean_Doc_MathView_of___closed__6_value;
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__7_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__7_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_MathView_of___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MathView_of___closed__7_value_aux_2),((lean_object*)&l_Lean_Doc_MathView_of___closed__6_value),LEAN_SCALAR_PTR_LITERAL(102, 9, 108, 134, 130, 7, 90, 114)}};
static const lean_object* l_Lean_Doc_MathView_of___closed__7 = (const lean_object*)&l_Lean_Doc_MathView_of___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_of(lean_object*);
static const lean_string_object l_Lean_Doc_LinkView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l_Lean_Doc_LinkView_of___closed__0 = (const lean_object*)&l_Lean_Doc_LinkView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_LinkView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_LinkView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_LinkView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 237, 8, 103, 58, 149, 183, 251)}};
static const lean_object* l_Lean_Doc_LinkView_of___closed__1 = (const lean_object*)&l_Lean_Doc_LinkView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_LinkView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_ImageView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "image"};
static const lean_object* l_Lean_Doc_ImageView_of___closed__0 = (const lean_object*)&l_Lean_Doc_ImageView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_ImageView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 170, 102, 209, 119, 14, 254, 233)}};
static const lean_object* l_Lean_Doc_ImageView_of___closed__1 = (const lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_ImageView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "versoImageAlt"};
static const lean_object* l_Lean_Doc_ImageView_of___closed__2 = (const lean_object*)&l_Lean_Doc_ImageView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_ImageView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(83, 180, 119, 241, 128, 95, 219, 17)}};
static const lean_object* l_Lean_Doc_ImageView_of___closed__3 = (const lean_object*)&l_Lean_Doc_ImageView_of___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_FootnoteView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "footnote"};
static const lean_object* l_Lean_Doc_FootnoteView_of___closed__0 = (const lean_object*)&l_Lean_Doc_FootnoteView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_FootnoteView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_FootnoteView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_FootnoteView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_FootnoteView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_FootnoteView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_FootnoteView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_FootnoteView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_FootnoteView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_FootnoteView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_FootnoteView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 121, 147, 210, 143, 103, 0, 217)}};
static const lean_object* l_Lean_Doc_FootnoteView_of___closed__1 = (const lean_object*)&l_Lean_Doc_FootnoteView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinebreakView_of(lean_object*);
static const lean_string_object l_Lean_Doc_RoleView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "role"};
static const lean_object* l_Lean_Doc_RoleView_of___closed__0 = (const lean_object*)&l_Lean_Doc_RoleView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_RoleView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_RoleView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_RoleView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_RoleView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_RoleView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_RoleView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_RoleView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_RoleView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_RoleView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_RoleView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 233, 178, 241, 96, 238, 218, 92)}};
static const lean_object* l_Lean_Doc_RoleView_of___closed__1 = (const lean_object*)&l_Lean_Doc_RoleView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_RoleView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Doc_instInhabitedInlineView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedTextView_default___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedInlineView_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedInlineView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedInlineView_default = (const lean_object*)&l_Lean_Doc_instInhabitedInlineView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedInlineView = (const lean_object*)&l_Lean_Doc_instInhabitedInlineView_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTextViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTextViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTextViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTextViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTextViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTextViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeTextViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeEmphViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeEmphViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeEmphViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeEmphViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeEmphViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeEmphViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeEmphViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBoldViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeBoldViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeBoldViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeBoldViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeBoldViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeBoldViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeBoldViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeCodeViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeCodeViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeCodeViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeCodeViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeCodeViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeCodeViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMathViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeMathViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeMathViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeMathViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeMathViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeMathViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeMathViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeLinkViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeLinkViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeLinkViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeLinkViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeLinkViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeLinkViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeImageViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeImageViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeImageViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeImageViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeImageViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeImageViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeImageViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeFootnoteViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeFootnoteViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeFootnoteViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeLinebreakViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeLinebreakViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeLinebreakViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeRoleViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeRoleViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeRoleViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeRoleViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeRoleViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeRoleViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeRoleViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_of(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_UnorderedListItemView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ListItem"};
static const lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__0 = (const lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__0_value;
static const lean_string_object l_Lean_Doc_UnorderedListItemView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "item"};
static const lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__1 = (const lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__1_value;
static const lean_ctor_object l_Lean_Doc_UnorderedListItemView_of___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListItemView_of___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListItemView_of___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListItemView_of___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 153, 101, 209, 126, 16, 11, 208)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListItemView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 123, 16, 134, 76, 179, 171, 228)}};
static const lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__2 = (const lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__2_value;
static const lean_string_object l_Lean_Doc_UnorderedListItemView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "listMarker"};
static const lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__3 = (const lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__3_value;
static const lean_ctor_object l_Lean_Doc_UnorderedListItemView_of___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListItemView_of___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListItemView_of___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListItemView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(220, 134, 18, 7, 181, 33, 85, 37)}};
static const lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__4 = (const lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_UnorderedListItemView_of___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_UnorderedListItemView_of___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__6;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_UnorderedListItemView_of___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__7;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_number(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_of(lean_object*);
static const lean_string_object l_Lean_Doc_DescItemView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DescItem"};
static const lean_object* l_Lean_Doc_DescItemView_of___closed__0 = (const lean_object*)&l_Lean_Doc_DescItemView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_DescItemView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_DescItemView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DescItemView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_DescItemView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DescItemView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_DescItemView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DescItemView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_DescItemView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 70, 30, 3, 105, 156, 130, 115)}};
static const lean_ctor_object l_Lean_Doc_DescItemView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DescItemView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_UnorderedListItemView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 193, 144, 210, 183, 212, 114, 89)}};
static const lean_object* l_Lean_Doc_DescItemView_of___closed__1 = (const lean_object*)&l_Lean_Doc_DescItemView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_DescItemView_of(lean_object*);
static const lean_array_object l_Lean_Doc_instInhabitedParaView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_instInhabitedParaView_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instInhabitedParaView_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedParaView_default___closed__1 = (const lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedParaView_default = (const lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedParaView = (const lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__1_value;
static const lean_string_object l_Lean_Doc_ParaView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Block"};
static const lean_object* l_Lean_Doc_ParaView_of___closed__0 = (const lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value;
static const lean_string_object l_Lean_Doc_ParaView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "para"};
static const lean_object* l_Lean_Doc_ParaView_of___closed__1 = (const lean_object*)&l_Lean_Doc_ParaView_of___closed__1_value;
static const lean_ctor_object l_Lean_Doc_ParaView_of___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ParaView_of___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ParaView_of___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ParaView_of___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ParaView_of___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ParaView_of___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ParaView_of___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_ParaView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ParaView_of___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_ParaView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(10, 167, 213, 66, 92, 160, 222, 146)}};
static const lean_object* l_Lean_Doc_ParaView_of___closed__2 = (const lean_object*)&l_Lean_Doc_ParaView_of___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Doc_ParaView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_UnorderedListView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ul"};
static const lean_object* l_Lean_Doc_UnorderedListView_of___closed__0 = (const lean_object*)&l_Lean_Doc_UnorderedListView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_UnorderedListView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_UnorderedListView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_UnorderedListView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_UnorderedListView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 45, 1, 212, 241, 159, 201, 84)}};
static const lean_object* l_Lean_Doc_UnorderedListView_of___closed__1 = (const lean_object*)&l_Lean_Doc_UnorderedListView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_OrderedListView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ol"};
static const lean_object* l_Lean_Doc_OrderedListView_of___closed__0 = (const lean_object*)&l_Lean_Doc_OrderedListView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_OrderedListView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_OrderedListView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_OrderedListView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_OrderedListView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_OrderedListView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_OrderedListView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_OrderedListView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_OrderedListView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_OrderedListView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_OrderedListView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 199, 227, 191, 40, 60, 185, 243)}};
static const lean_object* l_Lean_Doc_OrderedListView_of___closed__1 = (const lean_object*)&l_Lean_Doc_OrderedListView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_DescListView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "dl"};
static const lean_object* l_Lean_Doc_DescListView_of___closed__0 = (const lean_object*)&l_Lean_Doc_DescListView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_DescListView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_DescListView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DescListView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_DescListView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DescListView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_DescListView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DescListView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_DescListView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DescListView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_DescListView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 15, 76, 66, 114, 120, 124, 74)}};
static const lean_object* l_Lean_Doc_DescListView_of___closed__1 = (const lean_object*)&l_Lean_Doc_DescListView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_DescListView_of(lean_object*);
static const lean_string_object l_Lean_Doc_BlockquoteView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "blockquote"};
static const lean_object* l_Lean_Doc_BlockquoteView_of___closed__0 = (const lean_object*)&l_Lean_Doc_BlockquoteView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_BlockquoteView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_BlockquoteView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BlockquoteView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_BlockquoteView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BlockquoteView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_BlockquoteView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BlockquoteView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_BlockquoteView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_BlockquoteView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_BlockquoteView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 145, 178, 243, 42, 6, 105, 104)}};
static const lean_object* l_Lean_Doc_BlockquoteView_of___closed__1 = (const lean_object*)&l_Lean_Doc_BlockquoteView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_BlockquoteView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_CodeBlockView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "codeblock"};
static const lean_object* l_Lean_Doc_CodeBlockView_of___closed__0 = (const lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 32, 43, 99, 217, 167, 97, 87)}};
static const lean_object* l_Lean_Doc_CodeBlockView_of___closed__1 = (const lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_CodeBlockView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "versoCodeBlock"};
static const lean_object* l_Lean_Doc_CodeBlockView_of___closed__2 = (const lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(244, 196, 91, 225, 102, 151, 154, 53)}};
static const lean_object* l_Lean_Doc_CodeBlockView_of___closed__3 = (const lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__3_value;
static const lean_string_object l_Lean_Doc_CodeBlockView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "codeBlockFence"};
static const lean_object* l_Lean_Doc_CodeBlockView_of___closed__4 = (const lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__4_value;
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__4_value),LEAN_SCALAR_PTR_LITERAL(197, 154, 39, 84, 226, 168, 56, 199)}};
static const lean_object* l_Lean_Doc_CodeBlockView_of___closed__5 = (const lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_of(lean_object*);
static const lean_string_object l_Lean_Doc_DirectiveView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "directive"};
static const lean_object* l_Lean_Doc_DirectiveView_of___closed__0 = (const lean_object*)&l_Lean_Doc_DirectiveView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_DirectiveView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_DirectiveView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DirectiveView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_DirectiveView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DirectiveView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_DirectiveView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DirectiveView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_DirectiveView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DirectiveView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_DirectiveView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 234, 1, 42, 159, 198, 19, 176)}};
static const lean_object* l_Lean_Doc_DirectiveView_of___closed__1 = (const lean_object*)&l_Lean_Doc_DirectiveView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_DirectiveView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "directiveDelimiter"};
static const lean_object* l_Lean_Doc_DirectiveView_of___closed__2 = (const lean_object*)&l_Lean_Doc_DirectiveView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_DirectiveView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_DirectiveView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DirectiveView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_DirectiveView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DirectiveView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_DirectiveView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_DirectiveView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_DirectiveView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(190, 28, 38, 38, 72, 11, 173, 25)}};
static const lean_object* l_Lean_Doc_DirectiveView_of___closed__3 = (const lean_object*)&l_Lean_Doc_DirectiveView_of___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_DirectiveView_of(lean_object*);
static const lean_string_object l_Lean_Doc_CommandView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Doc_CommandView_of___closed__0 = (const lean_object*)&l_Lean_Doc_CommandView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_CommandView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CommandView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CommandView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CommandView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CommandView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CommandView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CommandView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_CommandView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CommandView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_CommandView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 232, 253, 29, 141, 75, 139, 21)}};
static const lean_object* l_Lean_Doc_CommandView_of___closed__1 = (const lean_object*)&l_Lean_Doc_CommandView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_CommandView_of(lean_object*);
static const lean_string_object l_Lean_Doc_HeaderView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Doc_HeaderView_of___closed__0 = (const lean_object*)&l_Lean_Doc_HeaderView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_HeaderView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_HeaderView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_HeaderView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_HeaderView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_HeaderView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_HeaderView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_HeaderView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_HeaderView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_HeaderView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_HeaderView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 176, 128, 73, 36, 235, 244, 141)}};
static const lean_object* l_Lean_Doc_HeaderView_of___closed__1 = (const lean_object*)&l_Lean_Doc_HeaderView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_HeaderView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "headerMarker"};
static const lean_object* l_Lean_Doc_HeaderView_of___closed__2 = (const lean_object*)&l_Lean_Doc_HeaderView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_HeaderView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_HeaderView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_HeaderView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_HeaderView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_HeaderView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_HeaderView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_HeaderView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_HeaderView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(79, 163, 210, 90, 152, 248, 144, 166)}};
static const lean_object* l_Lean_Doc_HeaderView_of___closed__3 = (const lean_object*)&l_Lean_Doc_HeaderView_of___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_HeaderView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_LinkRefView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "link_ref"};
static const lean_object* l_Lean_Doc_LinkRefView_of___closed__0 = (const lean_object*)&l_Lean_Doc_LinkRefView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 199, 233, 128, 119, 237, 18, 215)}};
static const lean_object* l_Lean_Doc_LinkRefView_of___closed__1 = (const lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_LinkRefView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "versoLinkRefUrl"};
static const lean_object* l_Lean_Doc_LinkRefView_of___closed__2 = (const lean_object*)&l_Lean_Doc_LinkRefView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 57, 106, 22, 121, 78, 15, 41)}};
static const lean_object* l_Lean_Doc_LinkRefView_of___closed__3 = (const lean_object*)&l_Lean_Doc_LinkRefView_of___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_FootnoteRefView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "footnote_ref"};
static const lean_object* l_Lean_Doc_FootnoteRefView_of___closed__0 = (const lean_object*)&l_Lean_Doc_FootnoteRefView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_FootnoteRefView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_FootnoteRefView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_FootnoteRefView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_FootnoteRefView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_FootnoteRefView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_FootnoteRefView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_FootnoteRefView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_FootnoteRefView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_FootnoteRefView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_FootnoteRefView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 53, 29, 246, 154, 171, 121, 154)}};
static const lean_object* l_Lean_Doc_FootnoteRefView_of___closed__1 = (const lean_object*)&l_Lean_Doc_FootnoteRefView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_MetadataView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "metadata_block"};
static const lean_object* l_Lean_Doc_MetadataView_of___closed__0 = (const lean_object*)&l_Lean_Doc_MetadataView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_MetadataView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_MetadataView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MetadataView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_MetadataView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MetadataView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_MetadataView_of___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MetadataView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ParaView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_MetadataView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MetadataView_of___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_MetadataView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 125, 116, 48, 167, 45, 110, 42)}};
static const lean_object* l_Lean_Doc_MetadataView_of___closed__1 = (const lean_object*)&l_Lean_Doc_MetadataView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_MetadataView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Doc_MetadataView_of___closed__2 = (const lean_object*)&l_Lean_Doc_MetadataView_of___closed__2_value;
static const lean_string_object l_Lean_Doc_MetadataView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lean_Doc_MetadataView_of___closed__3 = (const lean_object*)&l_Lean_Doc_MetadataView_of___closed__3_value;
static const lean_ctor_object l_Lean_Doc_MetadataView_of___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_MetadataView_of___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MetadataView_of___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Doc_MetadataView_of___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MetadataView_of___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_MetadataView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Doc_MetadataView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_MetadataView_of___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_MetadataView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lean_Doc_MetadataView_of___closed__4 = (const lean_object*)&l_Lean_Doc_MetadataView_of___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Doc_instInhabitedBlockView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__1_value)}};
static const lean_object* l_Lean_Doc_instInhabitedBlockView_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedBlockView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedBlockView_default = (const lean_object*)&l_Lean_Doc_instInhabitedBlockView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedBlockView = (const lean_object*)&l_Lean_Doc_instInhabitedBlockView_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeParaViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeParaViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeParaViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeParaViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeParaViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeParaViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeParaViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeUnorderedListViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeUnorderedListViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeUnorderedListViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeOrderedListViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeOrderedListViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeOrderedListViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDescListViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeDescListViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeDescListViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeDescListViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeDescListViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeDescListViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeDescListViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeBlockquoteViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeBlockquoteViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeBlockquoteViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeCodeBlockViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeCodeBlockViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeCodeBlockViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeDirectiveViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeDirectiveViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeDirectiveViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCommandViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeCommandViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeCommandViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeCommandViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeCommandViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeCommandViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeCommandViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeHeaderViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeHeaderViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeHeaderViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeHeaderViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeHeaderViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeLinkRefViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeLinkRefViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeLinkRefViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeFootnoteRefViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeFootnoteRefViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeFootnoteRefViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeMetadataViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeMetadataViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeMetadataViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeMetadataViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeMetadataViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoInline_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoBlock_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Doc_ArgValView_ctorIdx(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
switch(lean_obj_tag(v_t_7_))
{
case 0:
{
lean_object* v_lit_9_; lean_object* v_value_10_; lean_object* v___x_11_; 
v_lit_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_lit_9_);
v_value_10_ = lean_ctor_get(v_t_7_, 1);
lean_inc_ref(v_value_10_);
lean_dec_ref_known(v_t_7_, 2);
v___x_11_ = lean_apply_2(v_k_8_, v_lit_9_, v_value_10_);
return v___x_11_;
}
case 1:
{
lean_object* v_x_12_; lean_object* v___x_13_; 
v_x_12_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_x_12_);
lean_dec_ref_known(v_t_7_, 1);
v___x_13_ = lean_apply_1(v_k_8_, v_x_12_);
return v___x_13_;
}
default: 
{
lean_object* v_lit_14_; lean_object* v_value_15_; lean_object* v___x_16_; 
v_lit_14_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_lit_14_);
v_value_15_ = lean_ctor_get(v_t_7_, 1);
lean_inc(v_value_15_);
lean_dec_ref_known(v_t_7_, 2);
v___x_16_ = lean_apply_2(v_k_8_, v_lit_14_, v_value_15_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_19_, v_k_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim___boxed(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Doc_ArgValView_ctorElim(v_motive_23_, v_ctorIdx_24_, v_t_25_, v_h_26_, v_k_27_);
lean_dec(v_ctorIdx_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_str_elim___redArg(lean_object* v_t_29_, lean_object* v_str_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_29_, v_str_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_str_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_str_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_33_, v_str_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_name_elim___redArg(lean_object* v_t_37_, lean_object* v_name_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_37_, v_name_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_name_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_name_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_41_, v_name_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_num_elim___redArg(lean_object* v_t_45_, lean_object* v_num_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_45_, v_num_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_num_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_num_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_49_, v_num_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_of(lean_object* v_stx_84_){
_start:
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__5));
lean_inc(v_stx_84_);
v___x_86_ = l_Lean_Syntax_isOfKind(v_stx_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__7));
lean_inc(v_stx_84_);
v___x_88_ = l_Lean_Syntax_isOfKind(v_stx_84_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__9));
lean_inc(v_stx_84_);
v___x_90_ = l_Lean_Syntax_isOfKind(v_stx_84_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
lean_dec(v_stx_84_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v___x_92_; lean_object* v_s_93_; 
v___x_92_ = lean_unsigned_to_nat(0u);
v_s_93_ = l_Lean_Syntax_getArg(v_stx_84_, v___x_92_);
lean_dec(v_stx_84_);
if (v___x_88_ == 0)
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__10));
lean_inc(v_s_93_);
v___x_99_ = l_Lean_Syntax_isOfKind(v_s_93_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec(v_s_93_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
goto v___jp_94_;
}
}
else
{
goto v___jp_94_;
}
v___jp_94_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = l_Lean_TSyntax_getString(v_s_93_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_s_93_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
}
else
{
lean_object* v___x_101_; lean_object* v_n_102_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v_n_102_ = l_Lean_Syntax_getArg(v_stx_84_, v___x_101_);
lean_dec(v_stx_84_);
if (v___x_86_ == 0)
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__11));
lean_inc(v_n_102_);
v___x_108_ = l_Lean_Syntax_isOfKind(v_n_102_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
lean_dec(v_n_102_);
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
goto v___jp_103_;
}
}
else
{
goto v___jp_103_;
}
v___jp_103_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = l_Lean_TSyntax_getNat(v_n_102_);
v___x_105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_105_, 0, v_n_102_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
}
else
{
lean_object* v___x_110_; lean_object* v_x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_110_ = lean_unsigned_to_nat(0u);
v_x_111_ = l_Lean_Syntax_getArg(v_stx_84_, v___x_110_);
lean_dec(v_stx_84_);
v___x_112_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_111_);
v___x_113_ = l_Lean_Syntax_isOfKind(v_x_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
lean_dec(v_x_111_);
v___x_114_ = lean_box(0);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v_x_111_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx(lean_object* v_x_117_){
_start:
{
switch(lean_obj_tag(v_x_117_))
{
case 0:
{
lean_object* v___x_118_; 
v___x_118_ = lean_unsigned_to_nat(0u);
return v___x_118_;
}
case 1:
{
lean_object* v___x_119_; 
v___x_119_ = lean_unsigned_to_nat(1u);
return v___x_119_;
}
default: 
{
lean_object* v___x_120_; 
v___x_120_ = lean_unsigned_to_nat(2u);
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx___boxed(lean_object* v_x_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Doc_ArgView_ctorIdx(v_x_121_);
lean_dec_ref(v_x_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___redArg(lean_object* v_t_123_, lean_object* v_k_124_){
_start:
{
switch(lean_obj_tag(v_t_123_))
{
case 0:
{
lean_object* v_stx_125_; lean_object* v_val_126_; lean_object* v___x_127_; 
v_stx_125_ = lean_ctor_get(v_t_123_, 0);
lean_inc(v_stx_125_);
v_val_126_ = lean_ctor_get(v_t_123_, 1);
lean_inc(v_val_126_);
lean_dec_ref_known(v_t_123_, 2);
v___x_127_ = lean_apply_2(v_k_124_, v_stx_125_, v_val_126_);
return v___x_127_;
}
case 1:
{
lean_object* v_stx_128_; lean_object* v_parens_129_; lean_object* v_name_130_; lean_object* v_assign_131_; lean_object* v_val_132_; lean_object* v___x_133_; 
v_stx_128_ = lean_ctor_get(v_t_123_, 0);
lean_inc(v_stx_128_);
v_parens_129_ = lean_ctor_get(v_t_123_, 1);
lean_inc(v_parens_129_);
v_name_130_ = lean_ctor_get(v_t_123_, 2);
lean_inc(v_name_130_);
v_assign_131_ = lean_ctor_get(v_t_123_, 3);
lean_inc(v_assign_131_);
v_val_132_ = lean_ctor_get(v_t_123_, 4);
lean_inc(v_val_132_);
lean_dec_ref_known(v_t_123_, 5);
v___x_133_ = lean_apply_5(v_k_124_, v_stx_128_, v_parens_129_, v_name_130_, v_assign_131_, v_val_132_);
return v___x_133_;
}
default: 
{
lean_object* v_stx_134_; lean_object* v_sign_135_; lean_object* v_name_136_; uint8_t v_isOn_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_stx_134_ = lean_ctor_get(v_t_123_, 0);
lean_inc(v_stx_134_);
v_sign_135_ = lean_ctor_get(v_t_123_, 1);
lean_inc(v_sign_135_);
v_name_136_ = lean_ctor_get(v_t_123_, 2);
lean_inc(v_name_136_);
v_isOn_137_ = lean_ctor_get_uint8(v_t_123_, sizeof(void*)*3);
lean_dec_ref_known(v_t_123_, 3);
v___x_138_ = lean_box(v_isOn_137_);
v___x_139_ = lean_apply_4(v_k_124_, v_stx_134_, v_sign_135_, v_name_136_, v___x_138_);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim(lean_object* v_motive_140_, lean_object* v_ctorIdx_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_k_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_142_, v_k_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___boxed(lean_object* v_motive_146_, lean_object* v_ctorIdx_147_, lean_object* v_t_148_, lean_object* v_h_149_, lean_object* v_k_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Doc_ArgView_ctorElim(v_motive_146_, v_ctorIdx_147_, v_t_148_, v_h_149_, v_k_150_);
lean_dec(v_ctorIdx_147_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim___redArg(lean_object* v_t_152_, lean_object* v_anon_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_152_, v_anon_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim(lean_object* v_motive_155_, lean_object* v_t_156_, lean_object* v_h_157_, lean_object* v_anon_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_156_, v_anon_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim___redArg(lean_object* v_t_160_, lean_object* v_named_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_160_, v_named_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim(lean_object* v_motive_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_named_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_164_, v_named_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim___redArg(lean_object* v_t_168_, lean_object* v_flag_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_168_, v_flag_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim(lean_object* v_motive_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_flag_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_172_, v_flag_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx(lean_object* v_x_176_){
_start:
{
lean_object* v_stx_177_; 
v_stx_177_ = lean_ctor_get(v_x_176_, 0);
lean_inc(v_stx_177_);
return v_stx_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx___boxed(lean_object* v_x_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Doc_ArgView_stx(v_x_178_);
lean_dec_ref(v_x_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_of(lean_object* v_stx_216_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__2));
lean_inc(v_stx_216_);
v___x_218_ = l_Lean_Syntax_isOfKind(v_stx_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__4));
lean_inc(v_stx_216_);
v___x_220_ = l_Lean_Syntax_isOfKind(v_stx_216_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__6));
lean_inc(v_stx_216_);
v___x_222_ = l_Lean_Syntax_isOfKind(v_stx_216_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__8));
lean_inc(v_stx_216_);
v___x_224_ = l_Lean_Syntax_isOfKind(v_stx_216_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__10));
lean_inc(v_stx_216_);
v___x_226_ = l_Lean_Syntax_isOfKind(v_stx_216_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
lean_dec(v_stx_216_);
v___x_227_ = lean_box(0);
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v_tk_229_; lean_object* v___x_230_; lean_object* v_x_231_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v_tk_229_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(1u);
v_x_231_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_230_);
if (v___x_224_ == 0)
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_231_);
v___x_236_ = l_Lean_Syntax_isOfKind(v_x_231_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec(v_x_231_);
lean_dec(v_tk_229_);
lean_dec(v_stx_216_);
v___x_237_ = lean_box(0);
return v___x_237_;
}
else
{
goto v___jp_232_;
}
}
else
{
goto v___jp_232_;
}
v___jp_232_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_233_, 0, v_stx_216_);
lean_ctor_set(v___x_233_, 1, v_tk_229_);
lean_ctor_set(v___x_233_, 2, v_x_231_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*3, v___x_224_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
}
else
{
lean_object* v___x_238_; lean_object* v_tk_239_; lean_object* v___x_240_; lean_object* v_x_241_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v_tk_239_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_238_);
v___x_240_ = lean_unsigned_to_nat(1u);
v_x_241_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_240_);
if (v___x_222_ == 0)
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_241_);
v___x_246_ = l_Lean_Syntax_isOfKind(v_x_241_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
lean_dec(v_x_241_);
lean_dec(v_tk_239_);
lean_dec(v_stx_216_);
v___x_247_ = lean_box(0);
return v___x_247_;
}
else
{
goto v___jp_242_;
}
}
else
{
goto v___jp_242_;
}
v___jp_242_:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_243_, 0, v_stx_216_);
lean_ctor_set(v___x_243_, 1, v_tk_239_);
lean_ctor_set(v___x_243_, 2, v_x_241_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*3, v___x_224_);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
}
else
{
lean_object* v___x_248_; lean_object* v_x_249_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v_x_249_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_248_);
if (v___x_220_ == 0)
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_249_);
v___x_259_ = l_Lean_Syntax_isOfKind(v_x_249_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_x_249_);
lean_dec(v_stx_216_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
else
{
goto v___jp_250_;
}
}
else
{
goto v___jp_250_;
}
v___jp_250_:
{
lean_object* v___x_251_; lean_object* v_eq_252_; lean_object* v___x_253_; lean_object* v_v_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v_eq_252_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_251_);
v___x_253_ = lean_unsigned_to_nat(2u);
v_v_254_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_253_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(v___x_256_, 0, v_stx_216_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
lean_ctor_set(v___x_256_, 2, v_x_249_);
lean_ctor_set(v___x_256_, 3, v_eq_252_);
lean_ctor_set(v___x_256_, 4, v_v_254_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
else
{
lean_object* v___x_261_; lean_object* v_po_262_; lean_object* v___x_263_; lean_object* v_x_264_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v_po_262_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(1u);
v_x_264_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_263_);
if (v___x_218_ == 0)
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_264_);
v___x_277_ = l_Lean_Syntax_isOfKind(v_x_264_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec(v_x_264_);
lean_dec(v_po_262_);
lean_dec(v_stx_216_);
v___x_278_ = lean_box(0);
return v___x_278_;
}
else
{
goto v___jp_265_;
}
}
else
{
goto v___jp_265_;
}
v___jp_265_:
{
lean_object* v___x_266_; lean_object* v_eq_267_; lean_object* v___x_268_; lean_object* v_v_269_; lean_object* v___x_270_; lean_object* v_pc_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_266_ = lean_unsigned_to_nat(2u);
v_eq_267_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_266_);
v___x_268_ = lean_unsigned_to_nat(3u);
v_v_269_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_268_);
v___x_270_ = lean_unsigned_to_nat(4u);
v_pc_271_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_po_262_);
lean_ctor_set(v___x_272_, 1, v_pc_271_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
v___x_274_ = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(v___x_274_, 0, v_stx_216_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
lean_ctor_set(v___x_274_, 2, v_x_264_);
lean_ctor_set(v___x_274_, 3, v_eq_267_);
lean_ctor_set(v___x_274_, 4, v_v_269_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
}
else
{
lean_object* v___x_279_; lean_object* v_v_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v_v_280_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_stx_216_);
lean_ctor_set(v___x_281_, 1, v_v_280_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx(lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_unsigned_to_nat(0u);
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_unsigned_to_nat(1u);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx___boxed(lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Doc_LinkTargetView_ctorIdx(v_x_286_);
lean_dec_ref(v_x_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___redArg(lean_object* v_t_288_, lean_object* v_k_289_){
_start:
{
lean_object* v_stx_290_; lean_object* v_opener_291_; lean_object* v_url_292_; lean_object* v_closer_293_; lean_object* v___x_294_; 
v_stx_290_ = lean_ctor_get(v_t_288_, 0);
lean_inc(v_stx_290_);
v_opener_291_ = lean_ctor_get(v_t_288_, 1);
lean_inc(v_opener_291_);
v_url_292_ = lean_ctor_get(v_t_288_, 2);
lean_inc(v_url_292_);
v_closer_293_ = lean_ctor_get(v_t_288_, 3);
lean_inc(v_closer_293_);
lean_dec_ref(v_t_288_);
v___x_294_ = lean_apply_4(v_k_289_, v_stx_290_, v_opener_291_, v_url_292_, v_closer_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim(lean_object* v_motive_295_, lean_object* v_ctorIdx_296_, lean_object* v_t_297_, lean_object* v_h_298_, lean_object* v_k_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_297_, v_k_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___boxed(lean_object* v_motive_301_, lean_object* v_ctorIdx_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_k_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Doc_LinkTargetView_ctorElim(v_motive_301_, v_ctorIdx_302_, v_t_303_, v_h_304_, v_k_305_);
lean_dec(v_ctorIdx_302_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim___redArg(lean_object* v_t_307_, lean_object* v_url_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_307_, v_url_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim(lean_object* v_motive_310_, lean_object* v_t_311_, lean_object* v_h_312_, lean_object* v_url_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_311_, v_url_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim___redArg(lean_object* v_t_315_, lean_object* v_ref_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_315_, v_ref_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim(lean_object* v_motive_318_, lean_object* v_t_319_, lean_object* v_h_320_, lean_object* v_ref_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_319_, v_ref_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(lean_object* v_tok_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Syntax_getHeadInfo(v_tok_323_);
switch(lean_obj_tag(v___x_324_))
{
case 0:
{
lean_object* v_leading_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_346_; 
v_leading_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; lean_object* v_unused_348_; lean_object* v_unused_349_; 
v_unused_347_ = lean_ctor_get(v___x_324_, 3);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v___x_324_, 2);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v___x_324_, 1);
lean_dec(v_unused_349_);
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_346_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_leading_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_346_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint8_t v___x_329_; lean_object* v___x_330_; 
v___x_329_ = 0;
v___x_330_ = l_Lean_Syntax_getPos_x3f(v_tok_323_, v___x_329_);
if (lean_obj_tag(v___x_330_) == 1)
{
lean_object* v_val_331_; lean_object* v_str_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_342_; 
v_val_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v___x_330_, 1);
v_str_332_ = lean_ctor_get(v_leading_325_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_leading_325_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; lean_object* v_unused_344_; 
v_unused_343_ = lean_ctor_get(v_leading_325_, 2);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v_leading_325_, 1);
lean_dec(v_unused_344_);
v___x_334_ = v_leading_325_;
v_isShared_335_ = v_isSharedCheck_342_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_str_332_);
lean_dec(v_leading_325_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_342_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
lean_inc_n(v_val_331_, 2);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 2, v_val_331_);
lean_ctor_set(v___x_334_, 1, v_val_331_);
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_str_332_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_val_331_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_val_331_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_339_; 
lean_inc(v_val_331_);
lean_inc_ref(v___x_337_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 3, v_val_331_);
lean_ctor_set(v___x_327_, 2, v___x_337_);
lean_ctor_set(v___x_327_, 1, v_val_331_);
lean_ctor_set(v___x_327_, 0, v___x_337_);
v___x_339_ = v___x_327_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_val_331_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v_val_331_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v___x_345_; 
lean_dec(v___x_330_);
lean_del_object(v___x_327_);
lean_dec_ref(v_leading_325_);
v___x_345_ = lean_box(2);
return v___x_345_;
}
}
}
case 1:
{
uint8_t v_canonical_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_361_; 
v_canonical_350_ = lean_ctor_get_uint8(v___x_324_, sizeof(void*)*2);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; lean_object* v_unused_363_; 
v_unused_362_ = lean_ctor_get(v___x_324_, 1);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v___x_324_, 0);
lean_dec(v_unused_363_);
v___x_352_ = v___x_324_;
v_isShared_353_ = v_isSharedCheck_361_;
goto v_resetjp_351_;
}
else
{
lean_dec(v___x_324_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_361_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
uint8_t v___x_354_; lean_object* v___x_355_; 
v___x_354_ = 0;
v___x_355_ = l_Lean_Syntax_getPos_x3f(v_tok_323_, v___x_354_);
if (lean_obj_tag(v___x_355_) == 1)
{
lean_object* v_val_356_; lean_object* v___x_358_; 
v_val_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc_n(v_val_356_, 2);
lean_dec_ref_known(v___x_355_, 1);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v_val_356_);
lean_ctor_set(v___x_352_, 0, v_val_356_);
v___x_358_ = v___x_352_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_val_356_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_val_356_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*2, v_canonical_350_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
else
{
lean_object* v___x_360_; 
lean_dec(v___x_355_);
lean_del_object(v___x_352_);
v___x_360_ = lean_box(2);
return v___x_360_;
}
}
}
default: 
{
lean_object* v___x_364_; 
lean_dec(v___x_324_);
v___x_364_ = lean_box(2);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo___boxed(lean_object* v_tok_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v_tok_365_);
lean_dec(v_tok_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(lean_object* v___x_368_, lean_object* v_value_369_, lean_object* v_a_370_, lean_object* v_b_371_){
_start:
{
uint8_t v_decide_372_; 
v_decide_372_ = lean_nat_dec_eq(v_a_370_, v___x_368_);
if (v_decide_372_ == 0)
{
uint32_t v___x_373_; lean_object* v___x_374_; uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_373_ = lean_string_utf8_get_fast(v_value_369_, v_a_370_);
v___x_374_ = lean_string_utf8_next_fast(v_value_369_, v_a_370_);
lean_dec(v_a_370_);
v___x_375_ = 92;
v___x_376_ = lean_uint32_dec_eq(v___x_373_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
v___x_377_ = lean_string_push(v_b_371_, v___x_373_);
v_a_370_ = v___x_374_;
v_b_371_ = v___x_377_;
goto _start;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0));
v___x_380_ = lean_string_append(v_b_371_, v___x_379_);
v_a_370_ = v___x_374_;
v_b_371_ = v___x_380_;
goto _start;
}
}
else
{
lean_dec(v_a_370_);
return v_b_371_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___boxed(lean_object* v___x_382_, lean_object* v_value_383_, lean_object* v_a_384_, lean_object* v_b_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_382_, v_value_383_, v_a_384_, v_b_385_);
lean_dec_ref(v_value_383_);
lean_dec(v___x_382_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(lean_object* v_value_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_389_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0));
v___x_390_ = lean_string_utf8_byte_size(v_value_388_);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_390_, v_value_388_, v___x_391_, v___x_389_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___boxed(lean_object* v_value_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_393_);
lean_dec_ref(v_value_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v_value_397_, lean_object* v_inst_398_, lean_object* v_R_399_, lean_object* v_a_400_, lean_object* v_b_401_, lean_object* v_c_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_396_, v_value_397_, v_a_400_, v_b_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___boxed(lean_object* v___x_404_, lean_object* v___x_405_, lean_object* v_value_406_, lean_object* v_inst_407_, lean_object* v_R_408_, lean_object* v_a_409_, lean_object* v_b_410_, lean_object* v_c_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(v___x_404_, v___x_405_, v_value_406_, v_inst_407_, v_R_408_, v_a_409_, v_b_410_, v_c_411_);
lean_dec_ref(v_value_406_);
lean_dec(v___x_405_);
lean_dec_ref(v___x_404_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom(lean_object* v_src_413_, lean_object* v_value_414_, uint8_t v_canonical_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_416_ = l_Lean_Doc_versoTextKind;
v___x_417_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_414_);
v___x_418_ = l_Lean_SourceInfo_fromRef(v_src_413_, v_canonical_415_);
v___x_419_ = l_Lean_Syntax_mkLit(v___x_416_, v___x_417_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom___boxed(lean_object* v_src_420_, lean_object* v_value_421_, lean_object* v_canonical_422_){
_start:
{
uint8_t v_canonical_boxed_423_; lean_object* v_res_424_; 
v_canonical_boxed_423_ = lean_unbox(v_canonical_422_);
v_res_424_ = l_Lean_Doc_mkVersoTextFrom(v_src_420_, v_value_421_, v_canonical_boxed_423_);
lean_dec_ref(v_value_421_);
lean_dec(v_src_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom(lean_object* v_src_425_, lean_object* v_value_426_, uint8_t v_canonical_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = l_Lean_Doc_versoRefKind;
v___x_429_ = l_Lean_SourceInfo_fromRef(v_src_425_, v_canonical_427_);
v___x_430_ = l_Lean_Syntax_mkLit(v___x_428_, v_value_426_, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom___boxed(lean_object* v_src_431_, lean_object* v_value_432_, lean_object* v_canonical_433_){
_start:
{
uint8_t v_canonical_boxed_434_; lean_object* v_res_435_; 
v_canonical_boxed_434_ = lean_unbox(v_canonical_433_);
v_res_435_ = l_Lean_Doc_mkVersoRefNameFrom(v_src_431_, v_value_432_, v_canonical_boxed_434_);
lean_dec(v_src_431_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom(lean_object* v_src_436_, lean_object* v_value_437_, uint8_t v_canonical_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = l_Lean_Doc_versoLinkUrlKind;
v___x_440_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_437_);
v___x_441_ = l_Lean_SourceInfo_fromRef(v_src_436_, v_canonical_438_);
v___x_442_ = l_Lean_Syntax_mkLit(v___x_439_, v___x_440_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom___boxed(lean_object* v_src_443_, lean_object* v_value_444_, lean_object* v_canonical_445_){
_start:
{
uint8_t v_canonical_boxed_446_; lean_object* v_res_447_; 
v_canonical_boxed_446_ = lean_unbox(v_canonical_445_);
v_res_447_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_src_443_, v_value_444_, v_canonical_boxed_446_);
lean_dec_ref(v_value_444_);
lean_dec(v_src_443_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom(lean_object* v_src_448_, lean_object* v_value_449_, uint8_t v_canonical_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_451_ = l_Lean_Doc_versoImageAltKind;
v___x_452_ = l_Lean_Doc_escapeVersoImageAlt(v_value_449_);
v___x_453_ = l_Lean_SourceInfo_fromRef(v_src_448_, v_canonical_450_);
v___x_454_ = l_Lean_Syntax_mkLit(v___x_451_, v___x_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom___boxed(lean_object* v_src_455_, lean_object* v_value_456_, lean_object* v_canonical_457_){
_start:
{
uint8_t v_canonical_boxed_458_; lean_object* v_res_459_; 
v_canonical_boxed_458_ = lean_unbox(v_canonical_457_);
v_res_459_ = l_Lean_Doc_mkVersoImageAltFrom(v_src_455_, v_value_456_, v_canonical_boxed_458_);
lean_dec_ref(v_value_456_);
lean_dec(v_src_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom(lean_object* v_src_460_, lean_object* v_value_461_, uint8_t v_canonical_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = l_Lean_Doc_versoLinkRefUrlKind;
v___x_464_ = l_Lean_SourceInfo_fromRef(v_src_460_, v_canonical_462_);
v___x_465_ = l_Lean_Syntax_mkLit(v___x_463_, v_value_461_, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom___boxed(lean_object* v_src_466_, lean_object* v_value_467_, lean_object* v_canonical_468_){
_start:
{
uint8_t v_canonical_boxed_469_; lean_object* v_res_470_; 
v_canonical_boxed_469_ = lean_unbox(v_canonical_468_);
v_res_470_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_src_466_, v_value_467_, v_canonical_boxed_469_);
lean_dec(v_src_466_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(lean_object* v_info_471_, lean_object* v___x_472_, lean_object* v_value_473_, lean_object* v_a_474_, lean_object* v_b_475_){
_start:
{
uint8_t v_decide_476_; 
v_decide_476_ = lean_nat_dec_eq(v_a_474_, v___x_472_);
if (v_decide_476_ == 0)
{
lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_499_; 
v_fst_477_ = lean_ctor_get(v_b_475_, 0);
v_snd_478_ = lean_ctor_get(v_b_475_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_b_475_);
if (v_isSharedCheck_499_ == 0)
{
v___x_480_ = v_b_475_;
v_isShared_481_ = v_isSharedCheck_499_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snd_478_);
lean_inc(v_fst_477_);
lean_dec(v_b_475_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_499_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint32_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_482_ = lean_string_utf8_get_fast(v_value_473_, v_a_474_);
v___x_483_ = lean_string_utf8_next_fast(v_value_473_, v_a_474_);
lean_dec(v_a_474_);
v___x_484_ = lean_string_push(v_snd_478_, v___x_482_);
v___x_485_ = 10;
v___x_486_ = lean_uint32_dec_eq(v___x_482_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_488_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_484_);
v___x_488_ = v___x_480_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_fst_477_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v___x_484_);
v___x_488_ = v_reuseFailAlloc_490_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
v_a_474_ = v___x_483_;
v_b_475_ = v___x_488_;
goto _start;
}
}
else
{
lean_object* v_line_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v_line_491_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0));
v___x_492_ = l_Lean_Doc_versoCodeLineKind;
lean_inc(v_info_471_);
v___x_493_ = l_Lean_Syntax_mkLit(v___x_492_, v___x_484_, v_info_471_);
v___x_494_ = lean_array_push(v_fst_477_, v___x_493_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v_line_491_);
lean_ctor_set(v___x_480_, 0, v___x_494_);
v___x_496_ = v___x_480_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_line_491_);
v___x_496_ = v_reuseFailAlloc_498_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
v_a_474_ = v___x_483_;
v_b_475_ = v___x_496_;
goto _start;
}
}
}
}
else
{
lean_dec(v_a_474_);
lean_dec(v_info_471_);
return v_b_475_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg___boxed(lean_object* v_info_500_, lean_object* v___x_501_, lean_object* v_value_502_, lean_object* v_a_503_, lean_object* v_b_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_500_, v___x_501_, v_value_502_, v_a_503_, v_b_504_);
lean_dec_ref(v_value_502_);
lean_dec(v___x_501_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(lean_object* v_info_511_, lean_object* v_value_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v_fst_517_; lean_object* v_snd_518_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__1));
v___x_515_ = lean_string_utf8_byte_size(v_value_512_);
lean_inc(v_info_511_);
v___x_516_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_511_, v___x_515_, v_value_512_, v___x_513_, v___x_514_);
v_fst_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_fst_517_);
v_snd_518_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_snd_518_);
lean_dec_ref(v___x_516_);
v___x_523_ = lean_string_utf8_byte_size(v_snd_518_);
v___x_524_ = lean_nat_dec_eq(v___x_523_, v___x_513_);
if (v___x_524_ == 0)
{
goto v___jp_519_;
}
else
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_array_get_size(v_fst_517_);
v___x_526_ = lean_nat_dec_eq(v___x_525_, v___x_513_);
if (v___x_526_ == 0)
{
lean_dec(v_snd_518_);
lean_dec(v_info_511_);
return v_fst_517_;
}
else
{
goto v___jp_519_;
}
}
v___jp_519_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = l_Lean_Doc_versoCodeLineKind;
v___x_521_ = l_Lean_Syntax_mkLit(v___x_520_, v_snd_518_, v_info_511_);
v___x_522_ = lean_array_push(v_fst_517_, v___x_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___boxed(lean_object* v_info_527_, lean_object* v_value_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_527_, v_value_528_);
lean_dec_ref(v_value_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(lean_object* v_info_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v_value_533_, lean_object* v_inst_534_, lean_object* v_R_535_, lean_object* v_a_536_, lean_object* v_b_537_, lean_object* v_c_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_530_, v___x_532_, v_value_533_, v_a_536_, v_b_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___boxed(lean_object* v_info_540_, lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v_value_543_, lean_object* v_inst_544_, lean_object* v_R_545_, lean_object* v_a_546_, lean_object* v_b_547_, lean_object* v_c_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(v_info_540_, v___x_541_, v___x_542_, v_value_543_, v_inst_544_, v_R_545_, v_a_546_, v_b_547_, v_c_548_);
lean_dec_ref(v_value_543_);
lean_dec(v___x_542_);
lean_dec_ref(v___x_541_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom(lean_object* v_src_553_, lean_object* v_value_554_, uint8_t v_canonical_555_){
_start:
{
lean_object* v_info_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_info_556_ = l_Lean_SourceInfo_fromRef(v_src_553_, v_canonical_555_);
v___x_557_ = l_Lean_Doc_versoCodeKind;
lean_inc(v_info_556_);
v___x_558_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_556_, v_value_554_);
v___x_559_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_560_ = lean_box(2);
v___x_561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_559_);
lean_ctor_set(v___x_561_, 2, v___x_558_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_mk_empty_array_with_capacity(v___x_562_);
v___x_564_ = lean_array_push(v___x_563_, v___x_561_);
v___x_565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_565_, 0, v_info_556_);
lean_ctor_set(v___x_565_, 1, v___x_557_);
lean_ctor_set(v___x_565_, 2, v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom___boxed(lean_object* v_src_566_, lean_object* v_value_567_, lean_object* v_canonical_568_){
_start:
{
uint8_t v_canonical_boxed_569_; lean_object* v_res_570_; 
v_canonical_boxed_569_ = lean_unbox(v_canonical_568_);
v_res_570_ = l_Lean_Doc_mkVersoCodeFrom(v_src_566_, v_value_567_, v_canonical_boxed_569_);
lean_dec_ref(v_value_567_);
lean_dec(v_src_566_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom(lean_object* v_src_571_, lean_object* v_value_572_, uint8_t v_canonical_573_){
_start:
{
lean_object* v_info_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_info_574_ = l_Lean_SourceInfo_fromRef(v_src_571_, v_canonical_573_);
v___x_575_ = l_Lean_Doc_versoCodeBlockKind;
lean_inc(v_info_574_);
v___x_576_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_574_, v_value_572_);
v___x_577_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_578_ = lean_box(2);
v___x_579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
lean_ctor_set(v___x_579_, 2, v___x_576_);
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_mk_empty_array_with_capacity(v___x_580_);
v___x_582_ = lean_array_push(v___x_581_, v___x_579_);
v___x_583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_583_, 0, v_info_574_);
lean_ctor_set(v___x_583_, 1, v___x_575_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___boxed(lean_object* v_src_584_, lean_object* v_value_585_, lean_object* v_canonical_586_){
_start:
{
uint8_t v_canonical_boxed_587_; lean_object* v_res_588_; 
v_canonical_boxed_587_ = lean_unbox(v_canonical_586_);
v_res_588_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_src_584_, v_value_585_, v_canonical_boxed_587_);
lean_dec_ref(v_value_585_);
lean_dec(v_src_584_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom(lean_object* v_src_598_, uint8_t v_canonical_599_){
_start:
{
lean_object* v_info_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_info_600_ = l_Lean_SourceInfo_fromRef(v_src_598_, v_canonical_599_);
v___x_601_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
v___x_602_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__3));
lean_inc(v_info_600_);
v___x_603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_603_, 0, v_info_600_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
v___x_606_ = lean_array_push(v___x_605_, v___x_603_);
v___x_607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_607_, 0, v_info_600_);
lean_ctor_set(v___x_607_, 1, v___x_601_);
lean_ctor_set(v___x_607_, 2, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom___boxed(lean_object* v_src_608_, lean_object* v_canonical_609_){
_start:
{
uint8_t v_canonical_boxed_610_; lean_object* v_res_611_; 
v_canonical_boxed_610_ = lean_unbox(v_canonical_609_);
v_res_611_ = l_Lean_Doc_mkVersoLinebreakFrom(v_src_608_, v_canonical_boxed_610_);
lean_dec(v_src_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(uint8_t v_canonical_612_, lean_object* v_toPure_613_, lean_object* v_____do__lift_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = l_Lean_Doc_mkVersoLinebreakFrom(v_____do__lift_614_, v_canonical_612_);
v___x_616_ = lean_apply_2(v_toPure_613_, lean_box(0), v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed(lean_object* v_canonical_617_, lean_object* v_toPure_618_, lean_object* v_____do__lift_619_){
_start:
{
uint8_t v_canonical_boxed_620_; lean_object* v_res_621_; 
v_canonical_boxed_620_ = lean_unbox(v_canonical_617_);
v_res_621_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(v_canonical_boxed_620_, v_toPure_618_, v_____do__lift_619_);
lean_dec(v_____do__lift_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg(lean_object* v_inst_622_, lean_object* v_inst_623_, uint8_t v_canonical_624_){
_start:
{
lean_object* v_toApplicative_625_; lean_object* v_toBind_626_; lean_object* v_getRef_627_; lean_object* v_toPure_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; 
v_toApplicative_625_ = lean_ctor_get(v_inst_622_, 0);
lean_inc_ref(v_toApplicative_625_);
v_toBind_626_ = lean_ctor_get(v_inst_622_, 1);
lean_inc(v_toBind_626_);
lean_dec_ref(v_inst_622_);
v_getRef_627_ = lean_ctor_get(v_inst_623_, 0);
lean_inc(v_getRef_627_);
lean_dec_ref(v_inst_623_);
v_toPure_628_ = lean_ctor_get(v_toApplicative_625_, 1);
lean_inc(v_toPure_628_);
lean_dec_ref(v_toApplicative_625_);
v___x_629_ = lean_box(v_canonical_624_);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_630_, 0, v___x_629_);
lean_closure_set(v___f_630_, 1, v_toPure_628_);
v___x_631_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v_getRef_627_, v___f_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___boxed(lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_canonical_634_){
_start:
{
uint8_t v_canonical_boxed_635_; lean_object* v_res_636_; 
v_canonical_boxed_635_ = lean_unbox(v_canonical_634_);
v_res_636_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_632_, v_inst_633_, v_canonical_boxed_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef(lean_object* v_m_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, uint8_t v_canonical_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_638_, v_inst_639_, v_canonical_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___boxed(lean_object* v_m_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_canonical_645_){
_start:
{
uint8_t v_canonical_boxed_646_; lean_object* v_res_647_; 
v_canonical_boxed_646_ = lean_unbox(v_canonical_645_);
v_res_647_ = l_Lean_Doc_mkVersoLinebreakFromRef(v_m_642_, v_inst_643_, v_inst_644_, v_canonical_boxed_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(lean_object* v_value_648_, uint8_t v_canonical_649_, lean_object* v_toPure_650_, lean_object* v_____do__lift_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = l_Lean_Doc_mkVersoTextFrom(v_____do__lift_651_, v_value_648_, v_canonical_649_);
v___x_653_ = lean_apply_2(v_toPure_650_, lean_box(0), v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed(lean_object* v_value_654_, lean_object* v_canonical_655_, lean_object* v_toPure_656_, lean_object* v_____do__lift_657_){
_start:
{
uint8_t v_canonical_boxed_658_; lean_object* v_res_659_; 
v_canonical_boxed_658_ = lean_unbox(v_canonical_655_);
v_res_659_ = l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(v_value_654_, v_canonical_boxed_658_, v_toPure_656_, v_____do__lift_657_);
lean_dec(v_____do__lift_657_);
lean_dec_ref(v_value_654_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg(lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_value_662_, uint8_t v_canonical_663_){
_start:
{
lean_object* v_toApplicative_664_; lean_object* v_toBind_665_; lean_object* v_getRef_666_; lean_object* v_toPure_667_; lean_object* v___x_668_; lean_object* v___f_669_; lean_object* v___x_670_; 
v_toApplicative_664_ = lean_ctor_get(v_inst_660_, 0);
lean_inc_ref(v_toApplicative_664_);
v_toBind_665_ = lean_ctor_get(v_inst_660_, 1);
lean_inc(v_toBind_665_);
lean_dec_ref(v_inst_660_);
v_getRef_666_ = lean_ctor_get(v_inst_661_, 0);
lean_inc(v_getRef_666_);
lean_dec_ref(v_inst_661_);
v_toPure_667_ = lean_ctor_get(v_toApplicative_664_, 1);
lean_inc(v_toPure_667_);
lean_dec_ref(v_toApplicative_664_);
v___x_668_ = lean_box(v_canonical_663_);
v___f_669_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_669_, 0, v_value_662_);
lean_closure_set(v___f_669_, 1, v___x_668_);
lean_closure_set(v___f_669_, 2, v_toPure_667_);
v___x_670_ = lean_apply_4(v_toBind_665_, lean_box(0), lean_box(0), v_getRef_666_, v___f_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___boxed(lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_value_673_, lean_object* v_canonical_674_){
_start:
{
uint8_t v_canonical_boxed_675_; lean_object* v_res_676_; 
v_canonical_boxed_675_ = lean_unbox(v_canonical_674_);
v_res_676_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_671_, v_inst_672_, v_value_673_, v_canonical_boxed_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef(lean_object* v_m_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_value_680_, uint8_t v_canonical_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_678_, v_inst_679_, v_value_680_, v_canonical_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___boxed(lean_object* v_m_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_value_686_, lean_object* v_canonical_687_){
_start:
{
uint8_t v_canonical_boxed_688_; lean_object* v_res_689_; 
v_canonical_boxed_688_ = lean_unbox(v_canonical_687_);
v_res_689_ = l_Lean_Doc_mkVersoTextFromRef(v_m_683_, v_inst_684_, v_inst_685_, v_value_686_, v_canonical_boxed_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(lean_object* v_value_690_, uint8_t v_canonical_691_, lean_object* v_toPure_692_, lean_object* v_____do__lift_693_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = l_Lean_Doc_mkVersoRefNameFrom(v_____do__lift_693_, v_value_690_, v_canonical_691_);
v___x_695_ = lean_apply_2(v_toPure_692_, lean_box(0), v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed(lean_object* v_value_696_, lean_object* v_canonical_697_, lean_object* v_toPure_698_, lean_object* v_____do__lift_699_){
_start:
{
uint8_t v_canonical_boxed_700_; lean_object* v_res_701_; 
v_canonical_boxed_700_ = lean_unbox(v_canonical_697_);
v_res_701_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(v_value_696_, v_canonical_boxed_700_, v_toPure_698_, v_____do__lift_699_);
lean_dec(v_____do__lift_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg(lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_value_704_, uint8_t v_canonical_705_){
_start:
{
lean_object* v_toApplicative_706_; lean_object* v_toBind_707_; lean_object* v_getRef_708_; lean_object* v_toPure_709_; lean_object* v___x_710_; lean_object* v___f_711_; lean_object* v___x_712_; 
v_toApplicative_706_ = lean_ctor_get(v_inst_702_, 0);
lean_inc_ref(v_toApplicative_706_);
v_toBind_707_ = lean_ctor_get(v_inst_702_, 1);
lean_inc(v_toBind_707_);
lean_dec_ref(v_inst_702_);
v_getRef_708_ = lean_ctor_get(v_inst_703_, 0);
lean_inc(v_getRef_708_);
lean_dec_ref(v_inst_703_);
v_toPure_709_ = lean_ctor_get(v_toApplicative_706_, 1);
lean_inc(v_toPure_709_);
lean_dec_ref(v_toApplicative_706_);
v___x_710_ = lean_box(v_canonical_705_);
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_711_, 0, v_value_704_);
lean_closure_set(v___f_711_, 1, v___x_710_);
lean_closure_set(v___f_711_, 2, v_toPure_709_);
v___x_712_ = lean_apply_4(v_toBind_707_, lean_box(0), lean_box(0), v_getRef_708_, v___f_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___boxed(lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_value_715_, lean_object* v_canonical_716_){
_start:
{
uint8_t v_canonical_boxed_717_; lean_object* v_res_718_; 
v_canonical_boxed_717_ = lean_unbox(v_canonical_716_);
v_res_718_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_713_, v_inst_714_, v_value_715_, v_canonical_boxed_717_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef(lean_object* v_m_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_value_722_, uint8_t v_canonical_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_720_, v_inst_721_, v_value_722_, v_canonical_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___boxed(lean_object* v_m_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_value_728_, lean_object* v_canonical_729_){
_start:
{
uint8_t v_canonical_boxed_730_; lean_object* v_res_731_; 
v_canonical_boxed_730_ = lean_unbox(v_canonical_729_);
v_res_731_ = l_Lean_Doc_mkVersoRefNameFromRef(v_m_725_, v_inst_726_, v_inst_727_, v_value_728_, v_canonical_boxed_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(lean_object* v_value_732_, uint8_t v_canonical_733_, lean_object* v_toPure_734_, lean_object* v_____do__lift_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_____do__lift_735_, v_value_732_, v_canonical_733_);
v___x_737_ = lean_apply_2(v_toPure_734_, lean_box(0), v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_738_, lean_object* v_canonical_739_, lean_object* v_toPure_740_, lean_object* v_____do__lift_741_){
_start:
{
uint8_t v_canonical_boxed_742_; lean_object* v_res_743_; 
v_canonical_boxed_742_ = lean_unbox(v_canonical_739_);
v_res_743_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(v_value_738_, v_canonical_boxed_742_, v_toPure_740_, v_____do__lift_741_);
lean_dec(v_____do__lift_741_);
lean_dec_ref(v_value_738_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_value_746_, uint8_t v_canonical_747_){
_start:
{
lean_object* v_toApplicative_748_; lean_object* v_toBind_749_; lean_object* v_getRef_750_; lean_object* v_toPure_751_; lean_object* v___x_752_; lean_object* v___f_753_; lean_object* v___x_754_; 
v_toApplicative_748_ = lean_ctor_get(v_inst_744_, 0);
lean_inc_ref(v_toApplicative_748_);
v_toBind_749_ = lean_ctor_get(v_inst_744_, 1);
lean_inc(v_toBind_749_);
lean_dec_ref(v_inst_744_);
v_getRef_750_ = lean_ctor_get(v_inst_745_, 0);
lean_inc(v_getRef_750_);
lean_dec_ref(v_inst_745_);
v_toPure_751_ = lean_ctor_get(v_toApplicative_748_, 1);
lean_inc(v_toPure_751_);
lean_dec_ref(v_toApplicative_748_);
v___x_752_ = lean_box(v_canonical_747_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_753_, 0, v_value_746_);
lean_closure_set(v___f_753_, 1, v___x_752_);
lean_closure_set(v___f_753_, 2, v_toPure_751_);
v___x_754_ = lean_apply_4(v_toBind_749_, lean_box(0), lean_box(0), v_getRef_750_, v___f_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___boxed(lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_value_757_, lean_object* v_canonical_758_){
_start:
{
uint8_t v_canonical_boxed_759_; lean_object* v_res_760_; 
v_canonical_boxed_759_ = lean_unbox(v_canonical_758_);
v_res_760_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_755_, v_inst_756_, v_value_757_, v_canonical_boxed_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef(lean_object* v_m_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_value_764_, uint8_t v_canonical_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_762_, v_inst_763_, v_value_764_, v_canonical_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___boxed(lean_object* v_m_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_value_770_, lean_object* v_canonical_771_){
_start:
{
uint8_t v_canonical_boxed_772_; lean_object* v_res_773_; 
v_canonical_boxed_772_ = lean_unbox(v_canonical_771_);
v_res_773_ = l_Lean_Doc_mkVersoLinkUrlFromRef(v_m_767_, v_inst_768_, v_inst_769_, v_value_770_, v_canonical_boxed_772_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(lean_object* v_value_774_, uint8_t v_canonical_775_, lean_object* v_toPure_776_, lean_object* v_____do__lift_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = l_Lean_Doc_mkVersoImageAltFrom(v_____do__lift_777_, v_value_774_, v_canonical_775_);
v___x_779_ = lean_apply_2(v_toPure_776_, lean_box(0), v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed(lean_object* v_value_780_, lean_object* v_canonical_781_, lean_object* v_toPure_782_, lean_object* v_____do__lift_783_){
_start:
{
uint8_t v_canonical_boxed_784_; lean_object* v_res_785_; 
v_canonical_boxed_784_ = lean_unbox(v_canonical_781_);
v_res_785_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(v_value_780_, v_canonical_boxed_784_, v_toPure_782_, v_____do__lift_783_);
lean_dec(v_____do__lift_783_);
lean_dec_ref(v_value_780_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg(lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_value_788_, uint8_t v_canonical_789_){
_start:
{
lean_object* v_toApplicative_790_; lean_object* v_toBind_791_; lean_object* v_getRef_792_; lean_object* v_toPure_793_; lean_object* v___x_794_; lean_object* v___f_795_; lean_object* v___x_796_; 
v_toApplicative_790_ = lean_ctor_get(v_inst_786_, 0);
lean_inc_ref(v_toApplicative_790_);
v_toBind_791_ = lean_ctor_get(v_inst_786_, 1);
lean_inc(v_toBind_791_);
lean_dec_ref(v_inst_786_);
v_getRef_792_ = lean_ctor_get(v_inst_787_, 0);
lean_inc(v_getRef_792_);
lean_dec_ref(v_inst_787_);
v_toPure_793_ = lean_ctor_get(v_toApplicative_790_, 1);
lean_inc(v_toPure_793_);
lean_dec_ref(v_toApplicative_790_);
v___x_794_ = lean_box(v_canonical_789_);
v___f_795_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_795_, 0, v_value_788_);
lean_closure_set(v___f_795_, 1, v___x_794_);
lean_closure_set(v___f_795_, 2, v_toPure_793_);
v___x_796_ = lean_apply_4(v_toBind_791_, lean_box(0), lean_box(0), v_getRef_792_, v___f_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___boxed(lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_value_799_, lean_object* v_canonical_800_){
_start:
{
uint8_t v_canonical_boxed_801_; lean_object* v_res_802_; 
v_canonical_boxed_801_ = lean_unbox(v_canonical_800_);
v_res_802_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_797_, v_inst_798_, v_value_799_, v_canonical_boxed_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef(lean_object* v_m_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_value_806_, uint8_t v_canonical_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_804_, v_inst_805_, v_value_806_, v_canonical_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___boxed(lean_object* v_m_809_, lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_value_812_, lean_object* v_canonical_813_){
_start:
{
uint8_t v_canonical_boxed_814_; lean_object* v_res_815_; 
v_canonical_boxed_814_ = lean_unbox(v_canonical_813_);
v_res_815_ = l_Lean_Doc_mkVersoImageAltFromRef(v_m_809_, v_inst_810_, v_inst_811_, v_value_812_, v_canonical_boxed_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(lean_object* v_value_816_, uint8_t v_canonical_817_, lean_object* v_toPure_818_, lean_object* v_____do__lift_819_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_____do__lift_819_, v_value_816_, v_canonical_817_);
v___x_821_ = lean_apply_2(v_toPure_818_, lean_box(0), v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_822_, lean_object* v_canonical_823_, lean_object* v_toPure_824_, lean_object* v_____do__lift_825_){
_start:
{
uint8_t v_canonical_boxed_826_; lean_object* v_res_827_; 
v_canonical_boxed_826_ = lean_unbox(v_canonical_823_);
v_res_827_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(v_value_822_, v_canonical_boxed_826_, v_toPure_824_, v_____do__lift_825_);
lean_dec(v_____do__lift_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_value_830_, uint8_t v_canonical_831_){
_start:
{
lean_object* v_toApplicative_832_; lean_object* v_toBind_833_; lean_object* v_getRef_834_; lean_object* v_toPure_835_; lean_object* v___x_836_; lean_object* v___f_837_; lean_object* v___x_838_; 
v_toApplicative_832_ = lean_ctor_get(v_inst_828_, 0);
lean_inc_ref(v_toApplicative_832_);
v_toBind_833_ = lean_ctor_get(v_inst_828_, 1);
lean_inc(v_toBind_833_);
lean_dec_ref(v_inst_828_);
v_getRef_834_ = lean_ctor_get(v_inst_829_, 0);
lean_inc(v_getRef_834_);
lean_dec_ref(v_inst_829_);
v_toPure_835_ = lean_ctor_get(v_toApplicative_832_, 1);
lean_inc(v_toPure_835_);
lean_dec_ref(v_toApplicative_832_);
v___x_836_ = lean_box(v_canonical_831_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_837_, 0, v_value_830_);
lean_closure_set(v___f_837_, 1, v___x_836_);
lean_closure_set(v___f_837_, 2, v_toPure_835_);
v___x_838_ = lean_apply_4(v_toBind_833_, lean_box(0), lean_box(0), v_getRef_834_, v___f_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___boxed(lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_value_841_, lean_object* v_canonical_842_){
_start:
{
uint8_t v_canonical_boxed_843_; lean_object* v_res_844_; 
v_canonical_boxed_843_ = lean_unbox(v_canonical_842_);
v_res_844_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_839_, v_inst_840_, v_value_841_, v_canonical_boxed_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef(lean_object* v_m_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_value_848_, uint8_t v_canonical_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_846_, v_inst_847_, v_value_848_, v_canonical_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___boxed(lean_object* v_m_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_value_854_, lean_object* v_canonical_855_){
_start:
{
uint8_t v_canonical_boxed_856_; lean_object* v_res_857_; 
v_canonical_boxed_856_ = lean_unbox(v_canonical_855_);
v_res_857_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef(v_m_851_, v_inst_852_, v_inst_853_, v_value_854_, v_canonical_boxed_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(lean_object* v_value_858_, uint8_t v_canonical_859_, lean_object* v_toPure_860_, lean_object* v_____do__lift_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = l_Lean_Doc_mkVersoCodeFrom(v_____do__lift_861_, v_value_858_, v_canonical_859_);
v___x_863_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed(lean_object* v_value_864_, lean_object* v_canonical_865_, lean_object* v_toPure_866_, lean_object* v_____do__lift_867_){
_start:
{
uint8_t v_canonical_boxed_868_; lean_object* v_res_869_; 
v_canonical_boxed_868_ = lean_unbox(v_canonical_865_);
v_res_869_ = l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(v_value_864_, v_canonical_boxed_868_, v_toPure_866_, v_____do__lift_867_);
lean_dec(v_____do__lift_867_);
lean_dec_ref(v_value_864_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg(lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_value_872_, uint8_t v_canonical_873_){
_start:
{
lean_object* v_toApplicative_874_; lean_object* v_toBind_875_; lean_object* v_getRef_876_; lean_object* v_toPure_877_; lean_object* v___x_878_; lean_object* v___f_879_; lean_object* v___x_880_; 
v_toApplicative_874_ = lean_ctor_get(v_inst_870_, 0);
lean_inc_ref(v_toApplicative_874_);
v_toBind_875_ = lean_ctor_get(v_inst_870_, 1);
lean_inc(v_toBind_875_);
lean_dec_ref(v_inst_870_);
v_getRef_876_ = lean_ctor_get(v_inst_871_, 0);
lean_inc(v_getRef_876_);
lean_dec_ref(v_inst_871_);
v_toPure_877_ = lean_ctor_get(v_toApplicative_874_, 1);
lean_inc(v_toPure_877_);
lean_dec_ref(v_toApplicative_874_);
v___x_878_ = lean_box(v_canonical_873_);
v___f_879_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_879_, 0, v_value_872_);
lean_closure_set(v___f_879_, 1, v___x_878_);
lean_closure_set(v___f_879_, 2, v_toPure_877_);
v___x_880_ = lean_apply_4(v_toBind_875_, lean_box(0), lean_box(0), v_getRef_876_, v___f_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___boxed(lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_value_883_, lean_object* v_canonical_884_){
_start:
{
uint8_t v_canonical_boxed_885_; lean_object* v_res_886_; 
v_canonical_boxed_885_ = lean_unbox(v_canonical_884_);
v_res_886_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_881_, v_inst_882_, v_value_883_, v_canonical_boxed_885_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef(lean_object* v_m_887_, lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_value_890_, uint8_t v_canonical_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_888_, v_inst_889_, v_value_890_, v_canonical_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___boxed(lean_object* v_m_893_, lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_value_896_, lean_object* v_canonical_897_){
_start:
{
uint8_t v_canonical_boxed_898_; lean_object* v_res_899_; 
v_canonical_boxed_898_ = lean_unbox(v_canonical_897_);
v_res_899_ = l_Lean_Doc_mkVersoCodeFromRef(v_m_893_, v_inst_894_, v_inst_895_, v_value_896_, v_canonical_boxed_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(lean_object* v_value_900_, uint8_t v_canonical_901_, lean_object* v_toPure_902_, lean_object* v_____do__lift_903_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_____do__lift_903_, v_value_900_, v_canonical_901_);
v___x_905_ = lean_apply_2(v_toPure_902_, lean_box(0), v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed(lean_object* v_value_906_, lean_object* v_canonical_907_, lean_object* v_toPure_908_, lean_object* v_____do__lift_909_){
_start:
{
uint8_t v_canonical_boxed_910_; lean_object* v_res_911_; 
v_canonical_boxed_910_ = lean_unbox(v_canonical_907_);
v_res_911_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(v_value_906_, v_canonical_boxed_910_, v_toPure_908_, v_____do__lift_909_);
lean_dec(v_____do__lift_909_);
lean_dec_ref(v_value_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_value_914_, uint8_t v_canonical_915_){
_start:
{
lean_object* v_toApplicative_916_; lean_object* v_toBind_917_; lean_object* v_getRef_918_; lean_object* v_toPure_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; 
v_toApplicative_916_ = lean_ctor_get(v_inst_912_, 0);
lean_inc_ref(v_toApplicative_916_);
v_toBind_917_ = lean_ctor_get(v_inst_912_, 1);
lean_inc(v_toBind_917_);
lean_dec_ref(v_inst_912_);
v_getRef_918_ = lean_ctor_get(v_inst_913_, 0);
lean_inc(v_getRef_918_);
lean_dec_ref(v_inst_913_);
v_toPure_919_ = lean_ctor_get(v_toApplicative_916_, 1);
lean_inc(v_toPure_919_);
lean_dec_ref(v_toApplicative_916_);
v___x_920_ = lean_box(v_canonical_915_);
v___f_921_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_921_, 0, v_value_914_);
lean_closure_set(v___f_921_, 1, v___x_920_);
lean_closure_set(v___f_921_, 2, v_toPure_919_);
v___x_922_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v_getRef_918_, v___f_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___boxed(lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_value_925_, lean_object* v_canonical_926_){
_start:
{
uint8_t v_canonical_boxed_927_; lean_object* v_res_928_; 
v_canonical_boxed_927_ = lean_unbox(v_canonical_926_);
v_res_928_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_923_, v_inst_924_, v_value_925_, v_canonical_boxed_927_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef(lean_object* v_m_929_, lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_value_932_, uint8_t v_canonical_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_930_, v_inst_931_, v_value_932_, v_canonical_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___boxed(lean_object* v_m_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_value_938_, lean_object* v_canonical_939_){
_start:
{
uint8_t v_canonical_boxed_940_; lean_object* v_res_941_; 
v_canonical_boxed_940_ = lean_unbox(v_canonical_939_);
v_res_941_ = l_Lean_Doc_mkVersoCodeBlockFromRef(v_m_935_, v_inst_936_, v_inst_937_, v_value_938_, v_canonical_boxed_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_of(lean_object* v_stx_969_){
_start:
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__2));
lean_inc(v_stx_969_);
v___x_971_ = l_Lean_Syntax_isOfKind(v_stx_969_, v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__4));
lean_inc(v_stx_969_);
v___x_973_ = l_Lean_Syntax_isOfKind(v_stx_969_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec(v_stx_969_);
v___x_974_ = lean_box(0);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v_o_976_; lean_object* v___x_977_; lean_object* v_name_978_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v_o_976_ = l_Lean_Syntax_getArg(v_stx_969_, v___x_975_);
v___x_977_ = lean_unsigned_to_nat(1u);
v_name_978_ = l_Lean_Syntax_getArg(v_stx_969_, v___x_977_);
if (v___x_971_ == 0)
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_978_);
v___x_985_ = l_Lean_Syntax_isOfKind(v_name_978_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
lean_dec(v_name_978_);
lean_dec(v_o_976_);
lean_dec(v_stx_969_);
v___x_986_ = lean_box(0);
return v___x_986_;
}
else
{
goto v___jp_979_;
}
}
else
{
goto v___jp_979_;
}
v___jp_979_:
{
lean_object* v___x_980_; lean_object* v_c_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_980_ = lean_unsigned_to_nat(2u);
v_c_981_ = l_Lean_Syntax_getArg(v_stx_969_, v___x_980_);
v___x_982_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_982_, 0, v_stx_969_);
lean_ctor_set(v___x_982_, 1, v_o_976_);
lean_ctor_set(v___x_982_, 2, v_name_978_);
lean_ctor_set(v___x_982_, 3, v_c_981_);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
}
else
{
lean_object* v___x_987_; lean_object* v_url_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_987_ = lean_unsigned_to_nat(1u);
v_url_988_ = l_Lean_Syntax_getArg(v_stx_969_, v___x_987_);
v___x_989_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__8));
lean_inc(v_url_988_);
v___x_990_ = l_Lean_Syntax_isOfKind(v_url_988_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
lean_dec(v_url_988_);
lean_dec(v_stx_969_);
v___x_991_ = lean_box(0);
return v___x_991_;
}
else
{
lean_object* v___x_992_; lean_object* v_o_993_; lean_object* v___x_994_; lean_object* v_c_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_992_ = lean_unsigned_to_nat(0u);
v_o_993_ = l_Lean_Syntax_getArg(v_stx_969_, v___x_992_);
v___x_994_ = lean_unsigned_to_nat(2u);
v_c_995_ = l_Lean_Syntax_getArg(v_stx_969_, v___x_994_);
v___x_996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_996_, 0, v_stx_969_);
lean_ctor_set(v___x_996_, 1, v_o_993_);
lean_ctor_set(v___x_996_, 2, v_url_988_);
lean_ctor_set(v___x_996_, 3, v_c_995_);
v___x_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText(lean_object* v_v_1002_){
_start:
{
lean_object* v_content_1003_; lean_object* v___x_1004_; 
v_content_1003_ = lean_ctor_get(v_v_1002_, 1);
v___x_1004_ = l_Lean_TSyntax_getVersoText(v_content_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText___boxed(lean_object* v_v_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Doc_TextView_getVersoText(v_v_1005_);
lean_dec_ref(v_v_1005_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object* v_v_1007_){
_start:
{
lean_object* v_content_1008_; lean_object* v___x_1009_; 
v_content_1008_ = lean_ctor_get(v_v_1007_, 1);
v___x_1009_ = l_Lean_TSyntax_getVersoTextSource(v_content_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource___boxed(lean_object* v_v_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Doc_TextView_getVersoTextSource(v_v_1010_);
lean_dec_ref(v_v_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_of(lean_object* v_stx_1025_){
_start:
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__1));
lean_inc(v_stx_1025_);
v___x_1027_ = l_Lean_Syntax_isOfKind(v_stx_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
lean_dec(v_stx_1025_);
v___x_1028_ = lean_box(0);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; lean_object* v_s_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1029_ = lean_unsigned_to_nat(0u);
v_s_1030_ = l_Lean_Syntax_getArg(v_stx_1025_, v___x_1029_);
v___x_1031_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__3));
lean_inc(v_s_1030_);
v___x_1032_ = l_Lean_Syntax_isOfKind(v_s_1030_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_dec(v_s_1030_);
lean_dec(v_stx_1025_);
v___x_1033_ = lean_box(0);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_stx_1025_);
lean_ctor_set(v___x_1034_, 1, v_s_1030_);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_EmphView_of(lean_object* v_stx_1049_){
_start:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_Doc_EmphView_of___closed__1));
lean_inc(v_stx_1049_);
v___x_1051_ = l_Lean_Syntax_isOfKind(v_stx_1049_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; 
lean_dec(v_stx_1049_);
v___x_1052_ = lean_box(0);
return v___x_1052_;
}
else
{
lean_object* v___x_1053_; lean_object* v_o_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1053_ = lean_unsigned_to_nat(0u);
v_o_1054_ = l_Lean_Syntax_getArg(v_stx_1049_, v___x_1053_);
v___x_1055_ = ((lean_object*)(l_Lean_Doc_EmphView_of___closed__3));
lean_inc(v_o_1054_);
v___x_1056_ = l_Lean_Syntax_isOfKind(v_o_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_dec(v_o_1054_);
lean_dec(v_stx_1049_);
v___x_1057_ = lean_box(0);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v_c_1059_; uint8_t v___x_1060_; 
v___x_1058_ = lean_unsigned_to_nat(2u);
v_c_1059_ = l_Lean_Syntax_getArg(v_stx_1049_, v___x_1058_);
lean_inc(v_c_1059_);
v___x_1060_ = l_Lean_Syntax_isOfKind(v_c_1059_, v___x_1055_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_dec(v_c_1059_);
lean_dec(v_o_1054_);
lean_dec(v_stx_1049_);
v___x_1061_ = lean_box(0);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_inl_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = l_Lean_Syntax_getArg(v_stx_1049_, v___x_1062_);
v_inl_1064_ = l_Lean_Syntax_getArgs(v___x_1063_);
lean_dec(v___x_1063_);
v___x_1065_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1065_, 0, v_stx_1049_);
lean_ctor_set(v___x_1065_, 1, v_o_1054_);
lean_ctor_set(v___x_1065_, 2, v_inl_1064_);
lean_ctor_set(v___x_1065_, 3, v_c_1059_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BoldView_of(lean_object* v_stx_1080_){
_start:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_Doc_BoldView_of___closed__1));
lean_inc(v_stx_1080_);
v___x_1082_ = l_Lean_Syntax_isOfKind(v_stx_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
lean_dec(v_stx_1080_);
v___x_1083_ = lean_box(0);
return v___x_1083_;
}
else
{
lean_object* v___x_1084_; lean_object* v_o_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1084_ = lean_unsigned_to_nat(0u);
v_o_1085_ = l_Lean_Syntax_getArg(v_stx_1080_, v___x_1084_);
v___x_1086_ = ((lean_object*)(l_Lean_Doc_BoldView_of___closed__3));
lean_inc(v_o_1085_);
v___x_1087_ = l_Lean_Syntax_isOfKind(v_o_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_dec(v_o_1085_);
lean_dec(v_stx_1080_);
v___x_1088_ = lean_box(0);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; lean_object* v_c_1090_; uint8_t v___x_1091_; 
v___x_1089_ = lean_unsigned_to_nat(2u);
v_c_1090_ = l_Lean_Syntax_getArg(v_stx_1080_, v___x_1089_);
lean_inc(v_c_1090_);
v___x_1091_ = l_Lean_Syntax_isOfKind(v_c_1090_, v___x_1086_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
lean_dec(v_c_1090_);
lean_dec(v_o_1085_);
lean_dec(v_stx_1080_);
v___x_1092_ = lean_box(0);
return v___x_1092_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_inl_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = l_Lean_Syntax_getArg(v_stx_1080_, v___x_1093_);
v_inl_1095_ = l_Lean_Syntax_getArgs(v___x_1094_);
lean_dec(v___x_1094_);
v___x_1096_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1096_, 0, v_stx_1080_);
lean_ctor_set(v___x_1096_, 1, v_o_1085_);
lean_ctor_set(v___x_1096_, 2, v_inl_1095_);
lean_ctor_set(v___x_1096_, 3, v_c_1090_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object* v_v_1098_){
_start:
{
lean_object* v_content_1099_; lean_object* v___x_1100_; 
v_content_1099_ = lean_ctor_get(v_v_1098_, 2);
v___x_1100_ = l_Lean_TSyntax_getVersoCode(v_content_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode___boxed(lean_object* v_v_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_Doc_CodeView_getVersoCode(v_v_1101_);
lean_dec_ref(v_v_1101_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_of(lean_object* v_stx_1122_){
_start:
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v_stx_1122_);
v___x_1124_ = l_Lean_Syntax_isOfKind(v_stx_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec(v_stx_1122_);
v___x_1125_ = lean_box(0);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; lean_object* v_o_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1126_ = lean_unsigned_to_nat(0u);
v_o_1127_ = l_Lean_Syntax_getArg(v_stx_1122_, v___x_1126_);
v___x_1128_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__3));
lean_inc(v_o_1127_);
v___x_1129_ = l_Lean_Syntax_isOfKind(v_o_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
lean_dec(v_o_1127_);
lean_dec(v_stx_1122_);
v___x_1130_ = lean_box(0);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; lean_object* v_s_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1131_ = lean_unsigned_to_nat(1u);
v_s_1132_ = l_Lean_Syntax_getArg(v_stx_1122_, v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__5));
lean_inc(v_s_1132_);
v___x_1134_ = l_Lean_Syntax_isOfKind(v_s_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec(v_s_1132_);
lean_dec(v_o_1127_);
lean_dec(v_stx_1122_);
v___x_1135_ = lean_box(0);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; lean_object* v_c_1137_; uint8_t v___x_1138_; 
v___x_1136_ = lean_unsigned_to_nat(2u);
v_c_1137_ = l_Lean_Syntax_getArg(v_stx_1122_, v___x_1136_);
lean_inc(v_c_1137_);
v___x_1138_ = l_Lean_Syntax_isOfKind(v_c_1137_, v___x_1128_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_dec(v_c_1137_);
lean_dec(v_s_1132_);
lean_dec(v_o_1127_);
lean_dec(v_stx_1122_);
v___x_1139_ = lean_box(0);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1140_, 0, v_stx_1122_);
lean_ctor_set(v___x_1140_, 1, v_o_1127_);
lean_ctor_set(v___x_1140_, 2, v_s_1132_);
lean_ctor_set(v___x_1140_, 3, v_c_1137_);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object* v_v_1142_){
_start:
{
lean_object* v_code_1143_; lean_object* v___x_1144_; 
v_code_1143_ = lean_ctor_get(v_v_1142_, 2);
v___x_1144_ = l_Lean_Doc_CodeView_getVersoCode(v_code_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode___boxed(lean_object* v_v_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Doc_MathView_getVersoCode(v_v_1145_);
lean_dec_ref(v_v_1145_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_of(lean_object* v_stx_1173_){
_start:
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__1));
lean_inc(v_stx_1173_);
v___x_1175_ = l_Lean_Syntax_isOfKind(v_stx_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__3));
lean_inc(v_stx_1173_);
v___x_1177_ = l_Lean_Syntax_isOfKind(v_stx_1173_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; 
lean_dec(v_stx_1173_);
v___x_1178_ = lean_box(0);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___y_1182_; 
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = l_Lean_Syntax_getArg(v_stx_1173_, v___x_1179_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__5));
lean_inc(v___x_1180_);
v___x_1202_ = l_Lean_Syntax_isOfKind(v___x_1180_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; 
lean_dec(v___x_1180_);
lean_dec(v_stx_1173_);
v___x_1203_ = lean_box(0);
return v___x_1203_;
}
else
{
goto v___jp_1195_;
}
}
else
{
goto v___jp_1195_;
}
v___jp_1181_:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Doc_CodeView_of(v___y_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; 
lean_dec(v___x_1180_);
lean_dec(v_stx_1173_);
v___x_1184_ = lean_box(0);
return v___x_1184_;
}
else
{
lean_object* v_val_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1194_; 
v_val_1185_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1187_ = v___x_1183_;
v_isShared_1188_ = v_isSharedCheck_1194_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_val_1185_);
lean_dec(v___x_1183_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1194_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1189_ = 1;
v___x_1190_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1190_, 0, v_stx_1173_);
lean_ctor_set(v___x_1190_, 1, v___x_1180_);
lean_ctor_set(v___x_1190_, 2, v_val_1185_);
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*3, v___x_1189_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1190_);
v___x_1192_ = v___x_1187_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
v___jp_1195_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(1u);
v___x_1197_ = l_Lean_Syntax_getArg(v_stx_1173_, v___x_1196_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v___x_1197_);
v___x_1199_ = l_Lean_Syntax_isOfKind(v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
lean_dec(v___x_1197_);
lean_dec(v___x_1180_);
lean_dec(v_stx_1173_);
v___x_1200_ = lean_box(0);
return v___x_1200_;
}
else
{
v___y_1182_ = v___x_1197_;
goto v___jp_1181_;
}
}
else
{
v___y_1182_ = v___x_1197_;
goto v___jp_1181_;
}
}
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = l_Lean_Syntax_getArg(v_stx_1173_, v___x_1204_);
v___x_1206_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__7));
lean_inc(v___x_1205_);
v___x_1207_ = l_Lean_Syntax_isOfKind(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
lean_dec(v___x_1205_);
lean_dec(v_stx_1173_);
v___x_1208_ = lean_box(0);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = l_Lean_Syntax_getArg(v_stx_1173_, v___x_1209_);
v___x_1211_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v___x_1210_);
v___x_1212_ = l_Lean_Syntax_isOfKind(v___x_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec(v___x_1210_);
lean_dec(v___x_1205_);
lean_dec(v_stx_1173_);
v___x_1213_ = lean_box(0);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Doc_CodeView_of(v___x_1210_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1215_; 
lean_dec(v___x_1205_);
lean_dec(v_stx_1173_);
v___x_1215_ = lean_box(0);
return v___x_1215_;
}
else
{
lean_object* v_val_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1225_; 
v_val_1216_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1218_ = v___x_1214_;
v_isShared_1219_ = v_isSharedCheck_1225_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_val_1216_);
lean_dec(v___x_1214_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1225_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1220_ = 0;
v___x_1221_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1221_, 0, v_stx_1173_);
lean_ctor_set(v___x_1221_, 1, v___x_1205_);
lean_ctor_set(v___x_1221_, 2, v_val_1216_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*3, v___x_1220_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1221_);
v___x_1223_ = v___x_1218_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkView_of(lean_object* v_stx_1233_){
_start:
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = ((lean_object*)(l_Lean_Doc_LinkView_of___closed__1));
lean_inc(v_stx_1233_);
v___x_1235_ = l_Lean_Syntax_isOfKind(v_stx_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_dec(v_stx_1233_);
v___x_1236_ = lean_box(0);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v_tgt_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_unsigned_to_nat(3u);
v_tgt_1238_ = l_Lean_Syntax_getArg(v_stx_1233_, v___x_1237_);
v___x_1239_ = l_Lean_Doc_LinkTargetView_of(v_tgt_1238_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v___x_1240_; 
lean_dec(v_stx_1233_);
v___x_1240_ = lean_box(0);
return v___x_1240_;
}
else
{
lean_object* v_val_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1256_; 
v_val_1241_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1243_ = v___x_1239_;
v_isShared_1244_ = v_isSharedCheck_1256_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_val_1241_);
lean_dec(v___x_1239_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1256_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v_o_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v_c_1250_; lean_object* v_inl_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1245_ = lean_unsigned_to_nat(0u);
v_o_1246_ = l_Lean_Syntax_getArg(v_stx_1233_, v___x_1245_);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = l_Lean_Syntax_getArg(v_stx_1233_, v___x_1247_);
v___x_1249_ = lean_unsigned_to_nat(2u);
v_c_1250_ = l_Lean_Syntax_getArg(v_stx_1233_, v___x_1249_);
v_inl_1251_ = l_Lean_Syntax_getArgs(v___x_1248_);
lean_dec(v___x_1248_);
v___x_1252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1252_, 0, v_stx_1233_);
lean_ctor_set(v___x_1252_, 1, v_o_1246_);
lean_ctor_set(v___x_1252_, 2, v_inl_1251_);
lean_ctor_set(v___x_1252_, 3, v_c_1250_);
lean_ctor_set(v___x_1252_, 4, v_val_1241_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1252_);
v___x_1254_ = v___x_1243_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt(lean_object* v_v_1257_){
_start:
{
lean_object* v_alt_1258_; lean_object* v___x_1259_; 
v_alt_1258_ = lean_ctor_get(v_v_1257_, 2);
v___x_1259_ = l_Lean_TSyntax_getVersoImageAlt(v_alt_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt___boxed(lean_object* v_v_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Doc_ImageView_getAlt(v_v_1260_);
lean_dec_ref(v_v_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_of(lean_object* v_stx_1275_){
_start:
{
lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1276_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__1));
lean_inc(v_stx_1275_);
v___x_1277_ = l_Lean_Syntax_isOfKind(v_stx_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
lean_dec(v_stx_1275_);
v___x_1278_ = lean_box(0);
return v___x_1278_;
}
else
{
lean_object* v___x_1279_; lean_object* v_alt_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1279_ = lean_unsigned_to_nat(1u);
v_alt_1280_ = l_Lean_Syntax_getArg(v_stx_1275_, v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__3));
lean_inc(v_alt_1280_);
v___x_1282_ = l_Lean_Syntax_isOfKind(v_alt_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
lean_dec(v_alt_1280_);
lean_dec(v_stx_1275_);
v___x_1283_ = lean_box(0);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; lean_object* v_tgt_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_unsigned_to_nat(3u);
v_tgt_1285_ = l_Lean_Syntax_getArg(v_stx_1275_, v___x_1284_);
v___x_1286_ = l_Lean_Doc_LinkTargetView_of(v_tgt_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1287_; 
lean_dec(v_alt_1280_);
lean_dec(v_stx_1275_);
v___x_1287_ = lean_box(0);
return v___x_1287_;
}
else
{
lean_object* v_val_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1300_; 
v_val_1288_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1290_ = v___x_1286_;
v_isShared_1291_ = v_isSharedCheck_1300_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_val_1288_);
lean_dec(v___x_1286_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1300_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v_o_1293_; lean_object* v___x_1294_; lean_object* v_c_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1292_ = lean_unsigned_to_nat(0u);
v_o_1293_ = l_Lean_Syntax_getArg(v_stx_1275_, v___x_1292_);
v___x_1294_ = lean_unsigned_to_nat(2u);
v_c_1295_ = l_Lean_Syntax_getArg(v_stx_1275_, v___x_1294_);
v___x_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1296_, 0, v_stx_1275_);
lean_ctor_set(v___x_1296_, 1, v_o_1293_);
lean_ctor_set(v___x_1296_, 2, v_alt_1280_);
lean_ctor_set(v___x_1296_, 3, v_c_1295_);
lean_ctor_set(v___x_1296_, 4, v_val_1288_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1296_);
v___x_1298_ = v___x_1290_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName(lean_object* v_v_1301_){
_start:
{
lean_object* v_name_1302_; lean_object* v___x_1303_; 
v_name_1302_ = lean_ctor_get(v_v_1301_, 2);
v___x_1303_ = l_Lean_TSyntax_getVersoRefName(v_name_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName___boxed(lean_object* v_v_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Doc_FootnoteView_getName(v_v_1304_);
lean_dec_ref(v_v_1304_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_of(lean_object* v_stx_1313_){
_start:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_Doc_FootnoteView_of___closed__1));
lean_inc(v_stx_1313_);
v___x_1315_ = l_Lean_Syntax_isOfKind(v_stx_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_dec(v_stx_1313_);
v___x_1316_ = lean_box(0);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; lean_object* v_name_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1317_ = lean_unsigned_to_nat(1u);
v_name_1318_ = l_Lean_Syntax_getArg(v_stx_1313_, v___x_1317_);
v___x_1319_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_1318_);
v___x_1320_ = l_Lean_Syntax_isOfKind(v_name_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
lean_dec(v_name_1318_);
lean_dec(v_stx_1313_);
v___x_1321_ = lean_box(0);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; lean_object* v_o_1323_; lean_object* v___x_1324_; lean_object* v_c_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1322_ = lean_unsigned_to_nat(0u);
v_o_1323_ = l_Lean_Syntax_getArg(v_stx_1313_, v___x_1322_);
v___x_1324_ = lean_unsigned_to_nat(2u);
v_c_1325_ = l_Lean_Syntax_getArg(v_stx_1313_, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1326_, 0, v_stx_1313_);
lean_ctor_set(v___x_1326_, 1, v_o_1323_);
lean_ctor_set(v___x_1326_, 2, v_name_1318_);
lean_ctor_set(v___x_1326_, 3, v_c_1325_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinebreakView_of(lean_object* v_stx_1328_){
_start:
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
lean_inc(v_stx_1328_);
v___x_1330_ = l_Lean_Syntax_isOfKind(v_stx_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
lean_dec(v_stx_1328_);
v___x_1331_ = lean_box(0);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = l_Lean_Syntax_getArg(v_stx_1328_, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_stx_1328_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_RoleView_of(lean_object* v_stx_1343_){
_start:
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = ((lean_object*)(l_Lean_Doc_RoleView_of___closed__1));
lean_inc(v_stx_1343_);
v___x_1345_ = l_Lean_Syntax_isOfKind(v_stx_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec(v_stx_1343_);
v___x_1346_ = lean_box(0);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; lean_object* v_name_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1347_ = lean_unsigned_to_nat(1u);
v_name_1348_ = l_Lean_Syntax_getArg(v_stx_1343_, v___x_1347_);
v___x_1349_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_1348_);
v___x_1350_ = l_Lean_Syntax_isOfKind(v_name_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_dec(v_name_1348_);
lean_dec(v_stx_1343_);
v___x_1351_ = lean_box(0);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v_bo_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_bc_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1352_ = lean_unsigned_to_nat(0u);
v_bo_1353_ = l_Lean_Syntax_getArg(v_stx_1343_, v___x_1352_);
v___x_1354_ = lean_unsigned_to_nat(2u);
v___x_1355_ = l_Lean_Syntax_getArg(v_stx_1343_, v___x_1354_);
v___x_1356_ = lean_unsigned_to_nat(3u);
v_bc_1357_ = l_Lean_Syntax_getArg(v_stx_1343_, v___x_1356_);
v___x_1358_ = lean_unsigned_to_nat(4u);
v___x_1359_ = l_Lean_Syntax_getArg(v_stx_1343_, v___x_1358_);
lean_inc(v___x_1359_);
v___x_1360_ = l_Lean_Syntax_matchesNull(v___x_1359_, v___x_1347_);
if (v___x_1360_ == 0)
{
uint8_t v___x_1361_; 
v___x_1361_ = l_Lean_Syntax_matchesNull(v___x_1359_, v___x_1352_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_dec(v_bc_1357_);
lean_dec(v___x_1355_);
lean_dec(v_bo_1353_);
lean_dec(v_name_1348_);
lean_dec(v_stx_1343_);
v___x_1362_ = lean_box(0);
return v___x_1362_;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1363_ = lean_unsigned_to_nat(6u);
v___x_1364_ = l_Lean_Syntax_getArg(v_stx_1343_, v___x_1363_);
v___x_1365_ = l_Lean_Syntax_matchesNull(v___x_1364_, v___x_1352_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_dec(v_bc_1357_);
lean_dec(v___x_1355_);
lean_dec(v_bo_1353_);
lean_dec(v_name_1348_);
lean_dec(v_stx_1343_);
v___x_1366_ = lean_box(0);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_inl_1369_; lean_object* v_args_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1367_ = lean_unsigned_to_nat(5u);
v___x_1368_ = l_Lean_Syntax_getArg(v_stx_1343_, v___x_1367_);
v_inl_1369_ = l_Lean_Syntax_getArgs(v___x_1368_);
lean_dec(v___x_1368_);
v_args_1370_ = l_Lean_Syntax_getArgs(v___x_1355_);
lean_dec(v___x_1355_);
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1372_, 0, v_stx_1343_);
lean_ctor_set(v___x_1372_, 1, v_bo_1353_);
lean_ctor_set(v___x_1372_, 2, v_name_1348_);
lean_ctor_set(v___x_1372_, 3, v_args_1370_);
lean_ctor_set(v___x_1372_, 4, v_bc_1357_);
lean_ctor_set(v___x_1372_, 5, v___x_1371_);
lean_ctor_set(v___x_1372_, 6, v_inl_1369_);
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1374_ = lean_unsigned_to_nat(6u);
v___x_1375_ = l_Lean_Syntax_getArg(v_stx_1343_, v___x_1374_);
lean_inc(v___x_1375_);
v___x_1376_ = l_Lean_Syntax_matchesNull(v___x_1375_, v___x_1347_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec(v___x_1375_);
lean_dec(v___x_1359_);
lean_dec(v_bc_1357_);
lean_dec(v___x_1355_);
lean_dec(v_bo_1353_);
lean_dec(v_name_1348_);
lean_dec(v_stx_1343_);
v___x_1377_ = lean_box(0);
return v___x_1377_;
}
else
{
lean_object* v_so_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_sc_1381_; lean_object* v_inl_1382_; lean_object* v_args_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_so_1378_ = l_Lean_Syntax_getArg(v___x_1359_, v___x_1352_);
lean_dec(v___x_1359_);
v___x_1379_ = lean_unsigned_to_nat(5u);
v___x_1380_ = l_Lean_Syntax_getArg(v_stx_1343_, v___x_1379_);
v_sc_1381_ = l_Lean_Syntax_getArg(v___x_1375_, v___x_1352_);
lean_dec(v___x_1375_);
v_inl_1382_ = l_Lean_Syntax_getArgs(v___x_1380_);
lean_dec(v___x_1380_);
v_args_1383_ = l_Lean_Syntax_getArgs(v___x_1355_);
lean_dec(v___x_1355_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_so_1378_);
lean_ctor_set(v___x_1384_, 1, v_sc_1381_);
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
v___x_1386_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1386_, 0, v_stx_1343_);
lean_ctor_set(v___x_1386_, 1, v_bo_1353_);
lean_ctor_set(v___x_1386_, 2, v_name_1348_);
lean_ctor_set(v___x_1386_, 3, v_args_1383_);
lean_ctor_set(v___x_1386_, 4, v_bc_1357_);
lean_ctor_set(v___x_1386_, 5, v___x_1385_);
lean_ctor_set(v___x_1386_, 6, v_inl_1382_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx(lean_object* v_x_1388_){
_start:
{
switch(lean_obj_tag(v_x_1388_))
{
case 0:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_unsigned_to_nat(0u);
return v___x_1389_;
}
case 1:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_unsigned_to_nat(1u);
return v___x_1390_;
}
case 2:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_unsigned_to_nat(2u);
return v___x_1391_;
}
case 3:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_unsigned_to_nat(3u);
return v___x_1392_;
}
case 4:
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_unsigned_to_nat(4u);
return v___x_1393_;
}
case 5:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_unsigned_to_nat(5u);
return v___x_1394_;
}
case 6:
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_unsigned_to_nat(6u);
return v___x_1395_;
}
case 7:
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_unsigned_to_nat(7u);
return v___x_1396_;
}
case 8:
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_unsigned_to_nat(8u);
return v___x_1397_;
}
default: 
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_unsigned_to_nat(9u);
return v___x_1398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___boxed(lean_object* v_x_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Doc_InlineView_ctorIdx(v_x_1399_);
lean_dec_ref(v_x_1399_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___redArg(lean_object* v_t_1401_, lean_object* v_k_1402_){
_start:
{
lean_object* v_view_1403_; lean_object* v___x_1404_; 
v_view_1403_ = lean_ctor_get(v_t_1401_, 0);
lean_inc_ref(v_view_1403_);
lean_dec_ref(v_t_1401_);
v___x_1404_ = lean_apply_1(v_k_1402_, v_view_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim(lean_object* v_motive_1405_, lean_object* v_ctorIdx_1406_, lean_object* v_t_1407_, lean_object* v_h_1408_, lean_object* v_k_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1407_, v_k_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___boxed(lean_object* v_motive_1411_, lean_object* v_ctorIdx_1412_, lean_object* v_t_1413_, lean_object* v_h_1414_, lean_object* v_k_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Doc_InlineView_ctorElim(v_motive_1411_, v_ctorIdx_1412_, v_t_1413_, v_h_1414_, v_k_1415_);
lean_dec(v_ctorIdx_1412_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim___redArg(lean_object* v_t_1417_, lean_object* v_text_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1417_, v_text_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim(lean_object* v_motive_1420_, lean_object* v_t_1421_, lean_object* v_h_1422_, lean_object* v_text_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1421_, v_text_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim___redArg(lean_object* v_t_1425_, lean_object* v_emph_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1425_, v_emph_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim(lean_object* v_motive_1428_, lean_object* v_t_1429_, lean_object* v_h_1430_, lean_object* v_emph_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1429_, v_emph_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim___redArg(lean_object* v_t_1433_, lean_object* v_bold_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1433_, v_bold_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim(lean_object* v_motive_1436_, lean_object* v_t_1437_, lean_object* v_h_1438_, lean_object* v_bold_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1437_, v_bold_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim___redArg(lean_object* v_t_1441_, lean_object* v_code_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1441_, v_code_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim(lean_object* v_motive_1444_, lean_object* v_t_1445_, lean_object* v_h_1446_, lean_object* v_code_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1445_, v_code_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim___redArg(lean_object* v_t_1449_, lean_object* v_math_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1449_, v_math_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim(lean_object* v_motive_1452_, lean_object* v_t_1453_, lean_object* v_h_1454_, lean_object* v_math_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1453_, v_math_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim___redArg(lean_object* v_t_1457_, lean_object* v_link_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1457_, v_link_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim(lean_object* v_motive_1460_, lean_object* v_t_1461_, lean_object* v_h_1462_, lean_object* v_link_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1461_, v_link_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim___redArg(lean_object* v_t_1465_, lean_object* v_image_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1465_, v_image_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim(lean_object* v_motive_1468_, lean_object* v_t_1469_, lean_object* v_h_1470_, lean_object* v_image_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1469_, v_image_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim___redArg(lean_object* v_t_1473_, lean_object* v_footnote_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1473_, v_footnote_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim(lean_object* v_motive_1476_, lean_object* v_t_1477_, lean_object* v_h_1478_, lean_object* v_footnote_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1477_, v_footnote_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim___redArg(lean_object* v_t_1481_, lean_object* v_linebreak_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1481_, v_linebreak_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim(lean_object* v_motive_1484_, lean_object* v_t_1485_, lean_object* v_h_1486_, lean_object* v_linebreak_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1485_, v_linebreak_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim___redArg(lean_object* v_t_1489_, lean_object* v_role_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1489_, v_role_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim(lean_object* v_motive_1492_, lean_object* v_t_1493_, lean_object* v_h_1494_, lean_object* v_role_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1493_, v_role_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTextViewInlineView___lam__0(lean_object* v_view_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_view_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeEmphViewInlineView___lam__0(lean_object* v_view_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_view_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBoldViewInlineView___lam__0(lean_object* v_view_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_view_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeViewInlineView___lam__0(lean_object* v_view_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_view_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMathViewInlineView___lam__0(lean_object* v_view_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1518_, 0, v_view_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkViewInlineView___lam__0(lean_object* v_view_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_view_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeImageViewInlineView___lam__0(lean_object* v_view_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_view_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0(lean_object* v_view_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_view_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0(lean_object* v_view_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_view_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeRoleViewInlineView___lam__0(lean_object* v_view_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_view_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx(lean_object* v_x_1541_){
_start:
{
lean_object* v_view_1542_; lean_object* v_stx_1543_; 
v_view_1542_ = lean_ctor_get(v_x_1541_, 0);
v_stx_1543_ = lean_ctor_get(v_view_1542_, 0);
lean_inc(v_stx_1543_);
return v_stx_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx___boxed(lean_object* v_x_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Doc_InlineView_stx(v_x_1544_);
lean_dec_ref(v_x_1544_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_of(lean_object* v_stx_1546_){
_start:
{
lean_object* v___x_1547_; 
lean_inc(v_stx_1546_);
v___x_1547_ = l_Lean_Doc_TextView_of(v_stx_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; 
lean_inc(v_stx_1546_);
v___x_1548_ = l_Lean_Doc_EmphView_of(v_stx_1546_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v___x_1549_; 
lean_inc(v_stx_1546_);
v___x_1549_ = l_Lean_Doc_BoldView_of(v_stx_1546_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1550_; 
lean_inc(v_stx_1546_);
v___x_1550_ = l_Lean_Doc_CodeView_of(v_stx_1546_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; 
lean_inc(v_stx_1546_);
v___x_1551_ = l_Lean_Doc_MathView_of(v_stx_1546_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v___x_1552_; 
lean_inc(v_stx_1546_);
v___x_1552_ = l_Lean_Doc_LinkView_of(v_stx_1546_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v___x_1553_; 
lean_inc(v_stx_1546_);
v___x_1553_ = l_Lean_Doc_ImageView_of(v_stx_1546_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v___x_1554_; 
lean_inc(v_stx_1546_);
v___x_1554_ = l_Lean_Doc_FootnoteView_of(v_stx_1546_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1555_; 
lean_inc(v_stx_1546_);
v___x_1555_ = l_Lean_Doc_LinebreakView_of(v_stx_1546_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Doc_RoleView_of(v_stx_1546_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_box(0);
return v___x_1557_;
}
else
{
lean_object* v_val_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1566_; 
v_val_1558_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1560_ = v___x_1556_;
v_isShared_1561_ = v_isSharedCheck_1566_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_val_1558_);
lean_dec(v___x_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1566_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1562_, 0, v_val_1558_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1562_);
v___x_1564_ = v___x_1560_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_object* v_val_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v_stx_1546_);
v_val_1567_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1569_ = v___x_1555_;
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_val_1567_);
lean_dec(v___x_1555_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_val_1567_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1571_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_object* v_val_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_stx_1546_);
v_val_1576_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1578_ = v___x_1554_;
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_val_1576_);
lean_dec(v___x_1554_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_val_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1580_);
v___x_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_val_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_stx_1546_);
v_val_1585_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1587_ = v___x_1553_;
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_val_1585_);
lean_dec(v___x_1553_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1589_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1589_, 0, v_val_1585_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1589_);
v___x_1591_ = v___x_1587_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_val_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_stx_1546_);
v_val_1594_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1596_ = v___x_1552_;
v_isShared_1597_ = v_isSharedCheck_1602_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_val_1594_);
lean_dec(v___x_1552_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1602_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_val_1594_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1598_);
v___x_1600_ = v___x_1596_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_val_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_stx_1546_);
v_val_1603_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1605_ = v___x_1551_;
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_val_1603_);
lean_dec(v___x_1551_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1607_, 0, v_val_1603_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v_val_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v_stx_1546_);
v_val_1612_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1614_ = v___x_1550_;
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_val_1612_);
lean_dec(v___x_1550_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1616_, 0, v_val_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v_val_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_stx_1546_);
v_val_1621_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1623_ = v___x_1549_;
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_val_1621_);
lean_dec(v___x_1549_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1625_, 0, v_val_1621_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1625_);
v___x_1627_ = v___x_1623_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_val_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_stx_1546_);
v_val_1630_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1632_ = v___x_1548_;
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_val_1630_);
lean_dec(v___x_1548_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_val_1630_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1634_);
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v_val_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_stx_1546_);
v_val_1639_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1641_ = v___x_1547_;
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_val_1639_);
lean_dec(v___x_1547_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_val_1639_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1643_);
v___x_1645_ = v___x_1641_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(uint32_t v_a_1648_, lean_object* v_x_1649_){
_start:
{
if (lean_obj_tag(v_x_1649_) == 0)
{
uint8_t v___x_1650_; 
v___x_1650_ = 0;
return v___x_1650_;
}
else
{
lean_object* v_head_1651_; lean_object* v_tail_1652_; uint32_t v___x_1653_; uint8_t v___x_1654_; 
v_head_1651_ = lean_ctor_get(v_x_1649_, 0);
v_tail_1652_ = lean_ctor_get(v_x_1649_, 1);
v___x_1653_ = lean_unbox_uint32(v_head_1651_);
v___x_1654_ = lean_uint32_dec_eq(v_a_1648_, v___x_1653_);
if (v___x_1654_ == 0)
{
v_x_1649_ = v_tail_1652_;
goto _start;
}
else
{
return v___x_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0___boxed(lean_object* v_a_1656_, lean_object* v_x_1657_){
_start:
{
uint32_t v_a_boxed_1658_; uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_a_boxed_1658_ = lean_unbox_uint32(v_a_1656_);
lean_dec(v_a_1656_);
v_res_1659_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v_a_boxed_1658_, v_x_1657_);
lean_dec(v_x_1657_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = 43;
v___x_1676_ = lean_box_uint32(v___x_1675_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__5(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_box(0);
v___x_1678_ = l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1;
v___x_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
lean_ctor_set(v___x_1679_, 1, v___x_1677_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = 45;
v___x_1681_ = lean_box_uint32(v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__6(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__5, &l_Lean_Doc_UnorderedListItemView_of___closed__5_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__5);
v___x_1683_ = l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1;
v___x_1684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
lean_ctor_set(v___x_1684_, 1, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = 42;
v___x_1686_ = lean_box_uint32(v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__7(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__6, &l_Lean_Doc_UnorderedListItemView_of___closed__6_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__6);
v___x_1688_ = l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1;
v___x_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v___x_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of(lean_object* v_stx_1690_){
_start:
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__2));
lean_inc(v_stx_1690_);
v___x_1692_ = l_Lean_Syntax_isOfKind(v_stx_1690_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; 
lean_dec(v_stx_1690_);
v___x_1693_ = lean_box(0);
return v___x_1693_;
}
else
{
lean_object* v___x_1694_; lean_object* v_m_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1694_ = lean_unsigned_to_nat(0u);
v_m_1695_ = l_Lean_Syntax_getArg(v_stx_1690_, v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__4));
lean_inc(v_m_1695_);
v___x_1697_ = l_Lean_Syntax_isOfKind(v_m_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
lean_dec(v_m_1695_);
lean_dec(v_stx_1690_);
v___x_1698_ = lean_box(0);
return v___x_1698_;
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1699_ = l_Lean_TSyntax_getVersoDelimiter(v_m_1695_);
v___x_1700_ = lean_string_utf8_byte_size(v___x_1699_);
v___x_1701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1694_);
lean_ctor_set(v___x_1701_, 2, v___x_1700_);
v___x_1702_ = l_String_Slice_Pos_get_x3f(v___x_1701_, v___x_1694_);
lean_dec_ref_known(v___x_1701_, 3);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v___x_1703_; 
lean_dec(v_m_1695_);
lean_dec(v_stx_1690_);
v___x_1703_ = lean_box(0);
return v___x_1703_;
}
else
{
lean_object* v_val_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1719_; 
v_val_1704_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1706_ = v___x_1702_;
v_isShared_1707_ = v_isSharedCheck_1719_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_val_1704_);
lean_dec(v___x_1702_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1719_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; uint32_t v___x_1709_; uint8_t v___x_1710_; 
v___x_1708_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__7, &l_Lean_Doc_UnorderedListItemView_of___closed__7_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__7);
v___x_1709_ = lean_unbox_uint32(v_val_1704_);
lean_dec(v_val_1704_);
v___x_1710_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v___x_1709_, v___x_1708_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_del_object(v___x_1706_);
lean_dec(v_m_1695_);
lean_dec(v_stx_1690_);
v___x_1711_ = lean_box(0);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v_bs_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1712_ = lean_unsigned_to_nat(1u);
v___x_1713_ = l_Lean_Syntax_getArg(v_stx_1690_, v___x_1712_);
v_bs_1714_ = l_Lean_Syntax_getArgs(v___x_1713_);
lean_dec(v___x_1713_);
v___x_1715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1715_, 0, v_stx_1690_);
lean_ctor_set(v___x_1715_, 1, v_m_1695_);
lean_ctor_set(v___x_1715_, 2, v_bs_1714_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1715_);
v___x_1717_ = v___x_1706_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(lean_object* v_s_1720_, lean_object* v_pos_1721_){
_start:
{
lean_object* v_str_1722_; lean_object* v_startInclusive_1723_; lean_object* v_endExclusive_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v_decide_1728_; 
v_str_1722_ = lean_ctor_get(v_s_1720_, 0);
v_startInclusive_1723_ = lean_ctor_get(v_s_1720_, 1);
v_endExclusive_1724_ = lean_ctor_get(v_s_1720_, 2);
v___x_1725_ = lean_nat_add(v_startInclusive_1723_, v_pos_1721_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = lean_nat_sub(v_endExclusive_1724_, v___x_1725_);
v_decide_1728_ = lean_nat_dec_eq(v___x_1726_, v___x_1727_);
lean_dec(v___x_1727_);
if (v_decide_1728_ == 0)
{
uint32_t v___x_1729_; uint32_t v___x_1730_; uint8_t v___x_1731_; 
v___x_1729_ = lean_string_utf8_get_fast(v_str_1722_, v___x_1725_);
v___x_1730_ = 48;
v___x_1731_ = lean_uint32_dec_le(v___x_1730_, v___x_1729_);
if (v___x_1731_ == 0)
{
lean_dec(v___x_1725_);
return v_pos_1721_;
}
else
{
uint32_t v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = 57;
v___x_1733_ = lean_uint32_dec_le(v___x_1729_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_dec(v___x_1725_);
return v_pos_1721_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1734_ = lean_string_utf8_next_fast(v_str_1722_, v___x_1725_);
v___x_1735_ = lean_nat_sub(v___x_1734_, v___x_1725_);
lean_dec(v___x_1725_);
v___x_1736_ = lean_nat_add(v_pos_1721_, v___x_1735_);
lean_dec(v___x_1735_);
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = lean_nat_add(v_pos_1721_, v___x_1737_);
v___x_1739_ = lean_nat_dec_le(v___x_1738_, v___x_1736_);
lean_dec(v___x_1738_);
if (v___x_1739_ == 0)
{
lean_dec(v___x_1736_);
return v_pos_1721_;
}
else
{
lean_dec(v_pos_1721_);
v_pos_1721_ = v___x_1736_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_1725_);
return v_pos_1721_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0___boxed(lean_object* v_s_1741_, lean_object* v_pos_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v_s_1741_, v_pos_1742_);
lean_dec_ref(v_s_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_number(lean_object* v_v_1744_){
_start:
{
lean_object* v_marker_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1760_; 
v_marker_1745_ = lean_ctor_get(v_v_1744_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_v_1744_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; lean_object* v_unused_1762_; 
v_unused_1761_ = lean_ctor_get(v_v_1744_, 2);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v_v_1744_, 0);
lean_dec(v_unused_1762_);
v___x_1747_ = v_v_1744_;
v_isShared_1748_ = v_isSharedCheck_1760_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_marker_1745_);
lean_dec(v_v_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1760_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1749_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_1745_);
lean_dec(v_marker_1745_);
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_string_utf8_byte_size(v___x_1749_);
lean_inc_ref(v___x_1749_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 2, v___x_1751_);
lean_ctor_set(v___x_1747_, 1, v___x_1750_);
lean_ctor_set(v___x_1747_, 0, v___x_1749_);
v___x_1753_ = v___x_1747_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1754_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v___x_1753_, v___x_1750_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = lean_string_utf8_extract_fast(v___x_1749_, v___x_1750_, v___x_1754_);
lean_dec(v___x_1754_);
lean_dec_ref(v___x_1749_);
v___x_1756_ = lean_string_utf8_byte_size(v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1750_);
lean_ctor_set(v___x_1757_, 2, v___x_1756_);
v___x_1758_ = l_String_Slice_toNat_x3f(v___x_1757_);
lean_dec_ref_known(v___x_1757_, 3);
return v___x_1758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_of(lean_object* v_stx_1763_){
_start:
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__2));
lean_inc(v_stx_1763_);
v___x_1765_ = l_Lean_Syntax_isOfKind(v_stx_1763_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; 
lean_dec(v_stx_1763_);
v___x_1766_ = lean_box(0);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; lean_object* v_m_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
v_m_1768_ = l_Lean_Syntax_getArg(v_stx_1763_, v___x_1767_);
v___x_1769_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__4));
lean_inc(v_m_1768_);
v___x_1770_ = l_Lean_Syntax_isOfKind(v_m_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
lean_dec(v_m_1768_);
lean_dec(v_stx_1763_);
v___x_1771_ = lean_box(0);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1772_ = l_Lean_TSyntax_getVersoDelimiter(v_m_1768_);
v___x_1773_ = lean_string_utf8_byte_size(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1767_);
lean_ctor_set(v___x_1774_, 2, v___x_1773_);
v___x_1775_ = l_String_Slice_Pos_get_x3f(v___x_1774_, v___x_1767_);
lean_dec_ref_known(v___x_1774_, 3);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v___x_1776_; 
lean_dec(v_m_1768_);
lean_dec(v_stx_1763_);
v___x_1776_ = lean_box(0);
return v___x_1776_;
}
else
{
lean_object* v_val_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1796_; 
v_val_1777_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1779_ = v___x_1775_;
v_isShared_1780_ = v_isSharedCheck_1796_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_val_1777_);
lean_dec(v___x_1775_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1796_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
uint32_t v___x_1781_; uint32_t v___x_1782_; uint8_t v___x_1783_; 
v___x_1781_ = 48;
v___x_1782_ = lean_unbox_uint32(v_val_1777_);
v___x_1783_ = lean_uint32_dec_le(v___x_1781_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; 
lean_del_object(v___x_1779_);
lean_dec(v_val_1777_);
lean_dec(v_m_1768_);
lean_dec(v_stx_1763_);
v___x_1784_ = lean_box(0);
return v___x_1784_;
}
else
{
uint32_t v___x_1785_; uint32_t v___x_1786_; uint8_t v___x_1787_; 
v___x_1785_ = 57;
v___x_1786_ = lean_unbox_uint32(v_val_1777_);
lean_dec(v_val_1777_);
v___x_1787_ = lean_uint32_dec_le(v___x_1786_, v___x_1785_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; 
lean_del_object(v___x_1779_);
lean_dec(v_m_1768_);
lean_dec(v_stx_1763_);
v___x_1788_ = lean_box(0);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v_bs_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = l_Lean_Syntax_getArg(v_stx_1763_, v___x_1789_);
v_bs_1791_ = l_Lean_Syntax_getArgs(v___x_1790_);
lean_dec(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1792_, 0, v_stx_1763_);
lean_ctor_set(v___x_1792_, 1, v_m_1768_);
lean_ctor_set(v___x_1792_, 2, v_bs_1791_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1792_);
v___x_1794_ = v___x_1779_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescItemView_of(lean_object* v_stx_1804_){
_start:
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_Lean_Doc_DescItemView_of___closed__1));
lean_inc(v_stx_1804_);
v___x_1806_ = l_Lean_Syntax_isOfKind(v_stx_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec(v_stx_1804_);
v___x_1807_ = lean_box(0);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; lean_object* v_marker_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v_desc_1814_; lean_object* v_term_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1808_ = lean_unsigned_to_nat(0u);
v_marker_1809_ = l_Lean_Syntax_getArg(v_stx_1804_, v___x_1808_);
v___x_1810_ = lean_unsigned_to_nat(1u);
v___x_1811_ = l_Lean_Syntax_getArg(v_stx_1804_, v___x_1810_);
v___x_1812_ = lean_unsigned_to_nat(2u);
v___x_1813_ = l_Lean_Syntax_getArg(v_stx_1804_, v___x_1812_);
v_desc_1814_ = l_Lean_Syntax_getArgs(v___x_1813_);
lean_dec(v___x_1813_);
v_term_1815_ = l_Lean_Syntax_getArgs(v___x_1811_);
lean_dec(v___x_1811_);
v___x_1816_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1816_, 0, v_stx_1804_);
lean_ctor_set(v___x_1816_, 1, v_marker_1809_);
lean_ctor_set(v___x_1816_, 2, v_term_1815_);
lean_ctor_set(v___x_1816_, 3, v_desc_1814_);
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ParaView_of(lean_object* v_stx_1833_){
_start:
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_Lean_Doc_ParaView_of___closed__2));
lean_inc(v_stx_1833_);
v___x_1835_ = l_Lean_Syntax_isOfKind(v_stx_1833_, v___x_1834_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
lean_dec(v_stx_1833_);
v___x_1836_ = lean_box(0);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v_inl_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = l_Lean_Syntax_getArg(v_stx_1833_, v___x_1837_);
v_inl_1839_ = l_Lean_Syntax_getArgs(v___x_1838_);
lean_dec(v___x_1838_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_stx_1833_);
lean_ctor_set(v___x_1840_, 1, v_inl_1839_);
v___x_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
return v___x_1841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(size_t v_sz_1842_, size_t v_i_1843_, lean_object* v_bs_1844_){
_start:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_usize_dec_lt(v_i_1843_, v_sz_1842_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_bs_1844_);
return v___x_1846_;
}
else
{
lean_object* v_v_1847_; lean_object* v___x_1848_; 
v_v_1847_ = lean_array_uget_borrowed(v_bs_1844_, v_i_1843_);
lean_inc(v_v_1847_);
v___x_1848_ = l_Lean_Doc_UnorderedListItemView_of(v_v_1847_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v___x_1849_; 
lean_dec_ref(v_bs_1844_);
v___x_1849_ = lean_box(0);
return v___x_1849_;
}
else
{
lean_object* v_val_1850_; lean_object* v___x_1851_; lean_object* v_bs_x27_1852_; size_t v___x_1853_; size_t v___x_1854_; lean_object* v___x_1855_; 
v_val_1850_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_val_1850_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1851_ = lean_unsigned_to_nat(0u);
v_bs_x27_1852_ = lean_array_uset(v_bs_1844_, v_i_1843_, v___x_1851_);
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_add(v_i_1843_, v___x_1853_);
v___x_1855_ = lean_array_uset(v_bs_x27_1852_, v_i_1843_, v_val_1850_);
v_i_1843_ = v___x_1854_;
v_bs_1844_ = v___x_1855_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0___boxed(lean_object* v_sz_1857_, lean_object* v_i_1858_, lean_object* v_bs_1859_){
_start:
{
size_t v_sz_boxed_1860_; size_t v_i_boxed_1861_; lean_object* v_res_1862_; 
v_sz_boxed_1860_ = lean_unbox_usize(v_sz_1857_);
lean_dec(v_sz_1857_);
v_i_boxed_1861_ = lean_unbox_usize(v_i_1858_);
lean_dec(v_i_1858_);
v_res_1862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_boxed_1860_, v_i_boxed_1861_, v_bs_1859_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListView_of(lean_object* v_stx_1870_){
_start:
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = ((lean_object*)(l_Lean_Doc_UnorderedListView_of___closed__1));
lean_inc(v_stx_1870_);
v___x_1872_ = l_Lean_Syntax_isOfKind(v_stx_1870_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_dec(v_stx_1870_);
v___x_1873_ = lean_box(0);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_items_1876_; size_t v_sz_1877_; size_t v___x_1878_; lean_object* v___x_1879_; 
v___x_1874_ = lean_unsigned_to_nat(0u);
v___x_1875_ = l_Lean_Syntax_getArg(v_stx_1870_, v___x_1874_);
v_items_1876_ = l_Lean_Syntax_getArgs(v___x_1875_);
lean_dec(v___x_1875_);
v_sz_1877_ = lean_array_size(v_items_1876_);
v___x_1878_ = ((size_t)0ULL);
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_1877_, v___x_1878_, v_items_1876_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v___x_1880_; 
lean_dec(v_stx_1870_);
v___x_1880_ = lean_box(0);
return v___x_1880_;
}
else
{
lean_object* v_val_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
v_val_1881_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1883_ = v___x_1879_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_val_1881_);
lean_dec(v___x_1879_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_stx_1870_);
lean_ctor_set(v___x_1885_, 1, v_val_1881_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(size_t v_sz_1890_, size_t v_i_1891_, lean_object* v_bs_1892_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_usize_dec_lt(v_i_1891_, v_sz_1890_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_bs_1892_);
return v___x_1894_;
}
else
{
lean_object* v_v_1895_; lean_object* v___x_1896_; 
v_v_1895_ = lean_array_uget_borrowed(v_bs_1892_, v_i_1891_);
lean_inc(v_v_1895_);
v___x_1896_ = l_Lean_Doc_OrderedListItemView_of(v_v_1895_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v___x_1897_; 
lean_dec_ref(v_bs_1892_);
v___x_1897_ = lean_box(0);
return v___x_1897_;
}
else
{
lean_object* v_val_1898_; lean_object* v___x_1899_; lean_object* v_bs_x27_1900_; size_t v___x_1901_; size_t v___x_1902_; lean_object* v___x_1903_; 
v_val_1898_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_val_1898_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1899_ = lean_unsigned_to_nat(0u);
v_bs_x27_1900_ = lean_array_uset(v_bs_1892_, v_i_1891_, v___x_1899_);
v___x_1901_ = ((size_t)1ULL);
v___x_1902_ = lean_usize_add(v_i_1891_, v___x_1901_);
v___x_1903_ = lean_array_uset(v_bs_x27_1900_, v_i_1891_, v_val_1898_);
v_i_1891_ = v___x_1902_;
v_bs_1892_ = v___x_1903_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0___boxed(lean_object* v_sz_1905_, lean_object* v_i_1906_, lean_object* v_bs_1907_){
_start:
{
size_t v_sz_boxed_1908_; size_t v_i_boxed_1909_; lean_object* v_res_1910_; 
v_sz_boxed_1908_ = lean_unbox_usize(v_sz_1905_);
lean_dec(v_sz_1905_);
v_i_boxed_1909_ = lean_unbox_usize(v_i_1906_);
lean_dec(v_i_1906_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_boxed_1908_, v_i_boxed_1909_, v_bs_1907_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListView_of(lean_object* v_stx_1918_){
_start:
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = ((lean_object*)(l_Lean_Doc_OrderedListView_of___closed__1));
lean_inc(v_stx_1918_);
v___x_1920_ = l_Lean_Syntax_isOfKind(v_stx_1918_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; 
lean_dec(v_stx_1918_);
v___x_1921_ = lean_box(0);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v_items_1924_; size_t v_sz_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = l_Lean_Syntax_getArg(v_stx_1918_, v___x_1922_);
v_items_1924_ = l_Lean_Syntax_getArgs(v___x_1923_);
lean_dec(v___x_1923_);
v_sz_1925_ = lean_array_size(v_items_1924_);
v___x_1926_ = ((size_t)0ULL);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_1925_, v___x_1926_, v_items_1924_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1928_; 
lean_dec(v_stx_1918_);
v___x_1928_ = lean_box(0);
return v___x_1928_;
}
else
{
lean_object* v_val_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1946_; 
v_val_1929_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1931_ = v___x_1927_;
v_isShared_1932_ = v_isSharedCheck_1946_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_val_1929_);
lean_dec(v___x_1927_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1946_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___y_1934_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = lean_array_get_size(v_val_1929_);
v___x_1942_ = lean_nat_dec_lt(v___x_1922_, v___x_1941_);
if (v___x_1942_ == 0)
{
goto v___jp_1939_;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = lean_array_fget_borrowed(v_val_1929_, v___x_1922_);
lean_inc(v___x_1943_);
v___x_1944_ = l_Lean_Doc_OrderedListItemView_number(v___x_1943_);
if (lean_obj_tag(v___x_1944_) == 0)
{
goto v___jp_1939_;
}
else
{
lean_object* v_val_1945_; 
v_val_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_val_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v___y_1934_ = v_val_1945_;
goto v___jp_1933_;
}
}
v___jp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1935_, 0, v_stx_1918_);
lean_ctor_set(v___x_1935_, 1, v___y_1934_);
lean_ctor_set(v___x_1935_, 2, v_val_1929_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1935_);
v___x_1937_ = v___x_1931_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
v___jp_1939_:
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_unsigned_to_nat(1u);
v___y_1934_ = v___x_1940_;
goto v___jp_1933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(size_t v_sz_1947_, size_t v_i_1948_, lean_object* v_bs_1949_){
_start:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_usize_dec_lt(v_i_1948_, v_sz_1947_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_bs_1949_);
return v___x_1951_;
}
else
{
lean_object* v_v_1952_; lean_object* v___x_1953_; 
v_v_1952_ = lean_array_uget_borrowed(v_bs_1949_, v_i_1948_);
lean_inc(v_v_1952_);
v___x_1953_ = l_Lean_Doc_DescItemView_of(v_v_1952_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v___x_1954_; 
lean_dec_ref(v_bs_1949_);
v___x_1954_ = lean_box(0);
return v___x_1954_;
}
else
{
lean_object* v_val_1955_; lean_object* v___x_1956_; lean_object* v_bs_x27_1957_; size_t v___x_1958_; size_t v___x_1959_; lean_object* v___x_1960_; 
v_val_1955_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1956_ = lean_unsigned_to_nat(0u);
v_bs_x27_1957_ = lean_array_uset(v_bs_1949_, v_i_1948_, v___x_1956_);
v___x_1958_ = ((size_t)1ULL);
v___x_1959_ = lean_usize_add(v_i_1948_, v___x_1958_);
v___x_1960_ = lean_array_uset(v_bs_x27_1957_, v_i_1948_, v_val_1955_);
v_i_1948_ = v___x_1959_;
v_bs_1949_ = v___x_1960_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0___boxed(lean_object* v_sz_1962_, lean_object* v_i_1963_, lean_object* v_bs_1964_){
_start:
{
size_t v_sz_boxed_1965_; size_t v_i_boxed_1966_; lean_object* v_res_1967_; 
v_sz_boxed_1965_ = lean_unbox_usize(v_sz_1962_);
lean_dec(v_sz_1962_);
v_i_boxed_1966_ = lean_unbox_usize(v_i_1963_);
lean_dec(v_i_1963_);
v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_boxed_1965_, v_i_boxed_1966_, v_bs_1964_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescListView_of(lean_object* v_stx_1975_){
_start:
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_Doc_DescListView_of___closed__1));
lean_inc(v_stx_1975_);
v___x_1977_ = l_Lean_Syntax_isOfKind(v_stx_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_stx_1975_);
v___x_1978_ = lean_box(0);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v_items_1981_; size_t v_sz_1982_; size_t v___x_1983_; lean_object* v___x_1984_; 
v___x_1979_ = lean_unsigned_to_nat(0u);
v___x_1980_ = l_Lean_Syntax_getArg(v_stx_1975_, v___x_1979_);
v_items_1981_ = l_Lean_Syntax_getArgs(v___x_1980_);
lean_dec(v___x_1980_);
v_sz_1982_ = lean_array_size(v_items_1981_);
v___x_1983_ = ((size_t)0ULL);
v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_1982_, v___x_1983_, v_items_1981_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v___x_1985_; 
lean_dec(v_stx_1975_);
v___x_1985_ = lean_box(0);
return v___x_1985_;
}
else
{
lean_object* v_val_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1994_; 
v_val_1986_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1988_ = v___x_1984_;
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_val_1986_);
lean_dec(v___x_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_stx_1975_);
lean_ctor_set(v___x_1990_, 1, v_val_1986_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1990_);
v___x_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockquoteView_of(lean_object* v_stx_2002_){
_start:
{
lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = ((lean_object*)(l_Lean_Doc_BlockquoteView_of___closed__1));
lean_inc(v_stx_2002_);
v___x_2004_ = l_Lean_Syntax_isOfKind(v_stx_2002_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec(v_stx_2002_);
v___x_2005_ = lean_box(0);
return v___x_2005_;
}
else
{
lean_object* v___x_2006_; lean_object* v_gt_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v_bs_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2006_ = lean_unsigned_to_nat(0u);
v_gt_2007_ = l_Lean_Syntax_getArg(v_stx_2002_, v___x_2006_);
v___x_2008_ = lean_unsigned_to_nat(1u);
v___x_2009_ = l_Lean_Syntax_getArg(v_stx_2002_, v___x_2008_);
v_bs_2010_ = l_Lean_Syntax_getArgs(v___x_2009_);
lean_dec(v___x_2009_);
v___x_2011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2011_, 0, v_stx_2002_);
lean_ctor_set(v___x_2011_, 1, v_gt_2007_);
lean_ctor_set(v___x_2011_, 2, v_bs_2010_);
v___x_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
return v___x_2012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object* v_v_2013_){
_start:
{
lean_object* v_content_2014_; lean_object* v___x_2015_; 
v_content_2014_ = lean_ctor_get(v_v_2013_, 4);
v___x_2015_ = l_Lean_TSyntax_getVersoCodeBlock(v_content_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock___boxed(lean_object* v_v_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_v_2016_);
lean_dec_ref(v_v_2016_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_of(lean_object* v_stx_2037_){
_start:
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__1));
lean_inc(v_stx_2037_);
v___x_2039_ = l_Lean_Syntax_isOfKind(v_stx_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_dec(v_stx_2037_);
v___x_2040_ = lean_box(0);
return v___x_2040_;
}
else
{
lean_object* v___x_2041_; lean_object* v_openFence_2042_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v_name_2065_; lean_object* v_args_2066_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2041_ = lean_unsigned_to_nat(0u);
v_openFence_2042_ = l_Lean_Syntax_getArg(v_stx_2037_, v___x_2041_);
v___x_2079_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__5));
lean_inc(v_openFence_2042_);
v___x_2080_ = l_Lean_Syntax_isOfKind(v_openFence_2042_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
lean_dec(v_openFence_2042_);
lean_dec(v_stx_2037_);
v___x_2081_ = lean_box(0);
return v___x_2081_;
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2082_ = lean_unsigned_to_nat(1u);
v___x_2083_ = l_Lean_Syntax_getArg(v_stx_2037_, v___x_2082_);
v___x_2084_ = l_Lean_Syntax_isNone(v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2083_);
v___x_2086_ = l_Lean_Syntax_matchesNull(v___x_2083_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; 
lean_dec(v___x_2083_);
lean_dec(v_openFence_2042_);
lean_dec(v_stx_2037_);
v___x_2087_ = lean_box(0);
return v___x_2087_;
}
else
{
lean_object* v_name_2088_; 
v_name_2088_ = l_Lean_Syntax_getArg(v___x_2083_, v___x_2041_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2088_);
v___x_2095_ = l_Lean_Syntax_isOfKind(v_name_2088_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
lean_dec(v_name_2088_);
lean_dec(v___x_2083_);
lean_dec(v_openFence_2042_);
lean_dec(v_stx_2037_);
v___x_2096_ = lean_box(0);
return v___x_2096_;
}
else
{
goto v___jp_2089_;
}
}
else
{
goto v___jp_2089_;
}
v___jp_2089_:
{
lean_object* v___x_2090_; lean_object* v_args_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2090_ = l_Lean_Syntax_getArg(v___x_2083_, v___x_2082_);
lean_dec(v___x_2083_);
v_args_2091_ = l_Lean_Syntax_getArgs(v___x_2090_);
lean_dec(v___x_2090_);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_name_2088_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_args_2091_);
v_name_2065_ = v___x_2092_;
v_args_2066_ = v___x_2093_;
goto v___jp_2064_;
}
}
}
else
{
lean_object* v___x_2097_; 
lean_dec(v___x_2083_);
v___x_2097_ = lean_box(0);
v_name_2065_ = v___x_2097_;
v_args_2066_ = v___x_2097_;
goto v___jp_2064_;
}
}
v___jp_2043_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2048_, 0, v_stx_2037_);
lean_ctor_set(v___x_2048_, 1, v_openFence_2042_);
lean_ctor_set(v___x_2048_, 2, v___y_2044_);
lean_ctor_set(v___x_2048_, 3, v___y_2047_);
lean_ctor_set(v___x_2048_, 4, v___y_2046_);
lean_ctor_set(v___x_2048_, 5, v___y_2045_);
v___x_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
v___jp_2050_:
{
if (lean_obj_tag(v___y_2052_) == 0)
{
lean_object* v___x_2055_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0));
v___y_2044_ = v___y_2051_;
v___y_2045_ = v___y_2053_;
v___y_2046_ = v___y_2054_;
v___y_2047_ = v___x_2055_;
goto v___jp_2043_;
}
else
{
lean_object* v_val_2056_; 
v_val_2056_ = lean_ctor_get(v___y_2052_, 0);
lean_inc(v_val_2056_);
lean_dec_ref_known(v___y_2052_, 1);
v___y_2044_ = v___y_2051_;
v___y_2045_ = v___y_2053_;
v___y_2046_ = v___y_2054_;
v___y_2047_ = v_val_2056_;
goto v___jp_2043_;
}
}
v___jp_2057_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v___y_2060_);
v___x_2063_ = l_Lean_Syntax_setInfo(v___x_2062_, v___y_2061_);
v___y_2051_ = v___y_2058_;
v___y_2052_ = v___y_2059_;
v___y_2053_ = v___y_2060_;
v___y_2054_ = v___x_2063_;
goto v___jp_2050_;
}
v___jp_2064_:
{
lean_object* v___x_2067_; lean_object* v_s_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2067_ = lean_unsigned_to_nat(2u);
v_s_2068_ = l_Lean_Syntax_getArg(v_stx_2037_, v___x_2067_);
v___x_2069_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__3));
lean_inc(v_s_2068_);
v___x_2070_ = l_Lean_Syntax_isOfKind(v_s_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
lean_dec(v_s_2068_);
lean_dec(v_args_2066_);
lean_dec(v_name_2065_);
lean_dec(v_openFence_2042_);
lean_dec(v_stx_2037_);
v___x_2071_ = lean_box(0);
return v___x_2071_;
}
else
{
lean_object* v___x_2072_; lean_object* v_closeFence_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2072_ = lean_unsigned_to_nat(3u);
v_closeFence_2073_ = l_Lean_Syntax_getArg(v_stx_2037_, v___x_2072_);
v___x_2074_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__5));
lean_inc(v_closeFence_2073_);
v___x_2075_ = l_Lean_Syntax_isOfKind(v_closeFence_2073_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; 
lean_dec(v_closeFence_2073_);
lean_dec(v_s_2068_);
lean_dec(v_args_2066_);
lean_dec(v_name_2065_);
lean_dec(v_openFence_2042_);
lean_dec(v_stx_2037_);
v___x_2076_ = lean_box(0);
return v___x_2076_;
}
else
{
uint8_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = 0;
v___x_2078_ = l_Lean_Syntax_getPos_x3f(v_s_2068_, v___x_2077_);
if (lean_obj_tag(v___x_2078_) == 0)
{
v___y_2058_ = v_name_2065_;
v___y_2059_ = v_args_2066_;
v___y_2060_ = v_closeFence_2073_;
v___y_2061_ = v_s_2068_;
goto v___jp_2057_;
}
else
{
lean_dec_ref_known(v___x_2078_, 1);
if (v___x_2039_ == 0)
{
v___y_2058_ = v_name_2065_;
v___y_2059_ = v_args_2066_;
v___y_2060_ = v_closeFence_2073_;
v___y_2061_ = v_s_2068_;
goto v___jp_2057_;
}
else
{
v___y_2051_ = v_name_2065_;
v___y_2052_ = v_args_2066_;
v___y_2053_ = v_closeFence_2073_;
v___y_2054_ = v_s_2068_;
goto v___jp_2050_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DirectiveView_of(lean_object* v_stx_2111_){
_start:
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_Doc_DirectiveView_of___closed__1));
lean_inc(v_stx_2111_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v_stx_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec(v_stx_2111_);
v___x_2114_ = lean_box(0);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; lean_object* v_opener_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v_opener_2116_ = l_Lean_Syntax_getArg(v_stx_2111_, v___x_2115_);
v___x_2117_ = ((lean_object*)(l_Lean_Doc_DirectiveView_of___closed__3));
lean_inc(v_opener_2116_);
v___x_2118_ = l_Lean_Syntax_isOfKind(v_opener_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_dec(v_opener_2116_);
lean_dec(v_stx_2111_);
v___x_2119_ = lean_box(0);
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; lean_object* v_name_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2120_ = lean_unsigned_to_nat(1u);
v_name_2121_ = l_Lean_Syntax_getArg(v_stx_2111_, v___x_2120_);
v___x_2122_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2121_);
v___x_2123_ = l_Lean_Syntax_isOfKind(v_name_2121_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; 
lean_dec(v_name_2121_);
lean_dec(v_opener_2116_);
lean_dec(v_stx_2111_);
v___x_2124_ = lean_box(0);
return v___x_2124_;
}
else
{
lean_object* v___x_2125_; lean_object* v_closer_2126_; uint8_t v___x_2127_; 
v___x_2125_ = lean_unsigned_to_nat(4u);
v_closer_2126_ = l_Lean_Syntax_getArg(v_stx_2111_, v___x_2125_);
lean_inc(v_closer_2126_);
v___x_2127_ = l_Lean_Syntax_isOfKind(v_closer_2126_, v___x_2117_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; 
lean_dec(v_closer_2126_);
lean_dec(v_name_2121_);
lean_dec(v_opener_2116_);
lean_dec(v_stx_2111_);
v___x_2128_ = lean_box(0);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v_bs_2133_; lean_object* v_args_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2129_ = lean_unsigned_to_nat(2u);
v___x_2130_ = l_Lean_Syntax_getArg(v_stx_2111_, v___x_2129_);
v___x_2131_ = lean_unsigned_to_nat(3u);
v___x_2132_ = l_Lean_Syntax_getArg(v_stx_2111_, v___x_2131_);
v_bs_2133_ = l_Lean_Syntax_getArgs(v___x_2132_);
lean_dec(v___x_2132_);
v_args_2134_ = l_Lean_Syntax_getArgs(v___x_2130_);
lean_dec(v___x_2130_);
v___x_2135_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2135_, 0, v_stx_2111_);
lean_ctor_set(v___x_2135_, 1, v_opener_2116_);
lean_ctor_set(v___x_2135_, 2, v_name_2121_);
lean_ctor_set(v___x_2135_, 3, v_args_2134_);
lean_ctor_set(v___x_2135_, 4, v_bs_2133_);
lean_ctor_set(v___x_2135_, 5, v_closer_2126_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
return v___x_2136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CommandView_of(lean_object* v_stx_2144_){
_start:
{
lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_Lean_Doc_CommandView_of___closed__1));
lean_inc(v_stx_2144_);
v___x_2146_ = l_Lean_Syntax_isOfKind(v_stx_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_dec(v_stx_2144_);
v___x_2147_ = lean_box(0);
return v___x_2147_;
}
else
{
lean_object* v___x_2148_; lean_object* v_name_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2148_ = lean_unsigned_to_nat(1u);
v_name_2149_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2148_);
v___x_2150_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2149_);
v___x_2151_ = l_Lean_Syntax_isOfKind(v_name_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_dec(v_name_2149_);
lean_dec(v_stx_2144_);
v___x_2152_ = lean_box(0);
return v___x_2152_;
}
else
{
lean_object* v___x_2153_; lean_object* v_braceOpen_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v_braceClose_2158_; lean_object* v_args_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2153_ = lean_unsigned_to_nat(0u);
v_braceOpen_2154_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2153_);
v___x_2155_ = lean_unsigned_to_nat(2u);
v___x_2156_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2155_);
v___x_2157_ = lean_unsigned_to_nat(3u);
v_braceClose_2158_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2157_);
v_args_2159_ = l_Lean_Syntax_getArgs(v___x_2156_);
lean_dec(v___x_2156_);
v___x_2160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2160_, 0, v_stx_2144_);
lean_ctor_set(v___x_2160_, 1, v_braceOpen_2154_);
lean_ctor_set(v___x_2160_, 2, v_name_2149_);
lean_ctor_set(v___x_2160_, 3, v_args_2159_);
lean_ctor_set(v___x_2160_, 4, v_braceClose_2158_);
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_HeaderView_of(lean_object* v_stx_2175_){
_start:
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_Doc_HeaderView_of___closed__1));
lean_inc(v_stx_2175_);
v___x_2177_ = l_Lean_Syntax_isOfKind(v_stx_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; 
lean_dec(v_stx_2175_);
v___x_2178_ = lean_box(0);
return v___x_2178_;
}
else
{
lean_object* v___x_2179_; lean_object* v_marker_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v_marker_2180_ = l_Lean_Syntax_getArg(v_stx_2175_, v___x_2179_);
v___x_2181_ = ((lean_object*)(l_Lean_Doc_HeaderView_of___closed__3));
lean_inc(v_marker_2180_);
v___x_2182_ = l_Lean_Syntax_isOfKind(v_marker_2180_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
lean_dec(v_marker_2180_);
lean_dec(v_stx_2175_);
v___x_2183_ = lean_box(0);
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_content_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = l_Lean_Syntax_getArg(v_stx_2175_, v___x_2184_);
v_content_2186_ = l_Lean_Syntax_getArgs(v___x_2185_);
lean_dec(v___x_2185_);
v___x_2187_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_2180_);
v___x_2188_ = lean_string_length(v___x_2187_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = lean_nat_sub(v___x_2188_, v___x_2184_);
v___x_2190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2190_, 0, v_stx_2175_);
lean_ctor_set(v___x_2190_, 1, v_marker_2180_);
lean_ctor_set(v___x_2190_, 2, v___x_2189_);
lean_ctor_set(v___x_2190_, 3, v_content_2186_);
v___x_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
return v___x_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName(lean_object* v_v_2192_){
_start:
{
lean_object* v_name_2193_; lean_object* v___x_2194_; 
v_name_2193_ = lean_ctor_get(v_v_2192_, 2);
v___x_2194_ = l_Lean_TSyntax_getVersoRefName(v_name_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName___boxed(lean_object* v_v_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Doc_LinkRefView_getName(v_v_2195_);
lean_dec_ref(v_v_2195_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object* v_v_2197_){
_start:
{
lean_object* v_url_2198_; lean_object* v___x_2199_; 
v_url_2198_ = lean_ctor_get(v_v_2197_, 4);
v___x_2199_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_url_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl___boxed(lean_object* v_v_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_Doc_LinkRefView_getUrl(v_v_2200_);
lean_dec_ref(v_v_2200_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_of(lean_object* v_stx_2215_){
_start:
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__1));
lean_inc(v_stx_2215_);
v___x_2217_ = l_Lean_Syntax_isOfKind(v_stx_2215_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; 
lean_dec(v_stx_2215_);
v___x_2218_ = lean_box(0);
return v___x_2218_;
}
else
{
lean_object* v___x_2219_; lean_object* v_name_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2219_ = lean_unsigned_to_nat(1u);
v_name_2220_ = l_Lean_Syntax_getArg(v_stx_2215_, v___x_2219_);
v___x_2221_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_2220_);
v___x_2222_ = l_Lean_Syntax_isOfKind(v_name_2220_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_dec(v_name_2220_);
lean_dec(v_stx_2215_);
v___x_2223_ = lean_box(0);
return v___x_2223_;
}
else
{
lean_object* v___x_2224_; lean_object* v_url_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2224_ = lean_unsigned_to_nat(3u);
v_url_2225_ = l_Lean_Syntax_getArg(v_stx_2215_, v___x_2224_);
v___x_2226_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__3));
lean_inc(v_url_2225_);
v___x_2227_ = l_Lean_Syntax_isOfKind(v_url_2225_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; 
lean_dec(v_url_2225_);
lean_dec(v_name_2220_);
lean_dec(v_stx_2215_);
v___x_2228_ = lean_box(0);
return v___x_2228_;
}
else
{
lean_object* v___x_2229_; lean_object* v_opener_2230_; lean_object* v___x_2231_; lean_object* v_closer_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2229_ = lean_unsigned_to_nat(0u);
v_opener_2230_ = l_Lean_Syntax_getArg(v_stx_2215_, v___x_2229_);
v___x_2231_ = lean_unsigned_to_nat(2u);
v_closer_2232_ = l_Lean_Syntax_getArg(v_stx_2215_, v___x_2231_);
v___x_2233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2233_, 0, v_stx_2215_);
lean_ctor_set(v___x_2233_, 1, v_opener_2230_);
lean_ctor_set(v___x_2233_, 2, v_name_2220_);
lean_ctor_set(v___x_2233_, 3, v_closer_2232_);
lean_ctor_set(v___x_2233_, 4, v_url_2225_);
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object* v_v_2235_){
_start:
{
lean_object* v_name_2236_; lean_object* v___x_2237_; 
v_name_2236_ = lean_ctor_get(v_v_2235_, 2);
v___x_2237_ = l_Lean_TSyntax_getVersoRefName(v_name_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName___boxed(lean_object* v_v_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Doc_FootnoteRefView_getName(v_v_2238_);
lean_dec_ref(v_v_2238_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_of(lean_object* v_stx_2247_){
_start:
{
lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2248_ = ((lean_object*)(l_Lean_Doc_FootnoteRefView_of___closed__1));
lean_inc(v_stx_2247_);
v___x_2249_ = l_Lean_Syntax_isOfKind(v_stx_2247_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; 
lean_dec(v_stx_2247_);
v___x_2250_ = lean_box(0);
return v___x_2250_;
}
else
{
lean_object* v___x_2251_; lean_object* v_name_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2251_ = lean_unsigned_to_nat(1u);
v_name_2252_ = l_Lean_Syntax_getArg(v_stx_2247_, v___x_2251_);
v___x_2253_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_2252_);
v___x_2254_ = l_Lean_Syntax_isOfKind(v_name_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; 
lean_dec(v_name_2252_);
lean_dec(v_stx_2247_);
v___x_2255_ = lean_box(0);
return v___x_2255_;
}
else
{
lean_object* v___x_2256_; lean_object* v_opener_2257_; lean_object* v___x_2258_; lean_object* v_closer_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_content_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2256_ = lean_unsigned_to_nat(0u);
v_opener_2257_ = l_Lean_Syntax_getArg(v_stx_2247_, v___x_2256_);
v___x_2258_ = lean_unsigned_to_nat(2u);
v_closer_2259_ = l_Lean_Syntax_getArg(v_stx_2247_, v___x_2258_);
v___x_2260_ = lean_unsigned_to_nat(3u);
v___x_2261_ = l_Lean_Syntax_getArg(v_stx_2247_, v___x_2260_);
v_content_2262_ = l_Lean_Syntax_getArgs(v___x_2261_);
lean_dec(v___x_2261_);
v___x_2263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2263_, 0, v_stx_2247_);
lean_ctor_set(v___x_2263_, 1, v_opener_2257_);
lean_ctor_set(v___x_2263_, 2, v_name_2252_);
lean_ctor_set(v___x_2263_, 3, v_closer_2259_);
lean_ctor_set(v___x_2263_, 4, v_content_2262_);
v___x_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
return v___x_2264_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(size_t v_sz_2265_, size_t v_i_2266_, lean_object* v_bs_2267_){
_start:
{
uint8_t v___x_2268_; 
v___x_2268_ = lean_usize_dec_lt(v_i_2266_, v_sz_2265_);
if (v___x_2268_ == 0)
{
return v_bs_2267_;
}
else
{
lean_object* v_v_2269_; lean_object* v___x_2270_; lean_object* v_bs_x27_2271_; size_t v___x_2272_; size_t v___x_2273_; lean_object* v___x_2274_; 
v_v_2269_ = lean_array_uget(v_bs_2267_, v_i_2266_);
v___x_2270_ = lean_unsigned_to_nat(0u);
v_bs_x27_2271_ = lean_array_uset(v_bs_2267_, v_i_2266_, v___x_2270_);
v___x_2272_ = ((size_t)1ULL);
v___x_2273_ = lean_usize_add(v_i_2266_, v___x_2272_);
v___x_2274_ = lean_array_uset(v_bs_x27_2271_, v_i_2266_, v_v_2269_);
v_i_2266_ = v___x_2273_;
v_bs_2267_ = v___x_2274_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0___boxed(lean_object* v_sz_2276_, lean_object* v_i_2277_, lean_object* v_bs_2278_){
_start:
{
size_t v_sz_boxed_2279_; size_t v_i_boxed_2280_; lean_object* v_res_2281_; 
v_sz_boxed_2279_ = lean_unbox_usize(v_sz_2276_);
lean_dec(v_sz_2276_);
v_i_boxed_2280_ = lean_unbox_usize(v_i_2277_);
lean_dec(v_i_2277_);
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_boxed_2279_, v_i_boxed_2280_, v_bs_2278_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields(lean_object* v_v_2282_){
_start:
{
lean_object* v_contents_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; size_t v_sz_2287_; size_t v___x_2288_; lean_object* v___x_2289_; 
v_contents_2283_ = lean_ctor_get(v_v_2282_, 2);
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2285_ = l_Lean_Syntax_getArg(v_contents_2283_, v___x_2284_);
v___x_2286_ = l_Lean_Syntax_getSepArgs(v___x_2285_);
lean_dec(v___x_2285_);
v_sz_2287_ = lean_array_size(v___x_2286_);
v___x_2288_ = ((size_t)0ULL);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_2287_, v___x_2288_, v___x_2286_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields___boxed(lean_object* v_v_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Doc_MetadataView_fields(v_v_2290_);
lean_dec_ref(v_v_2290_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_of(lean_object* v_stx_2306_){
_start:
{
lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = ((lean_object*)(l_Lean_Doc_MetadataView_of___closed__1));
lean_inc(v_stx_2306_);
v___x_2308_ = l_Lean_Syntax_isOfKind(v_stx_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; 
lean_dec(v_stx_2306_);
v___x_2309_ = lean_box(0);
return v___x_2309_;
}
else
{
lean_object* v___x_2310_; lean_object* v_contents_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2310_ = lean_unsigned_to_nat(1u);
v_contents_2311_ = l_Lean_Syntax_getArg(v_stx_2306_, v___x_2310_);
v___x_2312_ = ((lean_object*)(l_Lean_Doc_MetadataView_of___closed__4));
lean_inc(v_contents_2311_);
v___x_2313_ = l_Lean_Syntax_isOfKind(v_contents_2311_, v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; 
lean_dec(v_contents_2311_);
lean_dec(v_stx_2306_);
v___x_2314_ = lean_box(0);
return v___x_2314_;
}
else
{
lean_object* v___x_2315_; lean_object* v_opener_2316_; lean_object* v___x_2317_; lean_object* v_closer_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2315_ = lean_unsigned_to_nat(0u);
v_opener_2316_ = l_Lean_Syntax_getArg(v_stx_2306_, v___x_2315_);
v___x_2317_ = lean_unsigned_to_nat(2u);
v_closer_2318_ = l_Lean_Syntax_getArg(v_stx_2306_, v___x_2317_);
v___x_2319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2319_, 0, v_stx_2306_);
lean_ctor_set(v___x_2319_, 1, v_opener_2316_);
lean_ctor_set(v___x_2319_, 2, v_contents_2311_);
lean_ctor_set(v___x_2319_, 3, v_closer_2318_);
v___x_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
return v___x_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx(lean_object* v_x_2321_){
_start:
{
switch(lean_obj_tag(v_x_2321_))
{
case 0:
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_unsigned_to_nat(0u);
return v___x_2322_;
}
case 1:
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_unsigned_to_nat(1u);
return v___x_2323_;
}
case 2:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_unsigned_to_nat(2u);
return v___x_2324_;
}
case 3:
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_unsigned_to_nat(3u);
return v___x_2325_;
}
case 4:
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_unsigned_to_nat(4u);
return v___x_2326_;
}
case 5:
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_unsigned_to_nat(5u);
return v___x_2327_;
}
case 6:
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_unsigned_to_nat(6u);
return v___x_2328_;
}
case 7:
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_unsigned_to_nat(7u);
return v___x_2329_;
}
case 8:
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_unsigned_to_nat(8u);
return v___x_2330_;
}
case 9:
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_unsigned_to_nat(9u);
return v___x_2331_;
}
case 10:
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_unsigned_to_nat(10u);
return v___x_2332_;
}
default: 
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_unsigned_to_nat(11u);
return v___x_2333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___boxed(lean_object* v_x_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Doc_BlockView_ctorIdx(v_x_2334_);
lean_dec_ref(v_x_2334_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___redArg(lean_object* v_t_2336_, lean_object* v_k_2337_){
_start:
{
lean_object* v_view_2338_; lean_object* v___x_2339_; 
v_view_2338_ = lean_ctor_get(v_t_2336_, 0);
lean_inc_ref(v_view_2338_);
lean_dec_ref(v_t_2336_);
v___x_2339_ = lean_apply_1(v_k_2337_, v_view_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim(lean_object* v_motive_2340_, lean_object* v_ctorIdx_2341_, lean_object* v_t_2342_, lean_object* v_h_2343_, lean_object* v_k_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2342_, v_k_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___boxed(lean_object* v_motive_2346_, lean_object* v_ctorIdx_2347_, lean_object* v_t_2348_, lean_object* v_h_2349_, lean_object* v_k_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_Doc_BlockView_ctorElim(v_motive_2346_, v_ctorIdx_2347_, v_t_2348_, v_h_2349_, v_k_2350_);
lean_dec(v_ctorIdx_2347_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim___redArg(lean_object* v_t_2352_, lean_object* v_para_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2352_, v_para_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim(lean_object* v_motive_2355_, lean_object* v_t_2356_, lean_object* v_h_2357_, lean_object* v_para_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2356_, v_para_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim___redArg(lean_object* v_t_2360_, lean_object* v_ul_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2360_, v_ul_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim(lean_object* v_motive_2363_, lean_object* v_t_2364_, lean_object* v_h_2365_, lean_object* v_ul_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2364_, v_ul_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim___redArg(lean_object* v_t_2368_, lean_object* v_ol_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2368_, v_ol_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim(lean_object* v_motive_2371_, lean_object* v_t_2372_, lean_object* v_h_2373_, lean_object* v_ol_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2372_, v_ol_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim___redArg(lean_object* v_t_2376_, lean_object* v_dl_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2376_, v_dl_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim(lean_object* v_motive_2379_, lean_object* v_t_2380_, lean_object* v_h_2381_, lean_object* v_dl_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2380_, v_dl_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim___redArg(lean_object* v_t_2384_, lean_object* v_blockquote_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2384_, v_blockquote_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim(lean_object* v_motive_2387_, lean_object* v_t_2388_, lean_object* v_h_2389_, lean_object* v_blockquote_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2388_, v_blockquote_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim___redArg(lean_object* v_t_2392_, lean_object* v_codeblock_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2392_, v_codeblock_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim(lean_object* v_motive_2395_, lean_object* v_t_2396_, lean_object* v_h_2397_, lean_object* v_codeblock_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2396_, v_codeblock_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim___redArg(lean_object* v_t_2400_, lean_object* v_directive_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2400_, v_directive_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim(lean_object* v_motive_2403_, lean_object* v_t_2404_, lean_object* v_h_2405_, lean_object* v_directive_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2404_, v_directive_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim___redArg(lean_object* v_t_2408_, lean_object* v_command_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2408_, v_command_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim(lean_object* v_motive_2411_, lean_object* v_t_2412_, lean_object* v_h_2413_, lean_object* v_command_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2412_, v_command_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim___redArg(lean_object* v_t_2416_, lean_object* v_header_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2416_, v_header_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim(lean_object* v_motive_2419_, lean_object* v_t_2420_, lean_object* v_h_2421_, lean_object* v_header_2422_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2420_, v_header_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim___redArg(lean_object* v_t_2424_, lean_object* v_linkRef_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2424_, v_linkRef_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim(lean_object* v_motive_2427_, lean_object* v_t_2428_, lean_object* v_h_2429_, lean_object* v_linkRef_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2428_, v_linkRef_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim___redArg(lean_object* v_t_2432_, lean_object* v_footnoteRef_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2432_, v_footnoteRef_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim(lean_object* v_motive_2435_, lean_object* v_t_2436_, lean_object* v_h_2437_, lean_object* v_footnoteRef_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2436_, v_footnoteRef_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim___redArg(lean_object* v_t_2440_, lean_object* v_metadata_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2440_, v_metadata_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim(lean_object* v_motive_2443_, lean_object* v_t_2444_, lean_object* v_h_2445_, lean_object* v_metadata_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2444_, v_metadata_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeParaViewBlockView___lam__0(lean_object* v_view_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_view_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0(lean_object* v_view_2456_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_view_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0(lean_object* v_view_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2461_, 0, v_view_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDescListViewBlockView___lam__0(lean_object* v_view_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2465_, 0, v_view_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0(lean_object* v_view_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_view_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0(lean_object* v_view_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_view_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0(lean_object* v_view_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2477_, 0, v_view_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCommandViewBlockView___lam__0(lean_object* v_view_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_view_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___lam__0(lean_object* v_view_2484_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_view_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0(lean_object* v_view_2488_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_view_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0(lean_object* v_view_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2493_, 0, v_view_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___lam__0(lean_object* v_view_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_view_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx(lean_object* v_x_2500_){
_start:
{
lean_object* v_view_2501_; lean_object* v_stx_2502_; 
v_view_2501_ = lean_ctor_get(v_x_2500_, 0);
v_stx_2502_ = lean_ctor_get(v_view_2501_, 0);
lean_inc(v_stx_2502_);
return v_stx_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx___boxed(lean_object* v_x_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_Doc_BlockView_stx(v_x_2503_);
lean_dec_ref(v_x_2503_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_of(lean_object* v_stx_2505_){
_start:
{
lean_object* v___x_2506_; 
lean_inc(v_stx_2505_);
v___x_2506_ = l_Lean_Doc_ParaView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v___x_2507_; 
lean_inc(v_stx_2505_);
v___x_2507_ = l_Lean_Doc_UnorderedListView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v___x_2508_; 
lean_inc(v_stx_2505_);
v___x_2508_ = l_Lean_Doc_OrderedListView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v___x_2509_; 
lean_inc(v_stx_2505_);
v___x_2509_ = l_Lean_Doc_DescListView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v___x_2510_; 
lean_inc(v_stx_2505_);
v___x_2510_ = l_Lean_Doc_BlockquoteView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v___x_2511_; 
lean_inc(v_stx_2505_);
v___x_2511_ = l_Lean_Doc_CodeBlockView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v___x_2512_; 
lean_inc(v_stx_2505_);
v___x_2512_ = l_Lean_Doc_DirectiveView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v___x_2513_; 
lean_inc(v_stx_2505_);
v___x_2513_ = l_Lean_Doc_CommandView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v___x_2514_; 
lean_inc(v_stx_2505_);
v___x_2514_ = l_Lean_Doc_HeaderView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v___x_2515_; 
lean_inc(v_stx_2505_);
v___x_2515_ = l_Lean_Doc_LinkRefView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v___x_2516_; 
lean_inc(v_stx_2505_);
v___x_2516_ = l_Lean_Doc_FootnoteRefView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Doc_MetadataView_of(v_stx_2505_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_box(0);
return v___x_2518_;
}
else
{
lean_object* v_val_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2527_; 
v_val_2519_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2521_ = v___x_2517_;
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_val_2519_);
lean_dec(v___x_2517_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2523_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2523_, 0, v_val_2519_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2523_);
v___x_2525_ = v___x_2521_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v_val_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v_stx_2505_);
v_val_2528_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2530_ = v___x_2516_;
v_isShared_2531_ = v_isSharedCheck_2536_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_val_2528_);
lean_dec(v___x_2516_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2536_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2532_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_val_2528_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v___x_2532_);
v___x_2534_ = v___x_2530_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_val_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_stx_2505_);
v_val_2537_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2539_ = v___x_2515_;
v_isShared_2540_ = v_isSharedCheck_2545_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_val_2537_);
lean_dec(v___x_2515_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2545_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2541_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2541_, 0, v_val_2537_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2541_);
v___x_2543_ = v___x_2539_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v_val_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_stx_2505_);
v_val_2546_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2548_ = v___x_2514_;
v_isShared_2549_ = v_isSharedCheck_2554_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_val_2546_);
lean_dec(v___x_2514_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2554_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; lean_object* v___x_2552_; 
v___x_2550_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_val_2546_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2550_);
v___x_2552_ = v___x_2548_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
else
{
lean_object* v_val_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_stx_2505_);
v_val_2555_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2557_ = v___x_2513_;
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_val_2555_);
lean_dec(v___x_2513_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2559_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_val_2555_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2559_);
v___x_2561_ = v___x_2557_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
else
{
lean_object* v_val_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_stx_2505_);
v_val_2564_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2566_ = v___x_2512_;
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_val_2564_);
lean_dec(v___x_2512_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2568_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_val_2564_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2568_);
v___x_2570_ = v___x_2566_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
else
{
lean_object* v_val_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_stx_2505_);
v_val_2573_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2575_ = v___x_2511_;
v_isShared_2576_ = v_isSharedCheck_2581_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_val_2573_);
lean_dec(v___x_2511_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2581_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2577_, 0, v_val_2573_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2577_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v_val_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v_stx_2505_);
v_val_2582_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2584_ = v___x_2510_;
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_val_2582_);
lean_dec(v___x_2510_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2590_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_val_2582_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2586_);
v___x_2588_ = v___x_2584_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v_val_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_stx_2505_);
v_val_2591_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2593_ = v___x_2509_;
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_val_2591_);
lean_dec(v___x_2509_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_val_2591_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2595_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_val_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2608_; 
lean_dec(v_stx_2505_);
v_val_2600_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2602_ = v___x_2508_;
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_val_2600_);
lean_dec(v___x_2508_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2604_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2604_, 0, v_val_2600_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2604_);
v___x_2606_ = v___x_2602_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
else
{
lean_object* v_val_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_stx_2505_);
v_val_2609_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2611_ = v___x_2507_;
v_isShared_2612_ = v_isSharedCheck_2617_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_val_2609_);
lean_dec(v___x_2507_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2617_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2613_, 0, v_val_2609_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2613_);
v___x_2615_ = v___x_2611_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v_val_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_stx_2505_);
v_val_2618_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2620_ = v___x_2506_;
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_val_2618_);
lean_dec(v___x_2506_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2622_, 0, v_val_2618_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2622_);
v___x_2624_ = v___x_2620_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
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
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoInline_view(lean_object* v_stx_2627_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_Doc_InlineView_of(v_stx_2627_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v___x_2629_; 
v___x_2629_ = ((lean_object*)(l_Lean_Doc_instInhabitedInlineView_default));
return v___x_2629_;
}
else
{
lean_object* v_val_2630_; 
v_val_2630_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_val_2630_);
lean_dec_ref_known(v___x_2628_, 1);
return v_val_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoBlock_view(lean_object* v_stx_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_Doc_BlockView_of(v_stx_2631_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v___x_2633_; 
v___x_2633_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlockView_default));
return v___x_2633_;
}
else
{
lean_object* v_val_2634_; 
v_val_2634_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_val_2634_);
lean_dec_ref_known(v___x_2632_, 1);
return v_val_2634_;
}
}
}
lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_View(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1 = _init_l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1);
l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1 = _init_l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1);
l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1 = _init_l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_View(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_View(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_View(builtin);
}
#ifdef __cplusplus
}
#endif
