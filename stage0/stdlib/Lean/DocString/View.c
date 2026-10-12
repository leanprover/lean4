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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Doc_ArgValView_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
lean_object* v_lit_7_; lean_object* v_value_8_; lean_object* v___x_9_; 
v_lit_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_lit_7_);
v_value_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_value_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_lit_7_, v_value_8_);
return v___x_9_;
}
case 1:
{
lean_object* v_x_10_; lean_object* v___x_11_; 
v_x_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_x_10_);
lean_dec_ref_known(v_t_5_, 1);
v___x_11_ = lean_apply_1(v_k_6_, v_x_10_);
return v___x_11_;
}
default: 
{
lean_object* v_lit_12_; lean_object* v_value_13_; lean_object* v___x_14_; 
v_lit_12_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_lit_12_);
v_value_13_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_value_13_);
lean_dec_ref_known(v_t_5_, 2);
v___x_14_ = lean_apply_2(v_k_6_, v_lit_12_, v_value_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Doc_ArgValView_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_str_elim___redArg(lean_object* v_t_27_, lean_object* v_str_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_27_, v_str_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_str_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_str_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_31_, v_str_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_name_elim___redArg(lean_object* v_t_35_, lean_object* v_name_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_35_, v_name_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_name_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_name_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_39_, v_name_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_num_elim___redArg(lean_object* v_t_43_, lean_object* v_num_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_43_, v_num_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_num_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_num_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_47_, v_num_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_of(lean_object* v_stx_82_){
_start:
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__5));
lean_inc(v_stx_82_);
v___x_84_ = l_Lean_Syntax_isOfKind(v_stx_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__7));
lean_inc(v_stx_82_);
v___x_86_ = l_Lean_Syntax_isOfKind(v_stx_82_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__9));
lean_inc(v_stx_82_);
v___x_88_ = l_Lean_Syntax_isOfKind(v_stx_82_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
lean_dec(v_stx_82_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
else
{
lean_object* v___x_90_; lean_object* v_s_91_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v_s_91_ = l_Lean_Syntax_getArg(v_stx_82_, v___x_90_);
lean_dec(v_stx_82_);
if (v___x_86_ == 0)
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__10));
lean_inc(v_s_91_);
v___x_97_ = l_Lean_Syntax_isOfKind(v_s_91_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec(v_s_91_);
v___x_98_ = lean_box(0);
return v___x_98_;
}
else
{
goto v___jp_92_;
}
}
else
{
goto v___jp_92_;
}
v___jp_92_:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = l_Lean_TSyntax_getString(v_s_91_);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_s_91_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
}
else
{
lean_object* v___x_99_; lean_object* v_n_100_; 
v___x_99_ = lean_unsigned_to_nat(0u);
v_n_100_ = l_Lean_Syntax_getArg(v_stx_82_, v___x_99_);
lean_dec(v_stx_82_);
if (v___x_84_ == 0)
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__11));
lean_inc(v_n_100_);
v___x_106_ = l_Lean_Syntax_isOfKind(v_n_100_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_dec(v_n_100_);
v___x_107_ = lean_box(0);
return v___x_107_;
}
else
{
goto v___jp_101_;
}
}
else
{
goto v___jp_101_;
}
v___jp_101_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = l_Lean_TSyntax_getNat(v_n_100_);
v___x_103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_103_, 0, v_n_100_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
}
else
{
lean_object* v___x_108_; lean_object* v_x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_108_ = lean_unsigned_to_nat(0u);
v_x_109_ = l_Lean_Syntax_getArg(v_stx_82_, v___x_108_);
lean_dec(v_stx_82_);
v___x_110_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_109_);
v___x_111_ = l_Lean_Syntax_isOfKind(v_x_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
lean_dec(v_x_109_);
v___x_112_ = lean_box(0);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v_x_109_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx___impl(lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_tag_nat(v_x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx___impl___boxed(lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Doc_ArgView_ctorIdx___impl(v_x_117_);
lean_dec_ref(v_x_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___redArg(lean_object* v_t_119_, lean_object* v_k_120_){
_start:
{
switch(lean_obj_tag(v_t_119_))
{
case 0:
{
lean_object* v_stx_121_; lean_object* v_val_122_; lean_object* v___x_123_; 
v_stx_121_ = lean_ctor_get(v_t_119_, 0);
lean_inc(v_stx_121_);
v_val_122_ = lean_ctor_get(v_t_119_, 1);
lean_inc(v_val_122_);
lean_dec_ref_known(v_t_119_, 2);
v___x_123_ = lean_apply_2(v_k_120_, v_stx_121_, v_val_122_);
return v___x_123_;
}
case 1:
{
lean_object* v_stx_124_; lean_object* v_parens_125_; lean_object* v_name_126_; lean_object* v_assign_127_; lean_object* v_val_128_; lean_object* v___x_129_; 
v_stx_124_ = lean_ctor_get(v_t_119_, 0);
lean_inc(v_stx_124_);
v_parens_125_ = lean_ctor_get(v_t_119_, 1);
lean_inc(v_parens_125_);
v_name_126_ = lean_ctor_get(v_t_119_, 2);
lean_inc(v_name_126_);
v_assign_127_ = lean_ctor_get(v_t_119_, 3);
lean_inc(v_assign_127_);
v_val_128_ = lean_ctor_get(v_t_119_, 4);
lean_inc(v_val_128_);
lean_dec_ref_known(v_t_119_, 5);
v___x_129_ = lean_apply_5(v_k_120_, v_stx_124_, v_parens_125_, v_name_126_, v_assign_127_, v_val_128_);
return v___x_129_;
}
default: 
{
lean_object* v_stx_130_; lean_object* v_sign_131_; lean_object* v_name_132_; uint8_t v_isOn_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_stx_130_ = lean_ctor_get(v_t_119_, 0);
lean_inc(v_stx_130_);
v_sign_131_ = lean_ctor_get(v_t_119_, 1);
lean_inc(v_sign_131_);
v_name_132_ = lean_ctor_get(v_t_119_, 2);
lean_inc(v_name_132_);
v_isOn_133_ = lean_ctor_get_uint8(v_t_119_, sizeof(void*)*3);
lean_dec_ref_known(v_t_119_, 3);
v___x_134_ = lean_box(v_isOn_133_);
v___x_135_ = lean_apply_4(v_k_120_, v_stx_130_, v_sign_131_, v_name_132_, v___x_134_);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim(lean_object* v_motive_136_, lean_object* v_ctorIdx_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_k_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_138_, v_k_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___boxed(lean_object* v_motive_142_, lean_object* v_ctorIdx_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_k_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Doc_ArgView_ctorElim(v_motive_142_, v_ctorIdx_143_, v_t_144_, v_h_145_, v_k_146_);
lean_dec(v_ctorIdx_143_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim___redArg(lean_object* v_t_148_, lean_object* v_anon_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_148_, v_anon_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim(lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_anon_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_152_, v_anon_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim___redArg(lean_object* v_t_156_, lean_object* v_named_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_156_, v_named_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim(lean_object* v_motive_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_named_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_160_, v_named_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim___redArg(lean_object* v_t_164_, lean_object* v_flag_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_164_, v_flag_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim(lean_object* v_motive_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_flag_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_168_, v_flag_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx(lean_object* v_x_172_){
_start:
{
lean_object* v_stx_173_; 
v_stx_173_ = lean_ctor_get(v_x_172_, 0);
lean_inc(v_stx_173_);
return v_stx_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx___boxed(lean_object* v_x_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Doc_ArgView_stx(v_x_174_);
lean_dec_ref(v_x_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_of(lean_object* v_stx_212_){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__2));
lean_inc(v_stx_212_);
v___x_214_ = l_Lean_Syntax_isOfKind(v_stx_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__4));
lean_inc(v_stx_212_);
v___x_216_ = l_Lean_Syntax_isOfKind(v_stx_212_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__6));
lean_inc(v_stx_212_);
v___x_218_ = l_Lean_Syntax_isOfKind(v_stx_212_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__8));
lean_inc(v_stx_212_);
v___x_220_ = l_Lean_Syntax_isOfKind(v_stx_212_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__10));
lean_inc(v_stx_212_);
v___x_222_ = l_Lean_Syntax_isOfKind(v_stx_212_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_dec(v_stx_212_);
v___x_223_ = lean_box(0);
return v___x_223_;
}
else
{
lean_object* v___x_224_; lean_object* v_tk_225_; lean_object* v___x_226_; lean_object* v_x_227_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v_tk_225_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_224_);
v___x_226_ = lean_unsigned_to_nat(1u);
v_x_227_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_226_);
if (v___x_220_ == 0)
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_227_);
v___x_232_ = l_Lean_Syntax_isOfKind(v_x_227_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
lean_dec(v_x_227_);
lean_dec(v_tk_225_);
lean_dec(v_stx_212_);
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
goto v___jp_228_;
}
}
else
{
goto v___jp_228_;
}
v___jp_228_:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_229_, 0, v_stx_212_);
lean_ctor_set(v___x_229_, 1, v_tk_225_);
lean_ctor_set(v___x_229_, 2, v_x_227_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*3, v___x_220_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
}
else
{
lean_object* v___x_234_; lean_object* v_tk_235_; lean_object* v___x_236_; lean_object* v_x_237_; 
v___x_234_ = lean_unsigned_to_nat(0u);
v_tk_235_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_234_);
v___x_236_ = lean_unsigned_to_nat(1u);
v_x_237_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_236_);
if (v___x_218_ == 0)
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_237_);
v___x_242_ = l_Lean_Syntax_isOfKind(v_x_237_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
lean_dec(v_x_237_);
lean_dec(v_tk_235_);
lean_dec(v_stx_212_);
v___x_243_ = lean_box(0);
return v___x_243_;
}
else
{
goto v___jp_238_;
}
}
else
{
goto v___jp_238_;
}
v___jp_238_:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_239_, 0, v_stx_212_);
lean_ctor_set(v___x_239_, 1, v_tk_235_);
lean_ctor_set(v___x_239_, 2, v_x_237_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*3, v___x_220_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
else
{
lean_object* v___x_244_; lean_object* v_x_245_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v_x_245_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_244_);
if (v___x_216_ == 0)
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_245_);
v___x_255_ = l_Lean_Syntax_isOfKind(v_x_245_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v_x_245_);
lean_dec(v_stx_212_);
v___x_256_ = lean_box(0);
return v___x_256_;
}
else
{
goto v___jp_246_;
}
}
else
{
goto v___jp_246_;
}
v___jp_246_:
{
lean_object* v___x_247_; lean_object* v_eq_248_; lean_object* v___x_249_; lean_object* v_v_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_247_ = lean_unsigned_to_nat(1u);
v_eq_248_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_247_);
v___x_249_ = lean_unsigned_to_nat(2u);
v_v_250_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_249_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(v___x_252_, 0, v_stx_212_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_ctor_set(v___x_252_, 2, v_x_245_);
lean_ctor_set(v___x_252_, 3, v_eq_248_);
lean_ctor_set(v___x_252_, 4, v_v_250_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
}
else
{
lean_object* v___x_257_; lean_object* v_po_258_; lean_object* v___x_259_; lean_object* v_x_260_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v_po_258_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_257_);
v___x_259_ = lean_unsigned_to_nat(1u);
v_x_260_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_259_);
if (v___x_214_ == 0)
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_260_);
v___x_273_ = l_Lean_Syntax_isOfKind(v_x_260_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec(v_x_260_);
lean_dec(v_po_258_);
lean_dec(v_stx_212_);
v___x_274_ = lean_box(0);
return v___x_274_;
}
else
{
goto v___jp_261_;
}
}
else
{
goto v___jp_261_;
}
v___jp_261_:
{
lean_object* v___x_262_; lean_object* v_eq_263_; lean_object* v___x_264_; lean_object* v_v_265_; lean_object* v___x_266_; lean_object* v_pc_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_262_ = lean_unsigned_to_nat(2u);
v_eq_263_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_262_);
v___x_264_ = lean_unsigned_to_nat(3u);
v_v_265_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_264_);
v___x_266_ = lean_unsigned_to_nat(4u);
v_pc_267_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_po_258_);
lean_ctor_set(v___x_268_, 1, v_pc_267_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(v___x_270_, 0, v_stx_212_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
lean_ctor_set(v___x_270_, 2, v_x_260_);
lean_ctor_set(v___x_270_, 3, v_eq_263_);
lean_ctor_set(v___x_270_, 4, v_v_265_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
}
else
{
lean_object* v___x_275_; lean_object* v_v_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = lean_unsigned_to_nat(0u);
v_v_276_ = l_Lean_Syntax_getArg(v_stx_212_, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v_stx_212_);
lean_ctor_set(v___x_277_, 1, v_v_276_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx___impl(lean_object* v_x_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_tag_nat(v_x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx___impl___boxed(lean_object* v_x_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Doc_LinkTargetView_ctorIdx___impl(v_x_281_);
lean_dec_ref(v_x_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___redArg(lean_object* v_t_283_, lean_object* v_k_284_){
_start:
{
lean_object* v_stx_285_; lean_object* v_opener_286_; lean_object* v_url_287_; lean_object* v_closer_288_; lean_object* v___x_289_; 
v_stx_285_ = lean_ctor_get(v_t_283_, 0);
lean_inc(v_stx_285_);
v_opener_286_ = lean_ctor_get(v_t_283_, 1);
lean_inc(v_opener_286_);
v_url_287_ = lean_ctor_get(v_t_283_, 2);
lean_inc(v_url_287_);
v_closer_288_ = lean_ctor_get(v_t_283_, 3);
lean_inc(v_closer_288_);
lean_dec_ref(v_t_283_);
v___x_289_ = lean_apply_4(v_k_284_, v_stx_285_, v_opener_286_, v_url_287_, v_closer_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim(lean_object* v_motive_290_, lean_object* v_ctorIdx_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_k_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_292_, v_k_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___boxed(lean_object* v_motive_296_, lean_object* v_ctorIdx_297_, lean_object* v_t_298_, lean_object* v_h_299_, lean_object* v_k_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Doc_LinkTargetView_ctorElim(v_motive_296_, v_ctorIdx_297_, v_t_298_, v_h_299_, v_k_300_);
lean_dec(v_ctorIdx_297_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim___redArg(lean_object* v_t_302_, lean_object* v_url_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_302_, v_url_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim(lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_url_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_306_, v_url_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim___redArg(lean_object* v_t_310_, lean_object* v_ref_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_310_, v_ref_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim(lean_object* v_motive_313_, lean_object* v_t_314_, lean_object* v_h_315_, lean_object* v_ref_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_314_, v_ref_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(lean_object* v_tok_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Syntax_getHeadInfo(v_tok_318_);
switch(lean_obj_tag(v___x_319_))
{
case 0:
{
lean_object* v_leading_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_341_; 
v_leading_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; lean_object* v_unused_343_; lean_object* v_unused_344_; 
v_unused_342_ = lean_ctor_get(v___x_319_, 3);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v___x_319_, 2);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v___x_319_, 1);
lean_dec(v_unused_344_);
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_341_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_leading_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_341_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
uint8_t v___x_324_; lean_object* v___x_325_; 
v___x_324_ = 0;
v___x_325_ = l_Lean_Syntax_getPos_x3f(v_tok_318_, v___x_324_);
if (lean_obj_tag(v___x_325_) == 1)
{
lean_object* v_val_326_; lean_object* v_str_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_337_; 
v_val_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_326_);
lean_dec_ref_known(v___x_325_, 1);
v_str_327_ = lean_ctor_get(v_leading_320_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_leading_320_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; lean_object* v_unused_339_; 
v_unused_338_ = lean_ctor_get(v_leading_320_, 2);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_leading_320_, 1);
lean_dec(v_unused_339_);
v___x_329_ = v_leading_320_;
v_isShared_330_ = v_isSharedCheck_337_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_str_327_);
lean_dec(v_leading_320_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_337_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
lean_inc_n(v_val_326_, 2);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 2, v_val_326_);
lean_ctor_set(v___x_329_, 1, v_val_326_);
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_str_327_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_val_326_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_val_326_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
lean_inc(v_val_326_);
lean_inc_ref(v___x_332_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 3, v_val_326_);
lean_ctor_set(v___x_322_, 2, v___x_332_);
lean_ctor_set(v___x_322_, 1, v_val_326_);
lean_ctor_set(v___x_322_, 0, v___x_332_);
v___x_334_ = v___x_322_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_val_326_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_val_326_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v___x_340_; 
lean_dec(v___x_325_);
lean_del_object(v___x_322_);
lean_dec_ref(v_leading_320_);
v___x_340_ = lean_box(2);
return v___x_340_;
}
}
}
case 1:
{
uint8_t v_canonical_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_356_; 
v_canonical_345_ = lean_ctor_get_uint8(v___x_319_, sizeof(void*)*2);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; lean_object* v_unused_358_; 
v_unused_357_ = lean_ctor_get(v___x_319_, 1);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v___x_319_, 0);
lean_dec(v_unused_358_);
v___x_347_ = v___x_319_;
v_isShared_348_ = v_isSharedCheck_356_;
goto v_resetjp_346_;
}
else
{
lean_dec(v___x_319_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_356_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
uint8_t v___x_349_; lean_object* v___x_350_; 
v___x_349_ = 0;
v___x_350_ = l_Lean_Syntax_getPos_x3f(v_tok_318_, v___x_349_);
if (lean_obj_tag(v___x_350_) == 1)
{
lean_object* v_val_351_; lean_object* v___x_353_; 
v_val_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc_n(v_val_351_, 2);
lean_dec_ref_known(v___x_350_, 1);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_val_351_);
lean_ctor_set(v___x_347_, 0, v_val_351_);
v___x_353_ = v___x_347_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_val_351_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_val_351_);
lean_ctor_set_uint8(v_reuseFailAlloc_354_, sizeof(void*)*2, v_canonical_345_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v___x_355_; 
lean_dec(v___x_350_);
lean_del_object(v___x_347_);
v___x_355_ = lean_box(2);
return v___x_355_;
}
}
}
default: 
{
lean_object* v___x_359_; 
lean_dec(v___x_319_);
v___x_359_ = lean_box(2);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo___boxed(lean_object* v_tok_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v_tok_360_);
lean_dec(v_tok_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(lean_object* v___x_363_, lean_object* v_value_364_, lean_object* v_a_365_, lean_object* v_b_366_){
_start:
{
uint8_t v_decide_367_; 
v_decide_367_ = lean_nat_dec_eq(v_a_365_, v___x_363_);
if (v_decide_367_ == 0)
{
uint32_t v___x_368_; lean_object* v___x_369_; uint32_t v___x_370_; uint8_t v___x_371_; 
v___x_368_ = lean_string_utf8_get_fast(v_value_364_, v_a_365_);
v___x_369_ = lean_string_utf8_next_fast(v_value_364_, v_a_365_);
lean_dec(v_a_365_);
v___x_370_ = 92;
v___x_371_ = lean_uint32_dec_eq(v___x_368_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
v___x_372_ = lean_string_push(v_b_366_, v___x_368_);
v_a_365_ = v___x_369_;
v_b_366_ = v___x_372_;
goto _start;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0));
v___x_375_ = lean_string_append(v_b_366_, v___x_374_);
v_a_365_ = v___x_369_;
v_b_366_ = v___x_375_;
goto _start;
}
}
else
{
lean_dec(v_a_365_);
return v_b_366_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___boxed(lean_object* v___x_377_, lean_object* v_value_378_, lean_object* v_a_379_, lean_object* v_b_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_377_, v_value_378_, v_a_379_, v_b_380_);
lean_dec_ref(v_value_378_);
lean_dec(v___x_377_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(lean_object* v_value_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0));
v___x_385_ = lean_string_utf8_byte_size(v_value_383_);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_385_, v_value_383_, v___x_386_, v___x_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___boxed(lean_object* v_value_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_388_);
lean_dec_ref(v_value_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(lean_object* v___x_390_, lean_object* v___x_391_, lean_object* v_value_392_, lean_object* v_inst_393_, lean_object* v_R_394_, lean_object* v_a_395_, lean_object* v_b_396_, lean_object* v_c_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_391_, v_value_392_, v_a_395_, v_b_396_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___boxed(lean_object* v___x_399_, lean_object* v___x_400_, lean_object* v_value_401_, lean_object* v_inst_402_, lean_object* v_R_403_, lean_object* v_a_404_, lean_object* v_b_405_, lean_object* v_c_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(v___x_399_, v___x_400_, v_value_401_, v_inst_402_, v_R_403_, v_a_404_, v_b_405_, v_c_406_);
lean_dec_ref(v_value_401_);
lean_dec(v___x_400_);
lean_dec_ref(v___x_399_);
return v_res_407_;
}
}
lean_object* l_Lean_Doc_mkVersoTextFrom(lean_object* v_src_408_, lean_object* v_value_409_, uint8_t v_canonical_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = l_Lean_Doc_versoTextKind;
v___x_412_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_409_);
v___x_413_ = l_Lean_SourceInfo_fromRef(v_src_408_, v_canonical_410_);
v___x_414_ = l_Lean_Syntax_mkLit(v___x_411_, v___x_412_, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoTextFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_408_ = stack[0].m_obj;
lean_object* v_value_409_ = stack[1].m_obj;
uint8_t v_canonical_410_ = stack[2].m_num;
lean_object* v_res_415_;
v_res_415_ = l_Lean_Doc_mkVersoTextFrom(v_src_408_, v_value_409_, v_canonical_410_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom___boxed(lean_object* v_src_416_, lean_object* v_value_417_, lean_object* v_canonical_418_){
_start:
{
uint8_t v_canonical_boxed_419_; lean_object* v_res_420_; 
v_canonical_boxed_419_ = lean_unbox(v_canonical_418_);
v_res_420_ = l_Lean_Doc_mkVersoTextFrom(v_src_416_, v_value_417_, v_canonical_boxed_419_);
lean_dec_ref(v_value_417_);
lean_dec(v_src_416_);
return v_res_420_;
}
}
lean_object* l_Lean_Doc_mkVersoRefNameFrom(lean_object* v_src_421_, lean_object* v_value_422_, uint8_t v_canonical_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = l_Lean_Doc_versoRefKind;
v___x_425_ = l_Lean_SourceInfo_fromRef(v_src_421_, v_canonical_423_);
v___x_426_ = l_Lean_Syntax_mkLit(v___x_424_, v_value_422_, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoRefNameFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_421_ = stack[0].m_obj;
lean_object* v_value_422_ = stack[1].m_obj;
uint8_t v_canonical_423_ = stack[2].m_num;
lean_object* v_res_427_;
v_res_427_ = l_Lean_Doc_mkVersoRefNameFrom(v_src_421_, v_value_422_, v_canonical_423_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom___boxed(lean_object* v_src_428_, lean_object* v_value_429_, lean_object* v_canonical_430_){
_start:
{
uint8_t v_canonical_boxed_431_; lean_object* v_res_432_; 
v_canonical_boxed_431_ = lean_unbox(v_canonical_430_);
v_res_432_ = l_Lean_Doc_mkVersoRefNameFrom(v_src_428_, v_value_429_, v_canonical_boxed_431_);
lean_dec(v_src_428_);
return v_res_432_;
}
}
lean_object* l_Lean_Doc_mkVersoLinkUrlFrom(lean_object* v_src_433_, lean_object* v_value_434_, uint8_t v_canonical_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = l_Lean_Doc_versoLinkUrlKind;
v___x_437_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_434_);
v___x_438_ = l_Lean_SourceInfo_fromRef(v_src_433_, v_canonical_435_);
v___x_439_ = l_Lean_Syntax_mkLit(v___x_436_, v___x_437_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinkUrlFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_433_ = stack[0].m_obj;
lean_object* v_value_434_ = stack[1].m_obj;
uint8_t v_canonical_435_ = stack[2].m_num;
lean_object* v_res_440_;
v_res_440_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_src_433_, v_value_434_, v_canonical_435_);
stack->m_obj
 = v_res_440_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom___boxed(lean_object* v_src_441_, lean_object* v_value_442_, lean_object* v_canonical_443_){
_start:
{
uint8_t v_canonical_boxed_444_; lean_object* v_res_445_; 
v_canonical_boxed_444_ = lean_unbox(v_canonical_443_);
v_res_445_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_src_441_, v_value_442_, v_canonical_boxed_444_);
lean_dec_ref(v_value_442_);
lean_dec(v_src_441_);
return v_res_445_;
}
}
lean_object* l_Lean_Doc_mkVersoImageAltFrom(lean_object* v_src_446_, lean_object* v_value_447_, uint8_t v_canonical_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_449_ = l_Lean_Doc_versoImageAltKind;
v___x_450_ = l_Lean_Doc_escapeVersoImageAlt(v_value_447_);
v___x_451_ = l_Lean_SourceInfo_fromRef(v_src_446_, v_canonical_448_);
v___x_452_ = l_Lean_Syntax_mkLit(v___x_449_, v___x_450_, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoImageAltFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_446_ = stack[0].m_obj;
lean_object* v_value_447_ = stack[1].m_obj;
uint8_t v_canonical_448_ = stack[2].m_num;
lean_object* v_res_453_;
v_res_453_ = l_Lean_Doc_mkVersoImageAltFrom(v_src_446_, v_value_447_, v_canonical_448_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom___boxed(lean_object* v_src_454_, lean_object* v_value_455_, lean_object* v_canonical_456_){
_start:
{
uint8_t v_canonical_boxed_457_; lean_object* v_res_458_; 
v_canonical_boxed_457_ = lean_unbox(v_canonical_456_);
v_res_458_ = l_Lean_Doc_mkVersoImageAltFrom(v_src_454_, v_value_455_, v_canonical_boxed_457_);
lean_dec_ref(v_value_455_);
lean_dec(v_src_454_);
return v_res_458_;
}
}
lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom(lean_object* v_src_459_, lean_object* v_value_460_, uint8_t v_canonical_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = l_Lean_Doc_versoLinkRefUrlKind;
v___x_463_ = l_Lean_SourceInfo_fromRef(v_src_459_, v_canonical_461_);
v___x_464_ = l_Lean_Syntax_mkLit(v___x_462_, v_value_460_, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinkRefUrlFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_459_ = stack[0].m_obj;
lean_object* v_value_460_ = stack[1].m_obj;
uint8_t v_canonical_461_ = stack[2].m_num;
lean_object* v_res_465_;
v_res_465_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_src_459_, v_value_460_, v_canonical_461_);
stack->m_obj
 = v_res_465_;
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
lean_object* l_Lean_Doc_mkVersoCodeFrom(lean_object* v_src_553_, lean_object* v_value_554_, uint8_t v_canonical_555_){
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
LEAN_EXPORT void l_Lean_Doc_mkVersoCodeFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_553_ = stack[0].m_obj;
lean_object* v_value_554_ = stack[1].m_obj;
uint8_t v_canonical_555_ = stack[2].m_num;
lean_object* v_res_566_;
v_res_566_ = l_Lean_Doc_mkVersoCodeFrom(v_src_553_, v_value_554_, v_canonical_555_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom___boxed(lean_object* v_src_567_, lean_object* v_value_568_, lean_object* v_canonical_569_){
_start:
{
uint8_t v_canonical_boxed_570_; lean_object* v_res_571_; 
v_canonical_boxed_570_ = lean_unbox(v_canonical_569_);
v_res_571_ = l_Lean_Doc_mkVersoCodeFrom(v_src_567_, v_value_568_, v_canonical_boxed_570_);
lean_dec_ref(v_value_568_);
lean_dec(v_src_567_);
return v_res_571_;
}
}
lean_object* l_Lean_Doc_mkVersoCodeBlockFrom(lean_object* v_src_572_, lean_object* v_value_573_, uint8_t v_canonical_574_){
_start:
{
lean_object* v_info_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_info_575_ = l_Lean_SourceInfo_fromRef(v_src_572_, v_canonical_574_);
v___x_576_ = l_Lean_Doc_versoCodeBlockKind;
lean_inc(v_info_575_);
v___x_577_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_575_, v_value_573_);
v___x_578_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_579_ = lean_box(2);
v___x_580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_577_);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_mk_empty_array_with_capacity(v___x_581_);
v___x_583_ = lean_array_push(v___x_582_, v___x_580_);
v___x_584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_584_, 0, v_info_575_);
lean_ctor_set(v___x_584_, 1, v___x_576_);
lean_ctor_set(v___x_584_, 2, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoCodeBlockFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_572_ = stack[0].m_obj;
lean_object* v_value_573_ = stack[1].m_obj;
uint8_t v_canonical_574_ = stack[2].m_num;
lean_object* v_res_585_;
v_res_585_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_src_572_, v_value_573_, v_canonical_574_);
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___boxed(lean_object* v_src_586_, lean_object* v_value_587_, lean_object* v_canonical_588_){
_start:
{
uint8_t v_canonical_boxed_589_; lean_object* v_res_590_; 
v_canonical_boxed_589_ = lean_unbox(v_canonical_588_);
v_res_590_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_src_586_, v_value_587_, v_canonical_boxed_589_);
lean_dec_ref(v_value_587_);
lean_dec(v_src_586_);
return v_res_590_;
}
}
lean_object* l_Lean_Doc_mkVersoLinebreakFrom(lean_object* v_src_600_, uint8_t v_canonical_601_){
_start:
{
lean_object* v_info_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_info_602_ = l_Lean_SourceInfo_fromRef(v_src_600_, v_canonical_601_);
v___x_603_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
v___x_604_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__3));
lean_inc(v_info_602_);
v___x_605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_605_, 0, v_info_602_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_mk_empty_array_with_capacity(v___x_606_);
v___x_608_ = lean_array_push(v___x_607_, v___x_605_);
v___x_609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_609_, 0, v_info_602_);
lean_ctor_set(v___x_609_, 1, v___x_603_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinebreakFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_600_ = stack[0].m_obj;
uint8_t v_canonical_601_ = stack[1].m_num;
lean_object* v_res_610_;
v_res_610_ = l_Lean_Doc_mkVersoLinebreakFrom(v_src_600_, v_canonical_601_);
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom___boxed(lean_object* v_src_611_, lean_object* v_canonical_612_){
_start:
{
uint8_t v_canonical_boxed_613_; lean_object* v_res_614_; 
v_canonical_boxed_613_ = lean_unbox(v_canonical_612_);
v_res_614_ = l_Lean_Doc_mkVersoLinebreakFrom(v_src_611_, v_canonical_boxed_613_);
lean_dec(v_src_611_);
return v_res_614_;
}
}
lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(uint8_t v_canonical_615_, lean_object* v_toPure_616_, lean_object* v_____do__lift_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = l_Lean_Doc_mkVersoLinebreakFrom(v_____do__lift_617_, v_canonical_615_);
v___x_619_ = lean_apply_2(v_toPure_616_, lean_box(0), v___x_618_);
return v___x_619_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_canonical_615_ = stack[0].m_num;
lean_object* v_toPure_616_ = stack[1].m_obj;
lean_object* v_____do__lift_617_ = stack[2].m_obj;
lean_object* v_res_620_;
v_res_620_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(v_canonical_615_, v_toPure_616_, v_____do__lift_617_);
stack->m_obj
 = v_res_620_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed(lean_object* v_canonical_621_, lean_object* v_toPure_622_, lean_object* v_____do__lift_623_){
_start:
{
uint8_t v_canonical_boxed_624_; lean_object* v_res_625_; 
v_canonical_boxed_624_ = lean_unbox(v_canonical_621_);
v_res_625_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(v_canonical_boxed_624_, v_toPure_622_, v_____do__lift_623_);
lean_dec(v_____do__lift_623_);
return v_res_625_;
}
}
lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg(lean_object* v_inst_626_, lean_object* v_inst_627_, uint8_t v_canonical_628_){
_start:
{
lean_object* v_toApplicative_629_; lean_object* v_toBind_630_; lean_object* v_getRef_631_; lean_object* v_toPure_632_; lean_object* v___x_633_; lean_object* v___f_634_; lean_object* v___x_635_; 
v_toApplicative_629_ = lean_ctor_get(v_inst_626_, 0);
lean_inc_ref(v_toApplicative_629_);
v_toBind_630_ = lean_ctor_get(v_inst_626_, 1);
lean_inc(v_toBind_630_);
lean_dec_ref(v_inst_626_);
v_getRef_631_ = lean_ctor_get(v_inst_627_, 0);
lean_inc(v_getRef_631_);
lean_dec_ref(v_inst_627_);
v_toPure_632_ = lean_ctor_get(v_toApplicative_629_, 1);
lean_inc(v_toPure_632_);
lean_dec_ref(v_toApplicative_629_);
v___x_633_ = lean_box(v_canonical_628_);
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_634_, 0, v___x_633_);
lean_closure_set(v___f_634_, 1, v_toPure_632_);
v___x_635_ = lean_apply_4(v_toBind_630_, lean_box(0), lean_box(0), v_getRef_631_, v___f_634_);
return v___x_635_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinebreakFromRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_626_ = stack[0].m_obj;
lean_object* v_inst_627_ = stack[1].m_obj;
uint8_t v_canonical_628_ = stack[2].m_num;
lean_object* v_res_636_;
v_res_636_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_626_, v_inst_627_, v_canonical_628_);
stack->m_obj
 = v_res_636_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___boxed(lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_canonical_639_){
_start:
{
uint8_t v_canonical_boxed_640_; lean_object* v_res_641_; 
v_canonical_boxed_640_ = lean_unbox(v_canonical_639_);
v_res_641_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_637_, v_inst_638_, v_canonical_boxed_640_);
return v_res_641_;
}
}
lean_object* l_Lean_Doc_mkVersoLinebreakFromRef(lean_object* v_m_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, uint8_t v_canonical_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_643_, v_inst_644_, v_canonical_645_);
return v___x_646_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinebreakFromRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_643_ = stack[1].m_obj;
lean_object* v_inst_644_ = stack[2].m_obj;
uint8_t v_canonical_645_ = stack[3].m_num;
lean_object* v_res_647_;
v_res_647_ = l_Lean_Doc_mkVersoLinebreakFromRef(lean_box(0), v_inst_643_, v_inst_644_, v_canonical_645_);
stack->m_obj
 = v_res_647_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___boxed(lean_object* v_m_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_canonical_651_){
_start:
{
uint8_t v_canonical_boxed_652_; lean_object* v_res_653_; 
v_canonical_boxed_652_ = lean_unbox(v_canonical_651_);
v_res_653_ = l_Lean_Doc_mkVersoLinebreakFromRef(v_m_648_, v_inst_649_, v_inst_650_, v_canonical_boxed_652_);
return v_res_653_;
}
}
lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(lean_object* v_value_654_, uint8_t v_canonical_655_, lean_object* v_toPure_656_, lean_object* v_____do__lift_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = l_Lean_Doc_mkVersoTextFrom(v_____do__lift_657_, v_value_654_, v_canonical_655_);
v___x_659_ = lean_apply_2(v_toPure_656_, lean_box(0), v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_654_ = stack[0].m_obj;
uint8_t v_canonical_655_ = stack[1].m_num;
lean_object* v_toPure_656_ = stack[2].m_obj;
lean_object* v_____do__lift_657_ = stack[3].m_obj;
lean_object* v_res_660_;
v_res_660_ = l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(v_value_654_, v_canonical_655_, v_toPure_656_, v_____do__lift_657_);
stack->m_obj
 = v_res_660_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed(lean_object* v_value_661_, lean_object* v_canonical_662_, lean_object* v_toPure_663_, lean_object* v_____do__lift_664_){
_start:
{
uint8_t v_canonical_boxed_665_; lean_object* v_res_666_; 
v_canonical_boxed_665_ = lean_unbox(v_canonical_662_);
v_res_666_ = l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(v_value_661_, v_canonical_boxed_665_, v_toPure_663_, v_____do__lift_664_);
lean_dec(v_____do__lift_664_);
lean_dec_ref(v_value_661_);
return v_res_666_;
}
}
lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg(lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_value_669_, uint8_t v_canonical_670_){
_start:
{
lean_object* v_toApplicative_671_; lean_object* v_toBind_672_; lean_object* v_getRef_673_; lean_object* v_toPure_674_; lean_object* v___x_675_; lean_object* v___f_676_; lean_object* v___x_677_; 
v_toApplicative_671_ = lean_ctor_get(v_inst_667_, 0);
lean_inc_ref(v_toApplicative_671_);
v_toBind_672_ = lean_ctor_get(v_inst_667_, 1);
lean_inc(v_toBind_672_);
lean_dec_ref(v_inst_667_);
v_getRef_673_ = lean_ctor_get(v_inst_668_, 0);
lean_inc(v_getRef_673_);
lean_dec_ref(v_inst_668_);
v_toPure_674_ = lean_ctor_get(v_toApplicative_671_, 1);
lean_inc(v_toPure_674_);
lean_dec_ref(v_toApplicative_671_);
v___x_675_ = lean_box(v_canonical_670_);
v___f_676_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_676_, 0, v_value_669_);
lean_closure_set(v___f_676_, 1, v___x_675_);
lean_closure_set(v___f_676_, 2, v_toPure_674_);
v___x_677_ = lean_apply_4(v_toBind_672_, lean_box(0), lean_box(0), v_getRef_673_, v___f_676_);
return v___x_677_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoTextFromRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_667_ = stack[0].m_obj;
lean_object* v_inst_668_ = stack[1].m_obj;
lean_object* v_value_669_ = stack[2].m_obj;
uint8_t v_canonical_670_ = stack[3].m_num;
lean_object* v_res_678_;
v_res_678_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_667_, v_inst_668_, v_value_669_, v_canonical_670_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___boxed(lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_value_681_, lean_object* v_canonical_682_){
_start:
{
uint8_t v_canonical_boxed_683_; lean_object* v_res_684_; 
v_canonical_boxed_683_ = lean_unbox(v_canonical_682_);
v_res_684_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_679_, v_inst_680_, v_value_681_, v_canonical_boxed_683_);
return v_res_684_;
}
}
lean_object* l_Lean_Doc_mkVersoTextFromRef(lean_object* v_m_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_value_688_, uint8_t v_canonical_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_686_, v_inst_687_, v_value_688_, v_canonical_689_);
return v___x_690_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoTextFromRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_686_ = stack[1].m_obj;
lean_object* v_inst_687_ = stack[2].m_obj;
lean_object* v_value_688_ = stack[3].m_obj;
uint8_t v_canonical_689_ = stack[4].m_num;
lean_object* v_res_691_;
v_res_691_ = l_Lean_Doc_mkVersoTextFromRef(lean_box(0), v_inst_686_, v_inst_687_, v_value_688_, v_canonical_689_);
stack->m_obj
 = v_res_691_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___boxed(lean_object* v_m_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_value_695_, lean_object* v_canonical_696_){
_start:
{
uint8_t v_canonical_boxed_697_; lean_object* v_res_698_; 
v_canonical_boxed_697_ = lean_unbox(v_canonical_696_);
v_res_698_ = l_Lean_Doc_mkVersoTextFromRef(v_m_692_, v_inst_693_, v_inst_694_, v_value_695_, v_canonical_boxed_697_);
return v_res_698_;
}
}
lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(lean_object* v_value_699_, uint8_t v_canonical_700_, lean_object* v_toPure_701_, lean_object* v_____do__lift_702_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = l_Lean_Doc_mkVersoRefNameFrom(v_____do__lift_702_, v_value_699_, v_canonical_700_);
v___x_704_ = lean_apply_2(v_toPure_701_, lean_box(0), v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_699_ = stack[0].m_obj;
uint8_t v_canonical_700_ = stack[1].m_num;
lean_object* v_toPure_701_ = stack[2].m_obj;
lean_object* v_____do__lift_702_ = stack[3].m_obj;
lean_object* v_res_705_;
v_res_705_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(v_value_699_, v_canonical_700_, v_toPure_701_, v_____do__lift_702_);
stack->m_obj
 = v_res_705_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed(lean_object* v_value_706_, lean_object* v_canonical_707_, lean_object* v_toPure_708_, lean_object* v_____do__lift_709_){
_start:
{
uint8_t v_canonical_boxed_710_; lean_object* v_res_711_; 
v_canonical_boxed_710_ = lean_unbox(v_canonical_707_);
v_res_711_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(v_value_706_, v_canonical_boxed_710_, v_toPure_708_, v_____do__lift_709_);
lean_dec(v_____do__lift_709_);
return v_res_711_;
}
}
lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg(lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_value_714_, uint8_t v_canonical_715_){
_start:
{
lean_object* v_toApplicative_716_; lean_object* v_toBind_717_; lean_object* v_getRef_718_; lean_object* v_toPure_719_; lean_object* v___x_720_; lean_object* v___f_721_; lean_object* v___x_722_; 
v_toApplicative_716_ = lean_ctor_get(v_inst_712_, 0);
lean_inc_ref(v_toApplicative_716_);
v_toBind_717_ = lean_ctor_get(v_inst_712_, 1);
lean_inc(v_toBind_717_);
lean_dec_ref(v_inst_712_);
v_getRef_718_ = lean_ctor_get(v_inst_713_, 0);
lean_inc(v_getRef_718_);
lean_dec_ref(v_inst_713_);
v_toPure_719_ = lean_ctor_get(v_toApplicative_716_, 1);
lean_inc(v_toPure_719_);
lean_dec_ref(v_toApplicative_716_);
v___x_720_ = lean_box(v_canonical_715_);
v___f_721_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_721_, 0, v_value_714_);
lean_closure_set(v___f_721_, 1, v___x_720_);
lean_closure_set(v___f_721_, 2, v_toPure_719_);
v___x_722_ = lean_apply_4(v_toBind_717_, lean_box(0), lean_box(0), v_getRef_718_, v___f_721_);
return v___x_722_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoRefNameFromRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_712_ = stack[0].m_obj;
lean_object* v_inst_713_ = stack[1].m_obj;
lean_object* v_value_714_ = stack[2].m_obj;
uint8_t v_canonical_715_ = stack[3].m_num;
lean_object* v_res_723_;
v_res_723_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_712_, v_inst_713_, v_value_714_, v_canonical_715_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___boxed(lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_value_726_, lean_object* v_canonical_727_){
_start:
{
uint8_t v_canonical_boxed_728_; lean_object* v_res_729_; 
v_canonical_boxed_728_ = lean_unbox(v_canonical_727_);
v_res_729_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_724_, v_inst_725_, v_value_726_, v_canonical_boxed_728_);
return v_res_729_;
}
}
lean_object* l_Lean_Doc_mkVersoRefNameFromRef(lean_object* v_m_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_value_733_, uint8_t v_canonical_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_731_, v_inst_732_, v_value_733_, v_canonical_734_);
return v___x_735_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoRefNameFromRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_731_ = stack[1].m_obj;
lean_object* v_inst_732_ = stack[2].m_obj;
lean_object* v_value_733_ = stack[3].m_obj;
uint8_t v_canonical_734_ = stack[4].m_num;
lean_object* v_res_736_;
v_res_736_ = l_Lean_Doc_mkVersoRefNameFromRef(lean_box(0), v_inst_731_, v_inst_732_, v_value_733_, v_canonical_734_);
stack->m_obj
 = v_res_736_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___boxed(lean_object* v_m_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_value_740_, lean_object* v_canonical_741_){
_start:
{
uint8_t v_canonical_boxed_742_; lean_object* v_res_743_; 
v_canonical_boxed_742_ = lean_unbox(v_canonical_741_);
v_res_743_ = l_Lean_Doc_mkVersoRefNameFromRef(v_m_737_, v_inst_738_, v_inst_739_, v_value_740_, v_canonical_boxed_742_);
return v_res_743_;
}
}
lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(lean_object* v_value_744_, uint8_t v_canonical_745_, lean_object* v_toPure_746_, lean_object* v_____do__lift_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_____do__lift_747_, v_value_744_, v_canonical_745_);
v___x_749_ = lean_apply_2(v_toPure_746_, lean_box(0), v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_744_ = stack[0].m_obj;
uint8_t v_canonical_745_ = stack[1].m_num;
lean_object* v_toPure_746_ = stack[2].m_obj;
lean_object* v_____do__lift_747_ = stack[3].m_obj;
lean_object* v_res_750_;
v_res_750_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(v_value_744_, v_canonical_745_, v_toPure_746_, v_____do__lift_747_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_751_, lean_object* v_canonical_752_, lean_object* v_toPure_753_, lean_object* v_____do__lift_754_){
_start:
{
uint8_t v_canonical_boxed_755_; lean_object* v_res_756_; 
v_canonical_boxed_755_ = lean_unbox(v_canonical_752_);
v_res_756_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(v_value_751_, v_canonical_boxed_755_, v_toPure_753_, v_____do__lift_754_);
lean_dec(v_____do__lift_754_);
lean_dec_ref(v_value_751_);
return v_res_756_;
}
}
lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_value_759_, uint8_t v_canonical_760_){
_start:
{
lean_object* v_toApplicative_761_; lean_object* v_toBind_762_; lean_object* v_getRef_763_; lean_object* v_toPure_764_; lean_object* v___x_765_; lean_object* v___f_766_; lean_object* v___x_767_; 
v_toApplicative_761_ = lean_ctor_get(v_inst_757_, 0);
lean_inc_ref(v_toApplicative_761_);
v_toBind_762_ = lean_ctor_get(v_inst_757_, 1);
lean_inc(v_toBind_762_);
lean_dec_ref(v_inst_757_);
v_getRef_763_ = lean_ctor_get(v_inst_758_, 0);
lean_inc(v_getRef_763_);
lean_dec_ref(v_inst_758_);
v_toPure_764_ = lean_ctor_get(v_toApplicative_761_, 1);
lean_inc(v_toPure_764_);
lean_dec_ref(v_toApplicative_761_);
v___x_765_ = lean_box(v_canonical_760_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_766_, 0, v_value_759_);
lean_closure_set(v___f_766_, 1, v___x_765_);
lean_closure_set(v___f_766_, 2, v_toPure_764_);
v___x_767_ = lean_apply_4(v_toBind_762_, lean_box(0), lean_box(0), v_getRef_763_, v___f_766_);
return v___x_767_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinkUrlFromRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_757_ = stack[0].m_obj;
lean_object* v_inst_758_ = stack[1].m_obj;
lean_object* v_value_759_ = stack[2].m_obj;
uint8_t v_canonical_760_ = stack[3].m_num;
lean_object* v_res_768_;
v_res_768_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_757_, v_inst_758_, v_value_759_, v_canonical_760_);
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___boxed(lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_value_771_, lean_object* v_canonical_772_){
_start:
{
uint8_t v_canonical_boxed_773_; lean_object* v_res_774_; 
v_canonical_boxed_773_ = lean_unbox(v_canonical_772_);
v_res_774_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_769_, v_inst_770_, v_value_771_, v_canonical_boxed_773_);
return v_res_774_;
}
}
lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef(lean_object* v_m_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_value_778_, uint8_t v_canonical_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_776_, v_inst_777_, v_value_778_, v_canonical_779_);
return v___x_780_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinkUrlFromRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_776_ = stack[1].m_obj;
lean_object* v_inst_777_ = stack[2].m_obj;
lean_object* v_value_778_ = stack[3].m_obj;
uint8_t v_canonical_779_ = stack[4].m_num;
lean_object* v_res_781_;
v_res_781_ = l_Lean_Doc_mkVersoLinkUrlFromRef(lean_box(0), v_inst_776_, v_inst_777_, v_value_778_, v_canonical_779_);
stack->m_obj
 = v_res_781_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___boxed(lean_object* v_m_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_value_785_, lean_object* v_canonical_786_){
_start:
{
uint8_t v_canonical_boxed_787_; lean_object* v_res_788_; 
v_canonical_boxed_787_ = lean_unbox(v_canonical_786_);
v_res_788_ = l_Lean_Doc_mkVersoLinkUrlFromRef(v_m_782_, v_inst_783_, v_inst_784_, v_value_785_, v_canonical_boxed_787_);
return v_res_788_;
}
}
lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(lean_object* v_value_789_, uint8_t v_canonical_790_, lean_object* v_toPure_791_, lean_object* v_____do__lift_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = l_Lean_Doc_mkVersoImageAltFrom(v_____do__lift_792_, v_value_789_, v_canonical_790_);
v___x_794_ = lean_apply_2(v_toPure_791_, lean_box(0), v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_789_ = stack[0].m_obj;
uint8_t v_canonical_790_ = stack[1].m_num;
lean_object* v_toPure_791_ = stack[2].m_obj;
lean_object* v_____do__lift_792_ = stack[3].m_obj;
lean_object* v_res_795_;
v_res_795_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(v_value_789_, v_canonical_790_, v_toPure_791_, v_____do__lift_792_);
stack->m_obj
 = v_res_795_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed(lean_object* v_value_796_, lean_object* v_canonical_797_, lean_object* v_toPure_798_, lean_object* v_____do__lift_799_){
_start:
{
uint8_t v_canonical_boxed_800_; lean_object* v_res_801_; 
v_canonical_boxed_800_ = lean_unbox(v_canonical_797_);
v_res_801_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(v_value_796_, v_canonical_boxed_800_, v_toPure_798_, v_____do__lift_799_);
lean_dec(v_____do__lift_799_);
lean_dec_ref(v_value_796_);
return v_res_801_;
}
}
lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg(lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_value_804_, uint8_t v_canonical_805_){
_start:
{
lean_object* v_toApplicative_806_; lean_object* v_toBind_807_; lean_object* v_getRef_808_; lean_object* v_toPure_809_; lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___x_812_; 
v_toApplicative_806_ = lean_ctor_get(v_inst_802_, 0);
lean_inc_ref(v_toApplicative_806_);
v_toBind_807_ = lean_ctor_get(v_inst_802_, 1);
lean_inc(v_toBind_807_);
lean_dec_ref(v_inst_802_);
v_getRef_808_ = lean_ctor_get(v_inst_803_, 0);
lean_inc(v_getRef_808_);
lean_dec_ref(v_inst_803_);
v_toPure_809_ = lean_ctor_get(v_toApplicative_806_, 1);
lean_inc(v_toPure_809_);
lean_dec_ref(v_toApplicative_806_);
v___x_810_ = lean_box(v_canonical_805_);
v___f_811_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_811_, 0, v_value_804_);
lean_closure_set(v___f_811_, 1, v___x_810_);
lean_closure_set(v___f_811_, 2, v_toPure_809_);
v___x_812_ = lean_apply_4(v_toBind_807_, lean_box(0), lean_box(0), v_getRef_808_, v___f_811_);
return v___x_812_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoImageAltFromRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_802_ = stack[0].m_obj;
lean_object* v_inst_803_ = stack[1].m_obj;
lean_object* v_value_804_ = stack[2].m_obj;
uint8_t v_canonical_805_ = stack[3].m_num;
lean_object* v_res_813_;
v_res_813_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_802_, v_inst_803_, v_value_804_, v_canonical_805_);
stack->m_obj
 = v_res_813_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___boxed(lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_value_816_, lean_object* v_canonical_817_){
_start:
{
uint8_t v_canonical_boxed_818_; lean_object* v_res_819_; 
v_canonical_boxed_818_ = lean_unbox(v_canonical_817_);
v_res_819_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_814_, v_inst_815_, v_value_816_, v_canonical_boxed_818_);
return v_res_819_;
}
}
lean_object* l_Lean_Doc_mkVersoImageAltFromRef(lean_object* v_m_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_value_823_, uint8_t v_canonical_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_821_, v_inst_822_, v_value_823_, v_canonical_824_);
return v___x_825_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoImageAltFromRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_821_ = stack[1].m_obj;
lean_object* v_inst_822_ = stack[2].m_obj;
lean_object* v_value_823_ = stack[3].m_obj;
uint8_t v_canonical_824_ = stack[4].m_num;
lean_object* v_res_826_;
v_res_826_ = l_Lean_Doc_mkVersoImageAltFromRef(lean_box(0), v_inst_821_, v_inst_822_, v_value_823_, v_canonical_824_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___boxed(lean_object* v_m_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_value_830_, lean_object* v_canonical_831_){
_start:
{
uint8_t v_canonical_boxed_832_; lean_object* v_res_833_; 
v_canonical_boxed_832_ = lean_unbox(v_canonical_831_);
v_res_833_ = l_Lean_Doc_mkVersoImageAltFromRef(v_m_827_, v_inst_828_, v_inst_829_, v_value_830_, v_canonical_boxed_832_);
return v_res_833_;
}
}
lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(lean_object* v_value_834_, uint8_t v_canonical_835_, lean_object* v_toPure_836_, lean_object* v_____do__lift_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_____do__lift_837_, v_value_834_, v_canonical_835_);
v___x_839_ = lean_apply_2(v_toPure_836_, lean_box(0), v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_834_ = stack[0].m_obj;
uint8_t v_canonical_835_ = stack[1].m_num;
lean_object* v_toPure_836_ = stack[2].m_obj;
lean_object* v_____do__lift_837_ = stack[3].m_obj;
lean_object* v_res_840_;
v_res_840_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(v_value_834_, v_canonical_835_, v_toPure_836_, v_____do__lift_837_);
stack->m_obj
 = v_res_840_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_841_, lean_object* v_canonical_842_, lean_object* v_toPure_843_, lean_object* v_____do__lift_844_){
_start:
{
uint8_t v_canonical_boxed_845_; lean_object* v_res_846_; 
v_canonical_boxed_845_ = lean_unbox(v_canonical_842_);
v_res_846_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(v_value_841_, v_canonical_boxed_845_, v_toPure_843_, v_____do__lift_844_);
lean_dec(v_____do__lift_844_);
return v_res_846_;
}
}
lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_value_849_, uint8_t v_canonical_850_){
_start:
{
lean_object* v_toApplicative_851_; lean_object* v_toBind_852_; lean_object* v_getRef_853_; lean_object* v_toPure_854_; lean_object* v___x_855_; lean_object* v___f_856_; lean_object* v___x_857_; 
v_toApplicative_851_ = lean_ctor_get(v_inst_847_, 0);
lean_inc_ref(v_toApplicative_851_);
v_toBind_852_ = lean_ctor_get(v_inst_847_, 1);
lean_inc(v_toBind_852_);
lean_dec_ref(v_inst_847_);
v_getRef_853_ = lean_ctor_get(v_inst_848_, 0);
lean_inc(v_getRef_853_);
lean_dec_ref(v_inst_848_);
v_toPure_854_ = lean_ctor_get(v_toApplicative_851_, 1);
lean_inc(v_toPure_854_);
lean_dec_ref(v_toApplicative_851_);
v___x_855_ = lean_box(v_canonical_850_);
v___f_856_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_856_, 0, v_value_849_);
lean_closure_set(v___f_856_, 1, v___x_855_);
lean_closure_set(v___f_856_, 2, v_toPure_854_);
v___x_857_ = lean_apply_4(v_toBind_852_, lean_box(0), lean_box(0), v_getRef_853_, v___f_856_);
return v___x_857_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_847_ = stack[0].m_obj;
lean_object* v_inst_848_ = stack[1].m_obj;
lean_object* v_value_849_ = stack[2].m_obj;
uint8_t v_canonical_850_ = stack[3].m_num;
lean_object* v_res_858_;
v_res_858_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_847_, v_inst_848_, v_value_849_, v_canonical_850_);
stack->m_obj
 = v_res_858_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___boxed(lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_value_861_, lean_object* v_canonical_862_){
_start:
{
uint8_t v_canonical_boxed_863_; lean_object* v_res_864_; 
v_canonical_boxed_863_ = lean_unbox(v_canonical_862_);
v_res_864_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_859_, v_inst_860_, v_value_861_, v_canonical_boxed_863_);
return v_res_864_;
}
}
lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef(lean_object* v_m_865_, lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_value_868_, uint8_t v_canonical_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_866_, v_inst_867_, v_value_868_, v_canonical_869_);
return v___x_870_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoLinkRefUrlFromRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_866_ = stack[1].m_obj;
lean_object* v_inst_867_ = stack[2].m_obj;
lean_object* v_value_868_ = stack[3].m_obj;
uint8_t v_canonical_869_ = stack[4].m_num;
lean_object* v_res_871_;
v_res_871_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef(lean_box(0), v_inst_866_, v_inst_867_, v_value_868_, v_canonical_869_);
stack->m_obj
 = v_res_871_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___boxed(lean_object* v_m_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_value_875_, lean_object* v_canonical_876_){
_start:
{
uint8_t v_canonical_boxed_877_; lean_object* v_res_878_; 
v_canonical_boxed_877_ = lean_unbox(v_canonical_876_);
v_res_878_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef(v_m_872_, v_inst_873_, v_inst_874_, v_value_875_, v_canonical_boxed_877_);
return v_res_878_;
}
}
lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(lean_object* v_value_879_, uint8_t v_canonical_880_, lean_object* v_toPure_881_, lean_object* v_____do__lift_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = l_Lean_Doc_mkVersoCodeFrom(v_____do__lift_882_, v_value_879_, v_canonical_880_);
v___x_884_ = lean_apply_2(v_toPure_881_, lean_box(0), v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_879_ = stack[0].m_obj;
uint8_t v_canonical_880_ = stack[1].m_num;
lean_object* v_toPure_881_ = stack[2].m_obj;
lean_object* v_____do__lift_882_ = stack[3].m_obj;
lean_object* v_res_885_;
v_res_885_ = l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(v_value_879_, v_canonical_880_, v_toPure_881_, v_____do__lift_882_);
stack->m_obj
 = v_res_885_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed(lean_object* v_value_886_, lean_object* v_canonical_887_, lean_object* v_toPure_888_, lean_object* v_____do__lift_889_){
_start:
{
uint8_t v_canonical_boxed_890_; lean_object* v_res_891_; 
v_canonical_boxed_890_ = lean_unbox(v_canonical_887_);
v_res_891_ = l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(v_value_886_, v_canonical_boxed_890_, v_toPure_888_, v_____do__lift_889_);
lean_dec(v_____do__lift_889_);
lean_dec_ref(v_value_886_);
return v_res_891_;
}
}
lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg(lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_value_894_, uint8_t v_canonical_895_){
_start:
{
lean_object* v_toApplicative_896_; lean_object* v_toBind_897_; lean_object* v_getRef_898_; lean_object* v_toPure_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; 
v_toApplicative_896_ = lean_ctor_get(v_inst_892_, 0);
lean_inc_ref(v_toApplicative_896_);
v_toBind_897_ = lean_ctor_get(v_inst_892_, 1);
lean_inc(v_toBind_897_);
lean_dec_ref(v_inst_892_);
v_getRef_898_ = lean_ctor_get(v_inst_893_, 0);
lean_inc(v_getRef_898_);
lean_dec_ref(v_inst_893_);
v_toPure_899_ = lean_ctor_get(v_toApplicative_896_, 1);
lean_inc(v_toPure_899_);
lean_dec_ref(v_toApplicative_896_);
v___x_900_ = lean_box(v_canonical_895_);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_901_, 0, v_value_894_);
lean_closure_set(v___f_901_, 1, v___x_900_);
lean_closure_set(v___f_901_, 2, v_toPure_899_);
v___x_902_ = lean_apply_4(v_toBind_897_, lean_box(0), lean_box(0), v_getRef_898_, v___f_901_);
return v___x_902_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoCodeFromRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_892_ = stack[0].m_obj;
lean_object* v_inst_893_ = stack[1].m_obj;
lean_object* v_value_894_ = stack[2].m_obj;
uint8_t v_canonical_895_ = stack[3].m_num;
lean_object* v_res_903_;
v_res_903_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_892_, v_inst_893_, v_value_894_, v_canonical_895_);
stack->m_obj
 = v_res_903_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___boxed(lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_value_906_, lean_object* v_canonical_907_){
_start:
{
uint8_t v_canonical_boxed_908_; lean_object* v_res_909_; 
v_canonical_boxed_908_ = lean_unbox(v_canonical_907_);
v_res_909_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_904_, v_inst_905_, v_value_906_, v_canonical_boxed_908_);
return v_res_909_;
}
}
lean_object* l_Lean_Doc_mkVersoCodeFromRef(lean_object* v_m_910_, lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_value_913_, uint8_t v_canonical_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_911_, v_inst_912_, v_value_913_, v_canonical_914_);
return v___x_915_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoCodeFromRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_911_ = stack[1].m_obj;
lean_object* v_inst_912_ = stack[2].m_obj;
lean_object* v_value_913_ = stack[3].m_obj;
uint8_t v_canonical_914_ = stack[4].m_num;
lean_object* v_res_916_;
v_res_916_ = l_Lean_Doc_mkVersoCodeFromRef(lean_box(0), v_inst_911_, v_inst_912_, v_value_913_, v_canonical_914_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___boxed(lean_object* v_m_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_value_920_, lean_object* v_canonical_921_){
_start:
{
uint8_t v_canonical_boxed_922_; lean_object* v_res_923_; 
v_canonical_boxed_922_ = lean_unbox(v_canonical_921_);
v_res_923_ = l_Lean_Doc_mkVersoCodeFromRef(v_m_917_, v_inst_918_, v_inst_919_, v_value_920_, v_canonical_boxed_922_);
return v_res_923_;
}
}
lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(lean_object* v_value_924_, uint8_t v_canonical_925_, lean_object* v_toPure_926_, lean_object* v_____do__lift_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_____do__lift_927_, v_value_924_, v_canonical_925_);
v___x_929_ = lean_apply_2(v_toPure_926_, lean_box(0), v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_924_ = stack[0].m_obj;
uint8_t v_canonical_925_ = stack[1].m_num;
lean_object* v_toPure_926_ = stack[2].m_obj;
lean_object* v_____do__lift_927_ = stack[3].m_obj;
lean_object* v_res_930_;
v_res_930_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(v_value_924_, v_canonical_925_, v_toPure_926_, v_____do__lift_927_);
stack->m_obj
 = v_res_930_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed(lean_object* v_value_931_, lean_object* v_canonical_932_, lean_object* v_toPure_933_, lean_object* v_____do__lift_934_){
_start:
{
uint8_t v_canonical_boxed_935_; lean_object* v_res_936_; 
v_canonical_boxed_935_ = lean_unbox(v_canonical_932_);
v_res_936_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(v_value_931_, v_canonical_boxed_935_, v_toPure_933_, v_____do__lift_934_);
lean_dec(v_____do__lift_934_);
lean_dec_ref(v_value_931_);
return v_res_936_;
}
}
lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_value_939_, uint8_t v_canonical_940_){
_start:
{
lean_object* v_toApplicative_941_; lean_object* v_toBind_942_; lean_object* v_getRef_943_; lean_object* v_toPure_944_; lean_object* v___x_945_; lean_object* v___f_946_; lean_object* v___x_947_; 
v_toApplicative_941_ = lean_ctor_get(v_inst_937_, 0);
lean_inc_ref(v_toApplicative_941_);
v_toBind_942_ = lean_ctor_get(v_inst_937_, 1);
lean_inc(v_toBind_942_);
lean_dec_ref(v_inst_937_);
v_getRef_943_ = lean_ctor_get(v_inst_938_, 0);
lean_inc(v_getRef_943_);
lean_dec_ref(v_inst_938_);
v_toPure_944_ = lean_ctor_get(v_toApplicative_941_, 1);
lean_inc(v_toPure_944_);
lean_dec_ref(v_toApplicative_941_);
v___x_945_ = lean_box(v_canonical_940_);
v___f_946_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_946_, 0, v_value_939_);
lean_closure_set(v___f_946_, 1, v___x_945_);
lean_closure_set(v___f_946_, 2, v_toPure_944_);
v___x_947_ = lean_apply_4(v_toBind_942_, lean_box(0), lean_box(0), v_getRef_943_, v___f_946_);
return v___x_947_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoCodeBlockFromRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_937_ = stack[0].m_obj;
lean_object* v_inst_938_ = stack[1].m_obj;
lean_object* v_value_939_ = stack[2].m_obj;
uint8_t v_canonical_940_ = stack[3].m_num;
lean_object* v_res_948_;
v_res_948_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_937_, v_inst_938_, v_value_939_, v_canonical_940_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___boxed(lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_value_951_, lean_object* v_canonical_952_){
_start:
{
uint8_t v_canonical_boxed_953_; lean_object* v_res_954_; 
v_canonical_boxed_953_ = lean_unbox(v_canonical_952_);
v_res_954_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_949_, v_inst_950_, v_value_951_, v_canonical_boxed_953_);
return v_res_954_;
}
}
lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef(lean_object* v_m_955_, lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_value_958_, uint8_t v_canonical_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_956_, v_inst_957_, v_value_958_, v_canonical_959_);
return v___x_960_;
}
}
LEAN_EXPORT void l_Lean_Doc_mkVersoCodeBlockFromRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_956_ = stack[1].m_obj;
lean_object* v_inst_957_ = stack[2].m_obj;
lean_object* v_value_958_ = stack[3].m_obj;
uint8_t v_canonical_959_ = stack[4].m_num;
lean_object* v_res_961_;
v_res_961_ = l_Lean_Doc_mkVersoCodeBlockFromRef(lean_box(0), v_inst_956_, v_inst_957_, v_value_958_, v_canonical_959_);
stack->m_obj
 = v_res_961_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___boxed(lean_object* v_m_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_value_965_, lean_object* v_canonical_966_){
_start:
{
uint8_t v_canonical_boxed_967_; lean_object* v_res_968_; 
v_canonical_boxed_967_ = lean_unbox(v_canonical_966_);
v_res_968_ = l_Lean_Doc_mkVersoCodeBlockFromRef(v_m_962_, v_inst_963_, v_inst_964_, v_value_965_, v_canonical_boxed_967_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_of(lean_object* v_stx_996_){
_start:
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__2));
lean_inc(v_stx_996_);
v___x_998_ = l_Lean_Syntax_isOfKind(v_stx_996_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__4));
lean_inc(v_stx_996_);
v___x_1000_ = l_Lean_Syntax_isOfKind(v_stx_996_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
lean_dec(v_stx_996_);
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v_o_1003_; lean_object* v___x_1004_; lean_object* v_name_1005_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v_o_1003_ = l_Lean_Syntax_getArg(v_stx_996_, v___x_1002_);
v___x_1004_ = lean_unsigned_to_nat(1u);
v_name_1005_ = l_Lean_Syntax_getArg(v_stx_996_, v___x_1004_);
if (v___x_998_ == 0)
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_1005_);
v___x_1012_ = l_Lean_Syntax_isOfKind(v_name_1005_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
lean_dec(v_name_1005_);
lean_dec(v_o_1003_);
lean_dec(v_stx_996_);
v___x_1013_ = lean_box(0);
return v___x_1013_;
}
else
{
goto v___jp_1006_;
}
}
else
{
goto v___jp_1006_;
}
v___jp_1006_:
{
lean_object* v___x_1007_; lean_object* v_c_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1007_ = lean_unsigned_to_nat(2u);
v_c_1008_ = l_Lean_Syntax_getArg(v_stx_996_, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1009_, 0, v_stx_996_);
lean_ctor_set(v___x_1009_, 1, v_o_1003_);
lean_ctor_set(v___x_1009_, 2, v_name_1005_);
lean_ctor_set(v___x_1009_, 3, v_c_1008_);
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v_url_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1014_ = lean_unsigned_to_nat(1u);
v_url_1015_ = l_Lean_Syntax_getArg(v_stx_996_, v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__8));
lean_inc(v_url_1015_);
v___x_1017_ = l_Lean_Syntax_isOfKind(v_url_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec(v_url_1015_);
lean_dec(v_stx_996_);
v___x_1018_ = lean_box(0);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v_o_1020_; lean_object* v___x_1021_; lean_object* v_c_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1019_ = lean_unsigned_to_nat(0u);
v_o_1020_ = l_Lean_Syntax_getArg(v_stx_996_, v___x_1019_);
v___x_1021_ = lean_unsigned_to_nat(2u);
v_c_1022_ = l_Lean_Syntax_getArg(v_stx_996_, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1023_, 0, v_stx_996_);
lean_ctor_set(v___x_1023_, 1, v_o_1020_);
lean_ctor_set(v___x_1023_, 2, v_url_1015_);
lean_ctor_set(v___x_1023_, 3, v_c_1022_);
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText(lean_object* v_v_1029_){
_start:
{
lean_object* v_content_1030_; lean_object* v___x_1031_; 
v_content_1030_ = lean_ctor_get(v_v_1029_, 1);
v___x_1031_ = l_Lean_TSyntax_getVersoText(v_content_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText___boxed(lean_object* v_v_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Doc_TextView_getVersoText(v_v_1032_);
lean_dec_ref(v_v_1032_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object* v_v_1034_){
_start:
{
lean_object* v_content_1035_; lean_object* v___x_1036_; 
v_content_1035_ = lean_ctor_get(v_v_1034_, 1);
v___x_1036_ = l_Lean_TSyntax_getVersoTextSource(v_content_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource___boxed(lean_object* v_v_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Doc_TextView_getVersoTextSource(v_v_1037_);
lean_dec_ref(v_v_1037_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_of(lean_object* v_stx_1052_){
_start:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__1));
lean_inc(v_stx_1052_);
v___x_1054_ = l_Lean_Syntax_isOfKind(v_stx_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_dec(v_stx_1052_);
v___x_1055_ = lean_box(0);
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; lean_object* v_s_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1056_ = lean_unsigned_to_nat(0u);
v_s_1057_ = l_Lean_Syntax_getArg(v_stx_1052_, v___x_1056_);
v___x_1058_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__3));
lean_inc(v_s_1057_);
v___x_1059_ = l_Lean_Syntax_isOfKind(v_s_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
lean_dec(v_s_1057_);
lean_dec(v_stx_1052_);
v___x_1060_ = lean_box(0);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_stx_1052_);
lean_ctor_set(v___x_1061_, 1, v_s_1057_);
v___x_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_EmphView_of(lean_object* v_stx_1076_){
_start:
{
lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_Doc_EmphView_of___closed__1));
lean_inc(v_stx_1076_);
v___x_1078_ = l_Lean_Syntax_isOfKind(v_stx_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v_stx_1076_);
v___x_1079_ = lean_box(0);
return v___x_1079_;
}
else
{
lean_object* v___x_1080_; lean_object* v_o_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1080_ = lean_unsigned_to_nat(0u);
v_o_1081_ = l_Lean_Syntax_getArg(v_stx_1076_, v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Lean_Doc_EmphView_of___closed__3));
lean_inc(v_o_1081_);
v___x_1083_ = l_Lean_Syntax_isOfKind(v_o_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec(v_o_1081_);
lean_dec(v_stx_1076_);
v___x_1084_ = lean_box(0);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v_c_1086_; uint8_t v___x_1087_; 
v___x_1085_ = lean_unsigned_to_nat(2u);
v_c_1086_ = l_Lean_Syntax_getArg(v_stx_1076_, v___x_1085_);
lean_inc(v_c_1086_);
v___x_1087_ = l_Lean_Syntax_isOfKind(v_c_1086_, v___x_1082_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_dec(v_c_1086_);
lean_dec(v_o_1081_);
lean_dec(v_stx_1076_);
v___x_1088_ = lean_box(0);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_inl_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = l_Lean_Syntax_getArg(v_stx_1076_, v___x_1089_);
v_inl_1091_ = l_Lean_Syntax_getArgs(v___x_1090_);
lean_dec(v___x_1090_);
v___x_1092_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1092_, 0, v_stx_1076_);
lean_ctor_set(v___x_1092_, 1, v_o_1081_);
lean_ctor_set(v___x_1092_, 2, v_inl_1091_);
lean_ctor_set(v___x_1092_, 3, v_c_1086_);
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BoldView_of(lean_object* v_stx_1107_){
_start:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_Doc_BoldView_of___closed__1));
lean_inc(v_stx_1107_);
v___x_1109_ = l_Lean_Syntax_isOfKind(v_stx_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec(v_stx_1107_);
v___x_1110_ = lean_box(0);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; lean_object* v_o_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1111_ = lean_unsigned_to_nat(0u);
v_o_1112_ = l_Lean_Syntax_getArg(v_stx_1107_, v___x_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_Doc_BoldView_of___closed__3));
lean_inc(v_o_1112_);
v___x_1114_ = l_Lean_Syntax_isOfKind(v_o_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec(v_o_1112_);
lean_dec(v_stx_1107_);
v___x_1115_ = lean_box(0);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; lean_object* v_c_1117_; uint8_t v___x_1118_; 
v___x_1116_ = lean_unsigned_to_nat(2u);
v_c_1117_ = l_Lean_Syntax_getArg(v_stx_1107_, v___x_1116_);
lean_inc(v_c_1117_);
v___x_1118_ = l_Lean_Syntax_isOfKind(v_c_1117_, v___x_1113_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec(v_c_1117_);
lean_dec(v_o_1112_);
lean_dec(v_stx_1107_);
v___x_1119_ = lean_box(0);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_inl_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1120_ = lean_unsigned_to_nat(1u);
v___x_1121_ = l_Lean_Syntax_getArg(v_stx_1107_, v___x_1120_);
v_inl_1122_ = l_Lean_Syntax_getArgs(v___x_1121_);
lean_dec(v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1123_, 0, v_stx_1107_);
lean_ctor_set(v___x_1123_, 1, v_o_1112_);
lean_ctor_set(v___x_1123_, 2, v_inl_1122_);
lean_ctor_set(v___x_1123_, 3, v_c_1117_);
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object* v_v_1125_){
_start:
{
lean_object* v_content_1126_; lean_object* v___x_1127_; 
v_content_1126_ = lean_ctor_get(v_v_1125_, 2);
v___x_1127_ = l_Lean_TSyntax_getVersoCode(v_content_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode___boxed(lean_object* v_v_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Doc_CodeView_getVersoCode(v_v_1128_);
lean_dec_ref(v_v_1128_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_of(lean_object* v_stx_1149_){
_start:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v_stx_1149_);
v___x_1151_ = l_Lean_Syntax_isOfKind(v_stx_1149_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
lean_dec(v_stx_1149_);
v___x_1152_ = lean_box(0);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; lean_object* v_o_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1153_ = lean_unsigned_to_nat(0u);
v_o_1154_ = l_Lean_Syntax_getArg(v_stx_1149_, v___x_1153_);
v___x_1155_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__3));
lean_inc(v_o_1154_);
v___x_1156_ = l_Lean_Syntax_isOfKind(v_o_1154_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec(v_o_1154_);
lean_dec(v_stx_1149_);
v___x_1157_ = lean_box(0);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; lean_object* v_s_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v_s_1159_ = l_Lean_Syntax_getArg(v_stx_1149_, v___x_1158_);
v___x_1160_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__5));
lean_inc(v_s_1159_);
v___x_1161_ = l_Lean_Syntax_isOfKind(v_s_1159_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
lean_dec(v_s_1159_);
lean_dec(v_o_1154_);
lean_dec(v_stx_1149_);
v___x_1162_ = lean_box(0);
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; lean_object* v_c_1164_; uint8_t v___x_1165_; 
v___x_1163_ = lean_unsigned_to_nat(2u);
v_c_1164_ = l_Lean_Syntax_getArg(v_stx_1149_, v___x_1163_);
lean_inc(v_c_1164_);
v___x_1165_ = l_Lean_Syntax_isOfKind(v_c_1164_, v___x_1155_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec(v_c_1164_);
lean_dec(v_s_1159_);
lean_dec(v_o_1154_);
lean_dec(v_stx_1149_);
v___x_1166_ = lean_box(0);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1167_, 0, v_stx_1149_);
lean_ctor_set(v___x_1167_, 1, v_o_1154_);
lean_ctor_set(v___x_1167_, 2, v_s_1159_);
lean_ctor_set(v___x_1167_, 3, v_c_1164_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object* v_v_1169_){
_start:
{
lean_object* v_code_1170_; lean_object* v___x_1171_; 
v_code_1170_ = lean_ctor_get(v_v_1169_, 2);
v___x_1171_ = l_Lean_Doc_CodeView_getVersoCode(v_code_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode___boxed(lean_object* v_v_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Doc_MathView_getVersoCode(v_v_1172_);
lean_dec_ref(v_v_1172_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_of(lean_object* v_stx_1200_){
_start:
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__1));
lean_inc(v_stx_1200_);
v___x_1202_ = l_Lean_Syntax_isOfKind(v_stx_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__3));
lean_inc(v_stx_1200_);
v___x_1204_ = l_Lean_Syntax_isOfKind(v_stx_1200_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
lean_dec(v_stx_1200_);
v___x_1205_ = lean_box(0);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___y_1209_; 
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = l_Lean_Syntax_getArg(v_stx_1200_, v___x_1206_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__5));
lean_inc(v___x_1207_);
v___x_1229_ = l_Lean_Syntax_isOfKind(v___x_1207_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
lean_dec(v___x_1207_);
lean_dec(v_stx_1200_);
v___x_1230_ = lean_box(0);
return v___x_1230_;
}
else
{
goto v___jp_1222_;
}
}
else
{
goto v___jp_1222_;
}
v___jp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Doc_CodeView_of(v___y_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1211_; 
lean_dec(v___x_1207_);
lean_dec(v_stx_1200_);
v___x_1211_ = lean_box(0);
return v___x_1211_;
}
else
{
lean_object* v_val_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1221_; 
v_val_1212_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1214_ = v___x_1210_;
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_val_1212_);
lean_dec(v___x_1210_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1216_ = 1;
v___x_1217_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1217_, 0, v_stx_1200_);
lean_ctor_set(v___x_1217_, 1, v___x_1207_);
lean_ctor_set(v___x_1217_, 2, v_val_1212_);
lean_ctor_set_uint8(v___x_1217_, sizeof(void*)*3, v___x_1216_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1217_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
v___jp_1222_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = l_Lean_Syntax_getArg(v_stx_1200_, v___x_1223_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v___x_1224_);
v___x_1226_ = l_Lean_Syntax_isOfKind(v___x_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; 
lean_dec(v___x_1224_);
lean_dec(v___x_1207_);
lean_dec(v_stx_1200_);
v___x_1227_ = lean_box(0);
return v___x_1227_;
}
else
{
v___y_1209_ = v___x_1224_;
goto v___jp_1208_;
}
}
else
{
v___y_1209_ = v___x_1224_;
goto v___jp_1208_;
}
}
}
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = l_Lean_Syntax_getArg(v_stx_1200_, v___x_1231_);
v___x_1233_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__7));
lean_inc(v___x_1232_);
v___x_1234_ = l_Lean_Syntax_isOfKind(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v___x_1232_);
lean_dec(v_stx_1200_);
v___x_1235_ = lean_box(0);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = l_Lean_Syntax_getArg(v_stx_1200_, v___x_1236_);
v___x_1238_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v___x_1237_);
v___x_1239_ = l_Lean_Syntax_isOfKind(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec(v___x_1237_);
lean_dec(v___x_1232_);
lean_dec(v_stx_1200_);
v___x_1240_ = lean_box(0);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Doc_CodeView_of(v___x_1237_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1242_; 
lean_dec(v___x_1232_);
lean_dec(v_stx_1200_);
v___x_1242_ = lean_box(0);
return v___x_1242_;
}
else
{
lean_object* v_val_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1252_; 
v_val_1243_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1245_ = v___x_1241_;
v_isShared_1246_ = v_isSharedCheck_1252_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_val_1243_);
lean_dec(v___x_1241_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1252_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1247_ = 0;
v___x_1248_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1248_, 0, v_stx_1200_);
lean_ctor_set(v___x_1248_, 1, v___x_1232_);
lean_ctor_set(v___x_1248_, 2, v_val_1243_);
lean_ctor_set_uint8(v___x_1248_, sizeof(void*)*3, v___x_1247_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1248_);
v___x_1250_ = v___x_1245_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkView_of(lean_object* v_stx_1260_){
_start:
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = ((lean_object*)(l_Lean_Doc_LinkView_of___closed__1));
lean_inc(v_stx_1260_);
v___x_1262_ = l_Lean_Syntax_isOfKind(v_stx_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_dec(v_stx_1260_);
v___x_1263_ = lean_box(0);
return v___x_1263_;
}
else
{
lean_object* v___x_1264_; lean_object* v_tgt_1265_; lean_object* v___x_1266_; 
v___x_1264_ = lean_unsigned_to_nat(3u);
v_tgt_1265_ = l_Lean_Syntax_getArg(v_stx_1260_, v___x_1264_);
v___x_1266_ = l_Lean_Doc_LinkTargetView_of(v_tgt_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; 
lean_dec(v_stx_1260_);
v___x_1267_ = lean_box(0);
return v___x_1267_;
}
else
{
lean_object* v_val_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1283_; 
v_val_1268_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1270_ = v___x_1266_;
v_isShared_1271_ = v_isSharedCheck_1283_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_val_1268_);
lean_dec(v___x_1266_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1283_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v_o_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_c_1277_; lean_object* v_inl_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1272_ = lean_unsigned_to_nat(0u);
v_o_1273_ = l_Lean_Syntax_getArg(v_stx_1260_, v___x_1272_);
v___x_1274_ = lean_unsigned_to_nat(1u);
v___x_1275_ = l_Lean_Syntax_getArg(v_stx_1260_, v___x_1274_);
v___x_1276_ = lean_unsigned_to_nat(2u);
v_c_1277_ = l_Lean_Syntax_getArg(v_stx_1260_, v___x_1276_);
v_inl_1278_ = l_Lean_Syntax_getArgs(v___x_1275_);
lean_dec(v___x_1275_);
v___x_1279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1279_, 0, v_stx_1260_);
lean_ctor_set(v___x_1279_, 1, v_o_1273_);
lean_ctor_set(v___x_1279_, 2, v_inl_1278_);
lean_ctor_set(v___x_1279_, 3, v_c_1277_);
lean_ctor_set(v___x_1279_, 4, v_val_1268_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1279_);
v___x_1281_ = v___x_1270_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt(lean_object* v_v_1284_){
_start:
{
lean_object* v_alt_1285_; lean_object* v___x_1286_; 
v_alt_1285_ = lean_ctor_get(v_v_1284_, 2);
v___x_1286_ = l_Lean_TSyntax_getVersoImageAlt(v_alt_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt___boxed(lean_object* v_v_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Doc_ImageView_getAlt(v_v_1287_);
lean_dec_ref(v_v_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_of(lean_object* v_stx_1302_){
_start:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__1));
lean_inc(v_stx_1302_);
v___x_1304_ = l_Lean_Syntax_isOfKind(v_stx_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec(v_stx_1302_);
v___x_1305_ = lean_box(0);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; lean_object* v_alt_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1306_ = lean_unsigned_to_nat(1u);
v_alt_1307_ = l_Lean_Syntax_getArg(v_stx_1302_, v___x_1306_);
v___x_1308_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__3));
lean_inc(v_alt_1307_);
v___x_1309_ = l_Lean_Syntax_isOfKind(v_alt_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
lean_dec(v_alt_1307_);
lean_dec(v_stx_1302_);
v___x_1310_ = lean_box(0);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; lean_object* v_tgt_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_unsigned_to_nat(3u);
v_tgt_1312_ = l_Lean_Syntax_getArg(v_stx_1302_, v___x_1311_);
v___x_1313_ = l_Lean_Doc_LinkTargetView_of(v_tgt_1312_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v___x_1314_; 
lean_dec(v_alt_1307_);
lean_dec(v_stx_1302_);
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
else
{
lean_object* v_val_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1327_; 
v_val_1315_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1317_ = v___x_1313_;
v_isShared_1318_ = v_isSharedCheck_1327_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_val_1315_);
lean_dec(v___x_1313_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1327_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v_o_1320_; lean_object* v___x_1321_; lean_object* v_c_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1319_ = lean_unsigned_to_nat(0u);
v_o_1320_ = l_Lean_Syntax_getArg(v_stx_1302_, v___x_1319_);
v___x_1321_ = lean_unsigned_to_nat(2u);
v_c_1322_ = l_Lean_Syntax_getArg(v_stx_1302_, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1323_, 0, v_stx_1302_);
lean_ctor_set(v___x_1323_, 1, v_o_1320_);
lean_ctor_set(v___x_1323_, 2, v_alt_1307_);
lean_ctor_set(v___x_1323_, 3, v_c_1322_);
lean_ctor_set(v___x_1323_, 4, v_val_1315_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1323_);
v___x_1325_ = v___x_1317_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName(lean_object* v_v_1328_){
_start:
{
lean_object* v_name_1329_; lean_object* v___x_1330_; 
v_name_1329_ = lean_ctor_get(v_v_1328_, 2);
v___x_1330_ = l_Lean_TSyntax_getVersoRefName(v_name_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName___boxed(lean_object* v_v_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Doc_FootnoteView_getName(v_v_1331_);
lean_dec_ref(v_v_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_of(lean_object* v_stx_1340_){
_start:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = ((lean_object*)(l_Lean_Doc_FootnoteView_of___closed__1));
lean_inc(v_stx_1340_);
v___x_1342_ = l_Lean_Syntax_isOfKind(v_stx_1340_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
lean_dec(v_stx_1340_);
v___x_1343_ = lean_box(0);
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; lean_object* v_name_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1344_ = lean_unsigned_to_nat(1u);
v_name_1345_ = l_Lean_Syntax_getArg(v_stx_1340_, v___x_1344_);
v___x_1346_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_1345_);
v___x_1347_ = l_Lean_Syntax_isOfKind(v_name_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec(v_name_1345_);
lean_dec(v_stx_1340_);
v___x_1348_ = lean_box(0);
return v___x_1348_;
}
else
{
lean_object* v___x_1349_; lean_object* v_o_1350_; lean_object* v___x_1351_; lean_object* v_c_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1349_ = lean_unsigned_to_nat(0u);
v_o_1350_ = l_Lean_Syntax_getArg(v_stx_1340_, v___x_1349_);
v___x_1351_ = lean_unsigned_to_nat(2u);
v_c_1352_ = l_Lean_Syntax_getArg(v_stx_1340_, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1353_, 0, v_stx_1340_);
lean_ctor_set(v___x_1353_, 1, v_o_1350_);
lean_ctor_set(v___x_1353_, 2, v_name_1345_);
lean_ctor_set(v___x_1353_, 3, v_c_1352_);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinebreakView_of(lean_object* v_stx_1355_){
_start:
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
lean_inc(v_stx_1355_);
v___x_1357_ = l_Lean_Syntax_isOfKind(v_stx_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec(v_stx_1355_);
v___x_1358_ = lean_box(0);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = l_Lean_Syntax_getArg(v_stx_1355_, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_stx_1355_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_RoleView_of(lean_object* v_stx_1370_){
_start:
{
lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = ((lean_object*)(l_Lean_Doc_RoleView_of___closed__1));
lean_inc(v_stx_1370_);
v___x_1372_ = l_Lean_Syntax_isOfKind(v_stx_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; 
lean_dec(v_stx_1370_);
v___x_1373_ = lean_box(0);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; lean_object* v_name_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1374_ = lean_unsigned_to_nat(1u);
v_name_1375_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_1375_);
v___x_1377_ = l_Lean_Syntax_isOfKind(v_name_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
lean_dec(v_name_1375_);
lean_dec(v_stx_1370_);
v___x_1378_ = lean_box(0);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; lean_object* v_bo_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_bc_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1379_ = lean_unsigned_to_nat(0u);
v_bo_1380_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1379_);
v___x_1381_ = lean_unsigned_to_nat(2u);
v___x_1382_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1381_);
v___x_1383_ = lean_unsigned_to_nat(3u);
v_bc_1384_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1383_);
v___x_1385_ = lean_unsigned_to_nat(4u);
v___x_1386_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1385_);
lean_inc(v___x_1386_);
v___x_1387_ = l_Lean_Syntax_matchesNull(v___x_1386_, v___x_1374_);
if (v___x_1387_ == 0)
{
uint8_t v___x_1388_; 
v___x_1388_ = l_Lean_Syntax_matchesNull(v___x_1386_, v___x_1379_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
lean_dec(v_bc_1384_);
lean_dec(v___x_1382_);
lean_dec(v_bo_1380_);
lean_dec(v_name_1375_);
lean_dec(v_stx_1370_);
v___x_1389_ = lean_box(0);
return v___x_1389_;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1390_ = lean_unsigned_to_nat(6u);
v___x_1391_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1390_);
v___x_1392_ = l_Lean_Syntax_matchesNull(v___x_1391_, v___x_1379_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
lean_dec(v_bc_1384_);
lean_dec(v___x_1382_);
lean_dec(v_bo_1380_);
lean_dec(v_name_1375_);
lean_dec(v_stx_1370_);
v___x_1393_ = lean_box(0);
return v___x_1393_;
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_inl_1396_; lean_object* v_args_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1394_ = lean_unsigned_to_nat(5u);
v___x_1395_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1394_);
v_inl_1396_ = l_Lean_Syntax_getArgs(v___x_1395_);
lean_dec(v___x_1395_);
v_args_1397_ = l_Lean_Syntax_getArgs(v___x_1382_);
lean_dec(v___x_1382_);
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1399_, 0, v_stx_1370_);
lean_ctor_set(v___x_1399_, 1, v_bo_1380_);
lean_ctor_set(v___x_1399_, 2, v_name_1375_);
lean_ctor_set(v___x_1399_, 3, v_args_1397_);
lean_ctor_set(v___x_1399_, 4, v_bc_1384_);
lean_ctor_set(v___x_1399_, 5, v___x_1398_);
lean_ctor_set(v___x_1399_, 6, v_inl_1396_);
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1401_ = lean_unsigned_to_nat(6u);
v___x_1402_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1401_);
lean_inc(v___x_1402_);
v___x_1403_ = l_Lean_Syntax_matchesNull(v___x_1402_, v___x_1374_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_dec(v___x_1402_);
lean_dec(v___x_1386_);
lean_dec(v_bc_1384_);
lean_dec(v___x_1382_);
lean_dec(v_bo_1380_);
lean_dec(v_name_1375_);
lean_dec(v_stx_1370_);
v___x_1404_ = lean_box(0);
return v___x_1404_;
}
else
{
lean_object* v_so_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v_sc_1408_; lean_object* v_inl_1409_; lean_object* v_args_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_so_1405_ = l_Lean_Syntax_getArg(v___x_1386_, v___x_1379_);
lean_dec(v___x_1386_);
v___x_1406_ = lean_unsigned_to_nat(5u);
v___x_1407_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1406_);
v_sc_1408_ = l_Lean_Syntax_getArg(v___x_1402_, v___x_1379_);
lean_dec(v___x_1402_);
v_inl_1409_ = l_Lean_Syntax_getArgs(v___x_1407_);
lean_dec(v___x_1407_);
v_args_1410_ = l_Lean_Syntax_getArgs(v___x_1382_);
lean_dec(v___x_1382_);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_so_1405_);
lean_ctor_set(v___x_1411_, 1, v_sc_1408_);
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1413_, 0, v_stx_1370_);
lean_ctor_set(v___x_1413_, 1, v_bo_1380_);
lean_ctor_set(v___x_1413_, 2, v_name_1375_);
lean_ctor_set(v___x_1413_, 3, v_args_1410_);
lean_ctor_set(v___x_1413_, 4, v_bc_1384_);
lean_ctor_set(v___x_1413_, 5, v___x_1412_);
lean_ctor_set(v___x_1413_, 6, v_inl_1409_);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___impl(lean_object* v_x_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_obj_tag_nat(v_x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___impl___boxed(lean_object* v_x_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Doc_InlineView_ctorIdx___impl(v_x_1417_);
lean_dec_ref(v_x_1417_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___redArg(lean_object* v_t_1419_, lean_object* v_k_1420_){
_start:
{
lean_object* v_view_1421_; lean_object* v___x_1422_; 
v_view_1421_ = lean_ctor_get(v_t_1419_, 0);
lean_inc_ref(v_view_1421_);
lean_dec_ref(v_t_1419_);
v___x_1422_ = lean_apply_1(v_k_1420_, v_view_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim(lean_object* v_motive_1423_, lean_object* v_ctorIdx_1424_, lean_object* v_t_1425_, lean_object* v_h_1426_, lean_object* v_k_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1425_, v_k_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___boxed(lean_object* v_motive_1429_, lean_object* v_ctorIdx_1430_, lean_object* v_t_1431_, lean_object* v_h_1432_, lean_object* v_k_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_Doc_InlineView_ctorElim(v_motive_1429_, v_ctorIdx_1430_, v_t_1431_, v_h_1432_, v_k_1433_);
lean_dec(v_ctorIdx_1430_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim___redArg(lean_object* v_t_1435_, lean_object* v_text_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1435_, v_text_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim(lean_object* v_motive_1438_, lean_object* v_t_1439_, lean_object* v_h_1440_, lean_object* v_text_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1439_, v_text_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim___redArg(lean_object* v_t_1443_, lean_object* v_emph_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1443_, v_emph_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim(lean_object* v_motive_1446_, lean_object* v_t_1447_, lean_object* v_h_1448_, lean_object* v_emph_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1447_, v_emph_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim___redArg(lean_object* v_t_1451_, lean_object* v_bold_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1451_, v_bold_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim(lean_object* v_motive_1454_, lean_object* v_t_1455_, lean_object* v_h_1456_, lean_object* v_bold_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1455_, v_bold_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim___redArg(lean_object* v_t_1459_, lean_object* v_code_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1459_, v_code_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim(lean_object* v_motive_1462_, lean_object* v_t_1463_, lean_object* v_h_1464_, lean_object* v_code_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1463_, v_code_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim___redArg(lean_object* v_t_1467_, lean_object* v_math_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1467_, v_math_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim(lean_object* v_motive_1470_, lean_object* v_t_1471_, lean_object* v_h_1472_, lean_object* v_math_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1471_, v_math_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim___redArg(lean_object* v_t_1475_, lean_object* v_link_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1475_, v_link_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim(lean_object* v_motive_1478_, lean_object* v_t_1479_, lean_object* v_h_1480_, lean_object* v_link_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1479_, v_link_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim___redArg(lean_object* v_t_1483_, lean_object* v_image_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1483_, v_image_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim(lean_object* v_motive_1486_, lean_object* v_t_1487_, lean_object* v_h_1488_, lean_object* v_image_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1487_, v_image_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim___redArg(lean_object* v_t_1491_, lean_object* v_footnote_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1491_, v_footnote_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim(lean_object* v_motive_1494_, lean_object* v_t_1495_, lean_object* v_h_1496_, lean_object* v_footnote_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1495_, v_footnote_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim___redArg(lean_object* v_t_1499_, lean_object* v_linebreak_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1499_, v_linebreak_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim(lean_object* v_motive_1502_, lean_object* v_t_1503_, lean_object* v_h_1504_, lean_object* v_linebreak_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1503_, v_linebreak_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim___redArg(lean_object* v_t_1507_, lean_object* v_role_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1507_, v_role_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim(lean_object* v_motive_1510_, lean_object* v_t_1511_, lean_object* v_h_1512_, lean_object* v_role_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1511_, v_role_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTextViewInlineView___lam__0(lean_object* v_view_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_view_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeEmphViewInlineView___lam__0(lean_object* v_view_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_view_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBoldViewInlineView___lam__0(lean_object* v_view_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_view_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeViewInlineView___lam__0(lean_object* v_view_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_view_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMathViewInlineView___lam__0(lean_object* v_view_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1536_, 0, v_view_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkViewInlineView___lam__0(lean_object* v_view_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_view_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeImageViewInlineView___lam__0(lean_object* v_view_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_view_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0(lean_object* v_view_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_view_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0(lean_object* v_view_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_view_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeRoleViewInlineView___lam__0(lean_object* v_view_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_view_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx(lean_object* v_x_1559_){
_start:
{
lean_object* v_view_1560_; lean_object* v_stx_1561_; 
v_view_1560_ = lean_ctor_get(v_x_1559_, 0);
v_stx_1561_ = lean_ctor_get(v_view_1560_, 0);
lean_inc(v_stx_1561_);
return v_stx_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx___boxed(lean_object* v_x_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Doc_InlineView_stx(v_x_1562_);
lean_dec_ref(v_x_1562_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_of(lean_object* v_stx_1564_){
_start:
{
lean_object* v___x_1565_; 
lean_inc(v_stx_1564_);
v___x_1565_ = l_Lean_Doc_TextView_of(v_stx_1564_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v___x_1566_; 
lean_inc(v_stx_1564_);
v___x_1566_ = l_Lean_Doc_EmphView_of(v_stx_1564_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v___x_1567_; 
lean_inc(v_stx_1564_);
v___x_1567_ = l_Lean_Doc_BoldView_of(v_stx_1564_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1568_; 
lean_inc(v_stx_1564_);
v___x_1568_ = l_Lean_Doc_CodeView_of(v_stx_1564_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v___x_1569_; 
lean_inc(v_stx_1564_);
v___x_1569_ = l_Lean_Doc_MathView_of(v_stx_1564_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1570_; 
lean_inc(v_stx_1564_);
v___x_1570_ = l_Lean_Doc_LinkView_of(v_stx_1564_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1571_; 
lean_inc(v_stx_1564_);
v___x_1571_ = l_Lean_Doc_ImageView_of(v_stx_1564_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1572_; 
lean_inc(v_stx_1564_);
v___x_1572_ = l_Lean_Doc_FootnoteView_of(v_stx_1564_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; 
lean_inc(v_stx_1564_);
v___x_1573_ = l_Lean_Doc_LinebreakView_of(v_stx_1564_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Doc_RoleView_of(v_stx_1564_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_box(0);
return v___x_1575_;
}
else
{
lean_object* v_val_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1584_; 
v_val_1576_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1578_ = v___x_1574_;
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_val_1576_);
lean_dec(v___x_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = lean_alloc_ctor(9, 1, 0);
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
lean_dec(v_stx_1564_);
v_val_1585_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1587_ = v___x_1573_;
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_val_1585_);
lean_dec(v___x_1573_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1589_ = lean_alloc_ctor(8, 1, 0);
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
lean_dec(v_stx_1564_);
v_val_1594_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1596_ = v___x_1572_;
v_isShared_1597_ = v_isSharedCheck_1602_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_val_1594_);
lean_dec(v___x_1572_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1602_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = lean_alloc_ctor(7, 1, 0);
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
lean_dec(v_stx_1564_);
v_val_1603_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1605_ = v___x_1571_;
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_val_1603_);
lean_dec(v___x_1571_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_alloc_ctor(6, 1, 0);
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
lean_dec(v_stx_1564_);
v_val_1612_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1614_ = v___x_1570_;
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_val_1612_);
lean_dec(v___x_1570_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = lean_alloc_ctor(5, 1, 0);
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
lean_dec(v_stx_1564_);
v_val_1621_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1623_ = v___x_1569_;
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_val_1621_);
lean_dec(v___x_1569_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = lean_alloc_ctor(4, 1, 0);
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
lean_dec(v_stx_1564_);
v_val_1630_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1632_ = v___x_1568_;
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_val_1630_);
lean_dec(v___x_1568_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = lean_alloc_ctor(3, 1, 0);
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
lean_dec(v_stx_1564_);
v_val_1639_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1641_ = v___x_1567_;
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_val_1639_);
lean_dec(v___x_1567_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_alloc_ctor(2, 1, 0);
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
else
{
lean_object* v_val_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_stx_1564_);
v_val_1648_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1650_ = v___x_1566_;
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_val_1648_);
lean_dec(v___x_1566_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v_val_1648_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1652_);
v___x_1654_ = v___x_1650_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
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
lean_object* v_val_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_stx_1564_);
v_val_1657_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1659_ = v___x_1565_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_val_1657_);
lean_dec(v___x_1565_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_val_1657_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
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
uint8_t l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(uint32_t v_a_1666_, lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1667_) == 0)
{
uint8_t v___x_1668_; 
v___x_1668_ = 0;
return v___x_1668_;
}
else
{
lean_object* v_head_1669_; lean_object* v_tail_1670_; uint32_t v___x_1671_; uint8_t v___x_1672_; 
v_head_1669_ = lean_ctor_get(v_x_1667_, 0);
v_tail_1670_ = lean_ctor_get(v_x_1667_, 1);
v___x_1671_ = lean_unbox_uint32(v_head_1669_);
v___x_1672_ = lean_uint32_dec_eq(v_a_1666_, v___x_1671_);
if (v___x_1672_ == 0)
{
v_x_1667_ = v_tail_1670_;
goto _start;
}
else
{
return v___x_1672_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1666_ = stack[0].m_num;
lean_object* v_x_1667_ = stack[1].m_obj;
uint8_t v_res_1674_;
v_res_1674_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v_a_1666_, v_x_1667_);
stack->m_num = v_res_1674_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0___boxed(lean_object* v_a_1675_, lean_object* v_x_1676_){
_start:
{
uint32_t v_a_boxed_1677_; uint8_t v_res_1678_; lean_object* v_r_1679_; 
v_a_boxed_1677_ = lean_unbox_uint32(v_a_1675_);
lean_dec(v_a_1675_);
v_res_1678_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v_a_boxed_1677_, v_x_1676_);
lean_dec(v_x_1676_);
v_r_1679_ = lean_box(v_res_1678_);
return v_r_1679_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = 43;
v___x_1695_ = lean_box_uint32(v___x_1694_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__5(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = lean_box(0);
v___x_1697_ = l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1;
v___x_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
lean_ctor_set(v___x_1698_, 1, v___x_1696_);
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = 45;
v___x_1700_ = lean_box_uint32(v___x_1699_);
return v___x_1700_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__6(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__5, &l_Lean_Doc_UnorderedListItemView_of___closed__5_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__5);
v___x_1702_ = l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1;
v___x_1703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v___x_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = 42;
v___x_1705_ = lean_box_uint32(v___x_1704_);
return v___x_1705_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__7(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__6, &l_Lean_Doc_UnorderedListItemView_of___closed__6_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__6);
v___x_1707_ = l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1;
v___x_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___x_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of(lean_object* v_stx_1709_){
_start:
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__2));
lean_inc(v_stx_1709_);
v___x_1711_ = l_Lean_Syntax_isOfKind(v_stx_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
lean_dec(v_stx_1709_);
v___x_1712_ = lean_box(0);
return v___x_1712_;
}
else
{
lean_object* v___x_1713_; lean_object* v_m_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1713_ = lean_unsigned_to_nat(0u);
v_m_1714_ = l_Lean_Syntax_getArg(v_stx_1709_, v___x_1713_);
v___x_1715_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__4));
lean_inc(v_m_1714_);
v___x_1716_ = l_Lean_Syntax_isOfKind(v_m_1714_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec(v_m_1714_);
lean_dec(v_stx_1709_);
v___x_1717_ = lean_box(0);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1718_ = l_Lean_TSyntax_getVersoDelimiter(v_m_1714_);
v___x_1719_ = lean_string_utf8_byte_size(v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1713_);
lean_ctor_set(v___x_1720_, 2, v___x_1719_);
v___x_1721_ = l_String_Slice_Pos_get_x3f(v___x_1720_, v___x_1713_);
lean_dec_ref_known(v___x_1720_, 3);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v___x_1722_; 
lean_dec(v_m_1714_);
lean_dec(v_stx_1709_);
v___x_1722_ = lean_box(0);
return v___x_1722_;
}
else
{
lean_object* v_val_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1738_; 
v_val_1723_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1725_ = v___x_1721_;
v_isShared_1726_ = v_isSharedCheck_1738_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_val_1723_);
lean_dec(v___x_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1738_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; uint32_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__7, &l_Lean_Doc_UnorderedListItemView_of___closed__7_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__7);
v___x_1728_ = lean_unbox_uint32(v_val_1723_);
lean_dec(v_val_1723_);
v___x_1729_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v___x_1728_, v___x_1727_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
lean_del_object(v___x_1725_);
lean_dec(v_m_1714_);
lean_dec(v_stx_1709_);
v___x_1730_ = lean_box(0);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v_bs_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = l_Lean_Syntax_getArg(v_stx_1709_, v___x_1731_);
v_bs_1733_ = l_Lean_Syntax_getArgs(v___x_1732_);
lean_dec(v___x_1732_);
v___x_1734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1734_, 0, v_stx_1709_);
lean_ctor_set(v___x_1734_, 1, v_m_1714_);
lean_ctor_set(v___x_1734_, 2, v_bs_1733_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1734_);
v___x_1736_ = v___x_1725_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(lean_object* v_s_1739_, lean_object* v_pos_1740_){
_start:
{
lean_object* v_str_1741_; lean_object* v_startInclusive_1742_; lean_object* v_endExclusive_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v_decide_1747_; 
v_str_1741_ = lean_ctor_get(v_s_1739_, 0);
v_startInclusive_1742_ = lean_ctor_get(v_s_1739_, 1);
v_endExclusive_1743_ = lean_ctor_get(v_s_1739_, 2);
v___x_1744_ = lean_nat_add(v_startInclusive_1742_, v_pos_1740_);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = lean_nat_sub(v_endExclusive_1743_, v___x_1744_);
v_decide_1747_ = lean_nat_dec_eq(v___x_1745_, v___x_1746_);
lean_dec(v___x_1746_);
if (v_decide_1747_ == 0)
{
uint32_t v___x_1748_; uint32_t v___x_1749_; uint8_t v___x_1750_; 
v___x_1748_ = lean_string_utf8_get_fast(v_str_1741_, v___x_1744_);
v___x_1749_ = 48;
v___x_1750_ = lean_uint32_dec_le(v___x_1749_, v___x_1748_);
if (v___x_1750_ == 0)
{
lean_dec(v___x_1744_);
return v_pos_1740_;
}
else
{
uint32_t v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = 57;
v___x_1752_ = lean_uint32_dec_le(v___x_1748_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec(v___x_1744_);
return v_pos_1740_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1753_ = lean_string_utf8_next_fast(v_str_1741_, v___x_1744_);
v___x_1754_ = lean_nat_sub(v___x_1753_, v___x_1744_);
lean_dec(v___x_1744_);
v___x_1755_ = lean_nat_add(v_pos_1740_, v___x_1754_);
lean_dec(v___x_1754_);
v___x_1756_ = lean_unsigned_to_nat(1u);
v___x_1757_ = lean_nat_add(v_pos_1740_, v___x_1756_);
v___x_1758_ = lean_nat_dec_le(v___x_1757_, v___x_1755_);
lean_dec(v___x_1757_);
if (v___x_1758_ == 0)
{
lean_dec(v___x_1755_);
return v_pos_1740_;
}
else
{
lean_dec(v_pos_1740_);
v_pos_1740_ = v___x_1755_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_1744_);
return v_pos_1740_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0___boxed(lean_object* v_s_1760_, lean_object* v_pos_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v_s_1760_, v_pos_1761_);
lean_dec_ref(v_s_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_number(lean_object* v_v_1763_){
_start:
{
lean_object* v_marker_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1779_; 
v_marker_1764_ = lean_ctor_get(v_v_1763_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_v_1763_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; lean_object* v_unused_1781_; 
v_unused_1780_ = lean_ctor_get(v_v_1763_, 2);
lean_dec(v_unused_1780_);
v_unused_1781_ = lean_ctor_get(v_v_1763_, 0);
lean_dec(v_unused_1781_);
v___x_1766_ = v_v_1763_;
v_isShared_1767_ = v_isSharedCheck_1779_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_marker_1764_);
lean_dec(v_v_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1779_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1768_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_1764_);
lean_dec(v_marker_1764_);
v___x_1769_ = lean_unsigned_to_nat(0u);
v___x_1770_ = lean_string_utf8_byte_size(v___x_1768_);
lean_inc_ref(v___x_1768_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 2, v___x_1770_);
lean_ctor_set(v___x_1766_, 1, v___x_1769_);
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1772_ = v___x_1766_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1773_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v___x_1772_, v___x_1769_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = lean_string_utf8_extract_fast(v___x_1768_, v___x_1769_, v___x_1773_);
lean_dec(v___x_1773_);
lean_dec_ref(v___x_1768_);
v___x_1775_ = lean_string_utf8_byte_size(v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1769_);
lean_ctor_set(v___x_1776_, 2, v___x_1775_);
v___x_1777_ = l_String_Slice_toNat_x3f(v___x_1776_);
lean_dec_ref_known(v___x_1776_, 3);
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_of(lean_object* v_stx_1782_){
_start:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__2));
lean_inc(v_stx_1782_);
v___x_1784_ = l_Lean_Syntax_isOfKind(v_stx_1782_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; 
lean_dec(v_stx_1782_);
v___x_1785_ = lean_box(0);
return v___x_1785_;
}
else
{
lean_object* v___x_1786_; lean_object* v_m_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1786_ = lean_unsigned_to_nat(0u);
v_m_1787_ = l_Lean_Syntax_getArg(v_stx_1782_, v___x_1786_);
v___x_1788_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__4));
lean_inc(v_m_1787_);
v___x_1789_ = l_Lean_Syntax_isOfKind(v_m_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; 
lean_dec(v_m_1787_);
lean_dec(v_stx_1782_);
v___x_1790_ = lean_box(0);
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1791_ = l_Lean_TSyntax_getVersoDelimiter(v_m_1787_);
v___x_1792_ = lean_string_utf8_byte_size(v___x_1791_);
v___x_1793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1786_);
lean_ctor_set(v___x_1793_, 2, v___x_1792_);
v___x_1794_ = l_String_Slice_Pos_get_x3f(v___x_1793_, v___x_1786_);
lean_dec_ref_known(v___x_1793_, 3);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v___x_1795_; 
lean_dec(v_m_1787_);
lean_dec(v_stx_1782_);
v___x_1795_ = lean_box(0);
return v___x_1795_;
}
else
{
lean_object* v_val_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1815_; 
v_val_1796_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1798_ = v___x_1794_;
v_isShared_1799_ = v_isSharedCheck_1815_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_val_1796_);
lean_dec(v___x_1794_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1815_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
uint32_t v___x_1800_; uint32_t v___x_1801_; uint8_t v___x_1802_; 
v___x_1800_ = 48;
v___x_1801_ = lean_unbox_uint32(v_val_1796_);
v___x_1802_ = lean_uint32_dec_le(v___x_1800_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
lean_del_object(v___x_1798_);
lean_dec(v_val_1796_);
lean_dec(v_m_1787_);
lean_dec(v_stx_1782_);
v___x_1803_ = lean_box(0);
return v___x_1803_;
}
else
{
uint32_t v___x_1804_; uint32_t v___x_1805_; uint8_t v___x_1806_; 
v___x_1804_ = 57;
v___x_1805_ = lean_unbox_uint32(v_val_1796_);
lean_dec(v_val_1796_);
v___x_1806_ = lean_uint32_dec_le(v___x_1805_, v___x_1804_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_del_object(v___x_1798_);
lean_dec(v_m_1787_);
lean_dec(v_stx_1782_);
v___x_1807_ = lean_box(0);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_bs_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1808_ = lean_unsigned_to_nat(1u);
v___x_1809_ = l_Lean_Syntax_getArg(v_stx_1782_, v___x_1808_);
v_bs_1810_ = l_Lean_Syntax_getArgs(v___x_1809_);
lean_dec(v___x_1809_);
v___x_1811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1811_, 0, v_stx_1782_);
lean_ctor_set(v___x_1811_, 1, v_m_1787_);
lean_ctor_set(v___x_1811_, 2, v_bs_1810_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1811_);
v___x_1813_ = v___x_1798_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescItemView_of(lean_object* v_stx_1823_){
_start:
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Lean_Doc_DescItemView_of___closed__1));
lean_inc(v_stx_1823_);
v___x_1825_ = l_Lean_Syntax_isOfKind(v_stx_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; 
lean_dec(v_stx_1823_);
v___x_1826_ = lean_box(0);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; lean_object* v_marker_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_desc_1833_; lean_object* v_term_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1827_ = lean_unsigned_to_nat(0u);
v_marker_1828_ = l_Lean_Syntax_getArg(v_stx_1823_, v___x_1827_);
v___x_1829_ = lean_unsigned_to_nat(1u);
v___x_1830_ = l_Lean_Syntax_getArg(v_stx_1823_, v___x_1829_);
v___x_1831_ = lean_unsigned_to_nat(2u);
v___x_1832_ = l_Lean_Syntax_getArg(v_stx_1823_, v___x_1831_);
v_desc_1833_ = l_Lean_Syntax_getArgs(v___x_1832_);
lean_dec(v___x_1832_);
v_term_1834_ = l_Lean_Syntax_getArgs(v___x_1830_);
lean_dec(v___x_1830_);
v___x_1835_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1835_, 0, v_stx_1823_);
lean_ctor_set(v___x_1835_, 1, v_marker_1828_);
lean_ctor_set(v___x_1835_, 2, v_term_1834_);
lean_ctor_set(v___x_1835_, 3, v_desc_1833_);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ParaView_of(lean_object* v_stx_1852_){
_start:
{
lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_Lean_Doc_ParaView_of___closed__2));
lean_inc(v_stx_1852_);
v___x_1854_ = l_Lean_Syntax_isOfKind(v_stx_1852_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; 
lean_dec(v_stx_1852_);
v___x_1855_ = lean_box(0);
return v___x_1855_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_inl_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = l_Lean_Syntax_getArg(v_stx_1852_, v___x_1856_);
v_inl_1858_ = l_Lean_Syntax_getArgs(v___x_1857_);
lean_dec(v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v_stx_1852_);
lean_ctor_set(v___x_1859_, 1, v_inl_1858_);
v___x_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(size_t v_sz_1861_, size_t v_i_1862_, lean_object* v_bs_1863_){
_start:
{
uint8_t v___x_1864_; 
v___x_1864_ = lean_usize_dec_lt(v_i_1862_, v_sz_1861_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1865_, 0, v_bs_1863_);
return v___x_1865_;
}
else
{
lean_object* v_v_1866_; lean_object* v___x_1867_; 
v_v_1866_ = lean_array_uget_borrowed(v_bs_1863_, v_i_1862_);
lean_inc(v_v_1866_);
v___x_1867_ = l_Lean_Doc_UnorderedListItemView_of(v_v_1866_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v_bs_1863_);
v___x_1868_ = lean_box(0);
return v___x_1868_;
}
else
{
lean_object* v_val_1869_; lean_object* v___x_1870_; lean_object* v_bs_x27_1871_; size_t v___x_1872_; size_t v___x_1873_; lean_object* v___x_1874_; 
v_val_1869_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1870_ = lean_unsigned_to_nat(0u);
v_bs_x27_1871_ = lean_array_uset(v_bs_1863_, v_i_1862_, v___x_1870_);
v___x_1872_ = ((size_t)1ULL);
v___x_1873_ = lean_usize_add(v_i_1862_, v___x_1872_);
v___x_1874_ = lean_array_uset(v_bs_x27_1871_, v_i_1862_, v_val_1869_);
v_i_1862_ = v___x_1873_;
v_bs_1863_ = v___x_1874_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1861_ = stack[0].m_num;
size_t v_i_1862_ = stack[1].m_num;
lean_object* v_bs_1863_ = stack[2].m_obj;
lean_object* v_res_1876_;
v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_1861_, v_i_1862_, v_bs_1863_);
stack->m_obj
 = v_res_1876_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0___boxed(lean_object* v_sz_1877_, lean_object* v_i_1878_, lean_object* v_bs_1879_){
_start:
{
size_t v_sz_boxed_1880_; size_t v_i_boxed_1881_; lean_object* v_res_1882_; 
v_sz_boxed_1880_ = lean_unbox_usize(v_sz_1877_);
lean_dec(v_sz_1877_);
v_i_boxed_1881_ = lean_unbox_usize(v_i_1878_);
lean_dec(v_i_1878_);
v_res_1882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_boxed_1880_, v_i_boxed_1881_, v_bs_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListView_of(lean_object* v_stx_1890_){
_start:
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = ((lean_object*)(l_Lean_Doc_UnorderedListView_of___closed__1));
lean_inc(v_stx_1890_);
v___x_1892_ = l_Lean_Syntax_isOfKind(v_stx_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; 
lean_dec(v_stx_1890_);
v___x_1893_ = lean_box(0);
return v___x_1893_;
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_items_1896_; size_t v_sz_1897_; size_t v___x_1898_; lean_object* v___x_1899_; 
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = l_Lean_Syntax_getArg(v_stx_1890_, v___x_1894_);
v_items_1896_ = l_Lean_Syntax_getArgs(v___x_1895_);
lean_dec(v___x_1895_);
v_sz_1897_ = lean_array_size(v_items_1896_);
v___x_1898_ = ((size_t)0ULL);
v___x_1899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_1897_, v___x_1898_, v_items_1896_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v___x_1900_; 
lean_dec(v_stx_1890_);
v___x_1900_ = lean_box(0);
return v___x_1900_;
}
else
{
lean_object* v_val_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1909_; 
v_val_1901_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1903_ = v___x_1899_;
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_val_1901_);
lean_dec(v___x_1899_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_stx_1890_);
lean_ctor_set(v___x_1905_, 1, v_val_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(size_t v_sz_1910_, size_t v_i_1911_, lean_object* v_bs_1912_){
_start:
{
uint8_t v___x_1913_; 
v___x_1913_ = lean_usize_dec_lt(v_i_1911_, v_sz_1910_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_bs_1912_);
return v___x_1914_;
}
else
{
lean_object* v_v_1915_; lean_object* v___x_1916_; 
v_v_1915_ = lean_array_uget_borrowed(v_bs_1912_, v_i_1911_);
lean_inc(v_v_1915_);
v___x_1916_ = l_Lean_Doc_OrderedListItemView_of(v_v_1915_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1917_; 
lean_dec_ref(v_bs_1912_);
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
else
{
lean_object* v_val_1918_; lean_object* v___x_1919_; lean_object* v_bs_x27_1920_; size_t v___x_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v_val_1918_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_val_1918_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1919_ = lean_unsigned_to_nat(0u);
v_bs_x27_1920_ = lean_array_uset(v_bs_1912_, v_i_1911_, v___x_1919_);
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1911_, v___x_1921_);
v___x_1923_ = lean_array_uset(v_bs_x27_1920_, v_i_1911_, v_val_1918_);
v_i_1911_ = v___x_1922_;
v_bs_1912_ = v___x_1923_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1910_ = stack[0].m_num;
size_t v_i_1911_ = stack[1].m_num;
lean_object* v_bs_1912_ = stack[2].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_1910_, v_i_1911_, v_bs_1912_);
stack->m_obj
 = v_res_1925_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0___boxed(lean_object* v_sz_1926_, lean_object* v_i_1927_, lean_object* v_bs_1928_){
_start:
{
size_t v_sz_boxed_1929_; size_t v_i_boxed_1930_; lean_object* v_res_1931_; 
v_sz_boxed_1929_ = lean_unbox_usize(v_sz_1926_);
lean_dec(v_sz_1926_);
v_i_boxed_1930_ = lean_unbox_usize(v_i_1927_);
lean_dec(v_i_1927_);
v_res_1931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_boxed_1929_, v_i_boxed_1930_, v_bs_1928_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListView_of(lean_object* v_stx_1939_){
_start:
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = ((lean_object*)(l_Lean_Doc_OrderedListView_of___closed__1));
lean_inc(v_stx_1939_);
v___x_1941_ = l_Lean_Syntax_isOfKind(v_stx_1939_, v___x_1940_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
lean_dec(v_stx_1939_);
v___x_1942_ = lean_box(0);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v_items_1945_; size_t v_sz_1946_; size_t v___x_1947_; lean_object* v___x_1948_; 
v___x_1943_ = lean_unsigned_to_nat(0u);
v___x_1944_ = l_Lean_Syntax_getArg(v_stx_1939_, v___x_1943_);
v_items_1945_ = l_Lean_Syntax_getArgs(v___x_1944_);
lean_dec(v___x_1944_);
v_sz_1946_ = lean_array_size(v_items_1945_);
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_1946_, v___x_1947_, v_items_1945_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v___x_1949_; 
lean_dec(v_stx_1939_);
v___x_1949_ = lean_box(0);
return v___x_1949_;
}
else
{
lean_object* v_val_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1967_; 
v_val_1950_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1952_ = v___x_1948_;
v_isShared_1953_ = v_isSharedCheck_1967_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_val_1950_);
lean_dec(v___x_1948_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1967_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___y_1955_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = lean_array_get_size(v_val_1950_);
v___x_1963_ = lean_nat_dec_lt(v___x_1943_, v___x_1962_);
if (v___x_1963_ == 0)
{
goto v___jp_1960_;
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = lean_array_fget_borrowed(v_val_1950_, v___x_1943_);
lean_inc(v___x_1964_);
v___x_1965_ = l_Lean_Doc_OrderedListItemView_number(v___x_1964_);
if (lean_obj_tag(v___x_1965_) == 0)
{
goto v___jp_1960_;
}
else
{
lean_object* v_val_1966_; 
v_val_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_val_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v___y_1955_ = v_val_1966_;
goto v___jp_1954_;
}
}
v___jp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1956_, 0, v_stx_1939_);
lean_ctor_set(v___x_1956_, 1, v___y_1955_);
lean_ctor_set(v___x_1956_, 2, v_val_1950_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1956_);
v___x_1958_ = v___x_1952_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
v___jp_1960_:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_unsigned_to_nat(1u);
v___y_1955_ = v___x_1961_;
goto v___jp_1954_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(size_t v_sz_1968_, size_t v_i_1969_, lean_object* v_bs_1970_){
_start:
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_usize_dec_lt(v_i_1969_, v_sz_1968_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_bs_1970_);
return v___x_1972_;
}
else
{
lean_object* v_v_1973_; lean_object* v___x_1974_; 
v_v_1973_ = lean_array_uget_borrowed(v_bs_1970_, v_i_1969_);
lean_inc(v_v_1973_);
v___x_1974_ = l_Lean_Doc_DescItemView_of(v_v_1973_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1975_; 
lean_dec_ref(v_bs_1970_);
v___x_1975_ = lean_box(0);
return v___x_1975_;
}
else
{
lean_object* v_val_1976_; lean_object* v___x_1977_; lean_object* v_bs_x27_1978_; size_t v___x_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
v_val_1976_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_val_1976_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1977_ = lean_unsigned_to_nat(0u);
v_bs_x27_1978_ = lean_array_uset(v_bs_1970_, v_i_1969_, v___x_1977_);
v___x_1979_ = ((size_t)1ULL);
v___x_1980_ = lean_usize_add(v_i_1969_, v___x_1979_);
v___x_1981_ = lean_array_uset(v_bs_x27_1978_, v_i_1969_, v_val_1976_);
v_i_1969_ = v___x_1980_;
v_bs_1970_ = v___x_1981_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1968_ = stack[0].m_num;
size_t v_i_1969_ = stack[1].m_num;
lean_object* v_bs_1970_ = stack[2].m_obj;
lean_object* v_res_1983_;
v_res_1983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_1968_, v_i_1969_, v_bs_1970_);
stack->m_obj
 = v_res_1983_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0___boxed(lean_object* v_sz_1984_, lean_object* v_i_1985_, lean_object* v_bs_1986_){
_start:
{
size_t v_sz_boxed_1987_; size_t v_i_boxed_1988_; lean_object* v_res_1989_; 
v_sz_boxed_1987_ = lean_unbox_usize(v_sz_1984_);
lean_dec(v_sz_1984_);
v_i_boxed_1988_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_res_1989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_boxed_1987_, v_i_boxed_1988_, v_bs_1986_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescListView_of(lean_object* v_stx_1997_){
_start:
{
lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = ((lean_object*)(l_Lean_Doc_DescListView_of___closed__1));
lean_inc(v_stx_1997_);
v___x_1999_ = l_Lean_Syntax_isOfKind(v_stx_1997_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
lean_dec(v_stx_1997_);
v___x_2000_ = lean_box(0);
return v___x_2000_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v_items_2003_; size_t v_sz_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
v___x_2001_ = lean_unsigned_to_nat(0u);
v___x_2002_ = l_Lean_Syntax_getArg(v_stx_1997_, v___x_2001_);
v_items_2003_ = l_Lean_Syntax_getArgs(v___x_2002_);
lean_dec(v___x_2002_);
v_sz_2004_ = lean_array_size(v_items_2003_);
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_2004_, v___x_2005_, v_items_2003_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v___x_2007_; 
lean_dec(v_stx_1997_);
v___x_2007_ = lean_box(0);
return v___x_2007_;
}
else
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
v_val_2008_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2010_ = v___x_2006_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v___x_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_stx_1997_);
lean_ctor_set(v___x_2012_, 1, v_val_2008_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2012_);
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockquoteView_of(lean_object* v_stx_2024_){
_start:
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = ((lean_object*)(l_Lean_Doc_BlockquoteView_of___closed__1));
lean_inc(v_stx_2024_);
v___x_2026_ = l_Lean_Syntax_isOfKind(v_stx_2024_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
lean_dec(v_stx_2024_);
v___x_2027_ = lean_box(0);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v_gt_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v_bs_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2028_ = lean_unsigned_to_nat(0u);
v_gt_2029_ = l_Lean_Syntax_getArg(v_stx_2024_, v___x_2028_);
v___x_2030_ = lean_unsigned_to_nat(1u);
v___x_2031_ = l_Lean_Syntax_getArg(v_stx_2024_, v___x_2030_);
v_bs_2032_ = l_Lean_Syntax_getArgs(v___x_2031_);
lean_dec(v___x_2031_);
v___x_2033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2033_, 0, v_stx_2024_);
lean_ctor_set(v___x_2033_, 1, v_gt_2029_);
lean_ctor_set(v___x_2033_, 2, v_bs_2032_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object* v_v_2035_){
_start:
{
lean_object* v_content_2036_; lean_object* v___x_2037_; 
v_content_2036_ = lean_ctor_get(v_v_2035_, 4);
v___x_2037_ = l_Lean_TSyntax_getVersoCodeBlock(v_content_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock___boxed(lean_object* v_v_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_v_2038_);
lean_dec_ref(v_v_2038_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_of(lean_object* v_stx_2059_){
_start:
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__1));
lean_inc(v_stx_2059_);
v___x_2061_ = l_Lean_Syntax_isOfKind(v_stx_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
lean_dec(v_stx_2059_);
v___x_2062_ = lean_box(0);
return v___x_2062_;
}
else
{
lean_object* v___x_2063_; lean_object* v_openFence_2064_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v_name_2087_; lean_object* v_args_2088_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2063_ = lean_unsigned_to_nat(0u);
v_openFence_2064_ = l_Lean_Syntax_getArg(v_stx_2059_, v___x_2063_);
v___x_2101_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__5));
lean_inc(v_openFence_2064_);
v___x_2102_ = l_Lean_Syntax_isOfKind(v_openFence_2064_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; 
lean_dec(v_openFence_2064_);
lean_dec(v_stx_2059_);
v___x_2103_ = lean_box(0);
return v___x_2103_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = l_Lean_Syntax_getArg(v_stx_2059_, v___x_2104_);
v___x_2106_ = l_Lean_Syntax_isNone(v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2105_);
v___x_2108_ = l_Lean_Syntax_matchesNull(v___x_2105_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_dec(v___x_2105_);
lean_dec(v_openFence_2064_);
lean_dec(v_stx_2059_);
v___x_2109_ = lean_box(0);
return v___x_2109_;
}
else
{
lean_object* v_name_2110_; 
v_name_2110_ = l_Lean_Syntax_getArg(v___x_2105_, v___x_2063_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2110_);
v___x_2117_ = l_Lean_Syntax_isOfKind(v_name_2110_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_dec(v_name_2110_);
lean_dec(v___x_2105_);
lean_dec(v_openFence_2064_);
lean_dec(v_stx_2059_);
v___x_2118_ = lean_box(0);
return v___x_2118_;
}
else
{
goto v___jp_2111_;
}
}
else
{
goto v___jp_2111_;
}
v___jp_2111_:
{
lean_object* v___x_2112_; lean_object* v_args_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2112_ = l_Lean_Syntax_getArg(v___x_2105_, v___x_2104_);
lean_dec(v___x_2105_);
v_args_2113_ = l_Lean_Syntax_getArgs(v___x_2112_);
lean_dec(v___x_2112_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_name_2110_);
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v_args_2113_);
v_name_2087_ = v___x_2114_;
v_args_2088_ = v___x_2115_;
goto v___jp_2086_;
}
}
}
else
{
lean_object* v___x_2119_; 
lean_dec(v___x_2105_);
v___x_2119_ = lean_box(0);
v_name_2087_ = v___x_2119_;
v_args_2088_ = v___x_2119_;
goto v___jp_2086_;
}
}
v___jp_2065_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2070_, 0, v_stx_2059_);
lean_ctor_set(v___x_2070_, 1, v_openFence_2064_);
lean_ctor_set(v___x_2070_, 2, v___y_2068_);
lean_ctor_set(v___x_2070_, 3, v___y_2069_);
lean_ctor_set(v___x_2070_, 4, v___y_2066_);
lean_ctor_set(v___x_2070_, 5, v___y_2067_);
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
v___jp_2072_:
{
if (lean_obj_tag(v___y_2073_) == 0)
{
lean_object* v___x_2077_; 
v___x_2077_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0));
v___y_2066_ = v___y_2076_;
v___y_2067_ = v___y_2075_;
v___y_2068_ = v___y_2074_;
v___y_2069_ = v___x_2077_;
goto v___jp_2065_;
}
else
{
lean_object* v_val_2078_; 
v_val_2078_ = lean_ctor_get(v___y_2073_, 0);
lean_inc(v_val_2078_);
lean_dec_ref_known(v___y_2073_, 1);
v___y_2066_ = v___y_2076_;
v___y_2067_ = v___y_2075_;
v___y_2068_ = v___y_2074_;
v___y_2069_ = v_val_2078_;
goto v___jp_2065_;
}
}
v___jp_2079_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v___y_2083_);
v___x_2085_ = l_Lean_Syntax_setInfo(v___x_2084_, v___y_2081_);
v___y_2073_ = v___y_2080_;
v___y_2074_ = v___y_2082_;
v___y_2075_ = v___y_2083_;
v___y_2076_ = v___x_2085_;
goto v___jp_2072_;
}
v___jp_2086_:
{
lean_object* v___x_2089_; lean_object* v_s_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2089_ = lean_unsigned_to_nat(2u);
v_s_2090_ = l_Lean_Syntax_getArg(v_stx_2059_, v___x_2089_);
v___x_2091_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__3));
lean_inc(v_s_2090_);
v___x_2092_ = l_Lean_Syntax_isOfKind(v_s_2090_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec(v_s_2090_);
lean_dec(v_args_2088_);
lean_dec(v_name_2087_);
lean_dec(v_openFence_2064_);
lean_dec(v_stx_2059_);
v___x_2093_ = lean_box(0);
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; lean_object* v_closeFence_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2094_ = lean_unsigned_to_nat(3u);
v_closeFence_2095_ = l_Lean_Syntax_getArg(v_stx_2059_, v___x_2094_);
v___x_2096_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__5));
lean_inc(v_closeFence_2095_);
v___x_2097_ = l_Lean_Syntax_isOfKind(v_closeFence_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
lean_dec(v_closeFence_2095_);
lean_dec(v_s_2090_);
lean_dec(v_args_2088_);
lean_dec(v_name_2087_);
lean_dec(v_openFence_2064_);
lean_dec(v_stx_2059_);
v___x_2098_ = lean_box(0);
return v___x_2098_;
}
else
{
uint8_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = 0;
v___x_2100_ = l_Lean_Syntax_getPos_x3f(v_s_2090_, v___x_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
v___y_2080_ = v_args_2088_;
v___y_2081_ = v_s_2090_;
v___y_2082_ = v_name_2087_;
v___y_2083_ = v_closeFence_2095_;
goto v___jp_2079_;
}
else
{
lean_dec_ref_known(v___x_2100_, 1);
if (v___x_2061_ == 0)
{
v___y_2080_ = v_args_2088_;
v___y_2081_ = v_s_2090_;
v___y_2082_ = v_name_2087_;
v___y_2083_ = v_closeFence_2095_;
goto v___jp_2079_;
}
else
{
v___y_2073_ = v_args_2088_;
v___y_2074_ = v_name_2087_;
v___y_2075_ = v_closeFence_2095_;
v___y_2076_ = v_s_2090_;
goto v___jp_2072_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DirectiveView_of(lean_object* v_stx_2133_){
_start:
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_Lean_Doc_DirectiveView_of___closed__1));
lean_inc(v_stx_2133_);
v___x_2135_ = l_Lean_Syntax_isOfKind(v_stx_2133_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec(v_stx_2133_);
v___x_2136_ = lean_box(0);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; lean_object* v_opener_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2137_ = lean_unsigned_to_nat(0u);
v_opener_2138_ = l_Lean_Syntax_getArg(v_stx_2133_, v___x_2137_);
v___x_2139_ = ((lean_object*)(l_Lean_Doc_DirectiveView_of___closed__3));
lean_inc(v_opener_2138_);
v___x_2140_ = l_Lean_Syntax_isOfKind(v_opener_2138_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_dec(v_opener_2138_);
lean_dec(v_stx_2133_);
v___x_2141_ = lean_box(0);
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; lean_object* v_name_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2142_ = lean_unsigned_to_nat(1u);
v_name_2143_ = l_Lean_Syntax_getArg(v_stx_2133_, v___x_2142_);
v___x_2144_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2143_);
v___x_2145_ = l_Lean_Syntax_isOfKind(v_name_2143_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; 
lean_dec(v_name_2143_);
lean_dec(v_opener_2138_);
lean_dec(v_stx_2133_);
v___x_2146_ = lean_box(0);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v_closer_2148_; uint8_t v___x_2149_; 
v___x_2147_ = lean_unsigned_to_nat(4u);
v_closer_2148_ = l_Lean_Syntax_getArg(v_stx_2133_, v___x_2147_);
lean_inc(v_closer_2148_);
v___x_2149_ = l_Lean_Syntax_isOfKind(v_closer_2148_, v___x_2139_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
lean_dec(v_closer_2148_);
lean_dec(v_name_2143_);
lean_dec(v_opener_2138_);
lean_dec(v_stx_2133_);
v___x_2150_ = lean_box(0);
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v_bs_2155_; lean_object* v_args_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2151_ = lean_unsigned_to_nat(2u);
v___x_2152_ = l_Lean_Syntax_getArg(v_stx_2133_, v___x_2151_);
v___x_2153_ = lean_unsigned_to_nat(3u);
v___x_2154_ = l_Lean_Syntax_getArg(v_stx_2133_, v___x_2153_);
v_bs_2155_ = l_Lean_Syntax_getArgs(v___x_2154_);
lean_dec(v___x_2154_);
v_args_2156_ = l_Lean_Syntax_getArgs(v___x_2152_);
lean_dec(v___x_2152_);
v___x_2157_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2157_, 0, v_stx_2133_);
lean_ctor_set(v___x_2157_, 1, v_opener_2138_);
lean_ctor_set(v___x_2157_, 2, v_name_2143_);
lean_ctor_set(v___x_2157_, 3, v_args_2156_);
lean_ctor_set(v___x_2157_, 4, v_bs_2155_);
lean_ctor_set(v___x_2157_, 5, v_closer_2148_);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CommandView_of(lean_object* v_stx_2166_){
_start:
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = ((lean_object*)(l_Lean_Doc_CommandView_of___closed__1));
lean_inc(v_stx_2166_);
v___x_2168_ = l_Lean_Syntax_isOfKind(v_stx_2166_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; 
lean_dec(v_stx_2166_);
v___x_2169_ = lean_box(0);
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; lean_object* v_name_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2170_ = lean_unsigned_to_nat(1u);
v_name_2171_ = l_Lean_Syntax_getArg(v_stx_2166_, v___x_2170_);
v___x_2172_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2171_);
v___x_2173_ = l_Lean_Syntax_isOfKind(v_name_2171_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_dec(v_name_2171_);
lean_dec(v_stx_2166_);
v___x_2174_ = lean_box(0);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; lean_object* v_braceOpen_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v_braceClose_2180_; lean_object* v_args_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v_braceOpen_2176_ = l_Lean_Syntax_getArg(v_stx_2166_, v___x_2175_);
v___x_2177_ = lean_unsigned_to_nat(2u);
v___x_2178_ = l_Lean_Syntax_getArg(v_stx_2166_, v___x_2177_);
v___x_2179_ = lean_unsigned_to_nat(3u);
v_braceClose_2180_ = l_Lean_Syntax_getArg(v_stx_2166_, v___x_2179_);
v_args_2181_ = l_Lean_Syntax_getArgs(v___x_2178_);
lean_dec(v___x_2178_);
v___x_2182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2182_, 0, v_stx_2166_);
lean_ctor_set(v___x_2182_, 1, v_braceOpen_2176_);
lean_ctor_set(v___x_2182_, 2, v_name_2171_);
lean_ctor_set(v___x_2182_, 3, v_args_2181_);
lean_ctor_set(v___x_2182_, 4, v_braceClose_2180_);
v___x_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
return v___x_2183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_HeaderView_of(lean_object* v_stx_2197_){
_start:
{
lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = ((lean_object*)(l_Lean_Doc_HeaderView_of___closed__1));
lean_inc(v_stx_2197_);
v___x_2199_ = l_Lean_Syntax_isOfKind(v_stx_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; 
lean_dec(v_stx_2197_);
v___x_2200_ = lean_box(0);
return v___x_2200_;
}
else
{
lean_object* v___x_2201_; lean_object* v_marker_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2201_ = lean_unsigned_to_nat(0u);
v_marker_2202_ = l_Lean_Syntax_getArg(v_stx_2197_, v___x_2201_);
v___x_2203_ = ((lean_object*)(l_Lean_Doc_HeaderView_of___closed__3));
lean_inc(v_marker_2202_);
v___x_2204_ = l_Lean_Syntax_isOfKind(v_marker_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; 
lean_dec(v_marker_2202_);
lean_dec(v_stx_2197_);
v___x_2205_ = lean_box(0);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_content_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2206_ = lean_unsigned_to_nat(1u);
v___x_2207_ = l_Lean_Syntax_getArg(v_stx_2197_, v___x_2206_);
v_content_2208_ = l_Lean_Syntax_getArgs(v___x_2207_);
lean_dec(v___x_2207_);
v___x_2209_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_2202_);
v___x_2210_ = lean_string_length(v___x_2209_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = lean_nat_sub(v___x_2210_, v___x_2206_);
v___x_2212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2212_, 0, v_stx_2197_);
lean_ctor_set(v___x_2212_, 1, v_marker_2202_);
lean_ctor_set(v___x_2212_, 2, v___x_2211_);
lean_ctor_set(v___x_2212_, 3, v_content_2208_);
v___x_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName(lean_object* v_v_2214_){
_start:
{
lean_object* v_name_2215_; lean_object* v___x_2216_; 
v_name_2215_ = lean_ctor_get(v_v_2214_, 2);
v___x_2216_ = l_Lean_TSyntax_getVersoRefName(v_name_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName___boxed(lean_object* v_v_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_Doc_LinkRefView_getName(v_v_2217_);
lean_dec_ref(v_v_2217_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object* v_v_2219_){
_start:
{
lean_object* v_url_2220_; lean_object* v___x_2221_; 
v_url_2220_ = lean_ctor_get(v_v_2219_, 4);
v___x_2221_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_url_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl___boxed(lean_object* v_v_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_Doc_LinkRefView_getUrl(v_v_2222_);
lean_dec_ref(v_v_2222_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_of(lean_object* v_stx_2237_){
_start:
{
lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2238_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__1));
lean_inc(v_stx_2237_);
v___x_2239_ = l_Lean_Syntax_isOfKind(v_stx_2237_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; 
lean_dec(v_stx_2237_);
v___x_2240_ = lean_box(0);
return v___x_2240_;
}
else
{
lean_object* v___x_2241_; lean_object* v_name_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2241_ = lean_unsigned_to_nat(1u);
v_name_2242_ = l_Lean_Syntax_getArg(v_stx_2237_, v___x_2241_);
v___x_2243_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_2242_);
v___x_2244_ = l_Lean_Syntax_isOfKind(v_name_2242_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; 
lean_dec(v_name_2242_);
lean_dec(v_stx_2237_);
v___x_2245_ = lean_box(0);
return v___x_2245_;
}
else
{
lean_object* v___x_2246_; lean_object* v_url_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2246_ = lean_unsigned_to_nat(3u);
v_url_2247_ = l_Lean_Syntax_getArg(v_stx_2237_, v___x_2246_);
v___x_2248_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__3));
lean_inc(v_url_2247_);
v___x_2249_ = l_Lean_Syntax_isOfKind(v_url_2247_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; 
lean_dec(v_url_2247_);
lean_dec(v_name_2242_);
lean_dec(v_stx_2237_);
v___x_2250_ = lean_box(0);
return v___x_2250_;
}
else
{
lean_object* v___x_2251_; lean_object* v_opener_2252_; lean_object* v___x_2253_; lean_object* v_closer_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2251_ = lean_unsigned_to_nat(0u);
v_opener_2252_ = l_Lean_Syntax_getArg(v_stx_2237_, v___x_2251_);
v___x_2253_ = lean_unsigned_to_nat(2u);
v_closer_2254_ = l_Lean_Syntax_getArg(v_stx_2237_, v___x_2253_);
v___x_2255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2255_, 0, v_stx_2237_);
lean_ctor_set(v___x_2255_, 1, v_opener_2252_);
lean_ctor_set(v___x_2255_, 2, v_name_2242_);
lean_ctor_set(v___x_2255_, 3, v_closer_2254_);
lean_ctor_set(v___x_2255_, 4, v_url_2247_);
v___x_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object* v_v_2257_){
_start:
{
lean_object* v_name_2258_; lean_object* v___x_2259_; 
v_name_2258_ = lean_ctor_get(v_v_2257_, 2);
v___x_2259_ = l_Lean_TSyntax_getVersoRefName(v_name_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName___boxed(lean_object* v_v_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Doc_FootnoteRefView_getName(v_v_2260_);
lean_dec_ref(v_v_2260_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_of(lean_object* v_stx_2269_){
_start:
{
lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = ((lean_object*)(l_Lean_Doc_FootnoteRefView_of___closed__1));
lean_inc(v_stx_2269_);
v___x_2271_ = l_Lean_Syntax_isOfKind(v_stx_2269_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; 
lean_dec(v_stx_2269_);
v___x_2272_ = lean_box(0);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; lean_object* v_name_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2273_ = lean_unsigned_to_nat(1u);
v_name_2274_ = l_Lean_Syntax_getArg(v_stx_2269_, v___x_2273_);
v___x_2275_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_2274_);
v___x_2276_ = l_Lean_Syntax_isOfKind(v_name_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
lean_dec(v_name_2274_);
lean_dec(v_stx_2269_);
v___x_2277_ = lean_box(0);
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; lean_object* v_opener_2279_; lean_object* v___x_2280_; lean_object* v_closer_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_content_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2278_ = lean_unsigned_to_nat(0u);
v_opener_2279_ = l_Lean_Syntax_getArg(v_stx_2269_, v___x_2278_);
v___x_2280_ = lean_unsigned_to_nat(2u);
v_closer_2281_ = l_Lean_Syntax_getArg(v_stx_2269_, v___x_2280_);
v___x_2282_ = lean_unsigned_to_nat(3u);
v___x_2283_ = l_Lean_Syntax_getArg(v_stx_2269_, v___x_2282_);
v_content_2284_ = l_Lean_Syntax_getArgs(v___x_2283_);
lean_dec(v___x_2283_);
v___x_2285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2285_, 0, v_stx_2269_);
lean_ctor_set(v___x_2285_, 1, v_opener_2279_);
lean_ctor_set(v___x_2285_, 2, v_name_2274_);
lean_ctor_set(v___x_2285_, 3, v_closer_2281_);
lean_ctor_set(v___x_2285_, 4, v_content_2284_);
v___x_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(size_t v_sz_2287_, size_t v_i_2288_, lean_object* v_bs_2289_){
_start:
{
uint8_t v___x_2290_; 
v___x_2290_ = lean_usize_dec_lt(v_i_2288_, v_sz_2287_);
if (v___x_2290_ == 0)
{
return v_bs_2289_;
}
else
{
lean_object* v_v_2291_; lean_object* v___x_2292_; lean_object* v_bs_x27_2293_; size_t v___x_2294_; size_t v___x_2295_; lean_object* v___x_2296_; 
v_v_2291_ = lean_array_uget(v_bs_2289_, v_i_2288_);
v___x_2292_ = lean_unsigned_to_nat(0u);
v_bs_x27_2293_ = lean_array_uset(v_bs_2289_, v_i_2288_, v___x_2292_);
v___x_2294_ = ((size_t)1ULL);
v___x_2295_ = lean_usize_add(v_i_2288_, v___x_2294_);
v___x_2296_ = lean_array_uset(v_bs_x27_2293_, v_i_2288_, v_v_2291_);
v_i_2288_ = v___x_2295_;
v_bs_2289_ = v___x_2296_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2287_ = stack[0].m_num;
size_t v_i_2288_ = stack[1].m_num;
lean_object* v_bs_2289_ = stack[2].m_obj;
lean_object* v_res_2298_;
v_res_2298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_2287_, v_i_2288_, v_bs_2289_);
stack->m_obj
 = v_res_2298_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0___boxed(lean_object* v_sz_2299_, lean_object* v_i_2300_, lean_object* v_bs_2301_){
_start:
{
size_t v_sz_boxed_2302_; size_t v_i_boxed_2303_; lean_object* v_res_2304_; 
v_sz_boxed_2302_ = lean_unbox_usize(v_sz_2299_);
lean_dec(v_sz_2299_);
v_i_boxed_2303_ = lean_unbox_usize(v_i_2300_);
lean_dec(v_i_2300_);
v_res_2304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_boxed_2302_, v_i_boxed_2303_, v_bs_2301_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields(lean_object* v_v_2305_){
_start:
{
lean_object* v_contents_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; size_t v_sz_2310_; size_t v___x_2311_; lean_object* v___x_2312_; 
v_contents_2306_ = lean_ctor_get(v_v_2305_, 2);
v___x_2307_ = lean_unsigned_to_nat(0u);
v___x_2308_ = l_Lean_Syntax_getArg(v_contents_2306_, v___x_2307_);
v___x_2309_ = l_Lean_Syntax_getSepArgs(v___x_2308_);
lean_dec(v___x_2308_);
v_sz_2310_ = lean_array_size(v___x_2309_);
v___x_2311_ = ((size_t)0ULL);
v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_2310_, v___x_2311_, v___x_2309_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields___boxed(lean_object* v_v_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_Doc_MetadataView_fields(v_v_2313_);
lean_dec_ref(v_v_2313_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_of(lean_object* v_stx_2329_){
_start:
{
lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_Doc_MetadataView_of___closed__1));
lean_inc(v_stx_2329_);
v___x_2331_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_dec(v_stx_2329_);
v___x_2332_ = lean_box(0);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; lean_object* v_contents_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2333_ = lean_unsigned_to_nat(1u);
v_contents_2334_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2333_);
v___x_2335_ = ((lean_object*)(l_Lean_Doc_MetadataView_of___closed__4));
lean_inc(v_contents_2334_);
v___x_2336_ = l_Lean_Syntax_isOfKind(v_contents_2334_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; 
lean_dec(v_contents_2334_);
lean_dec(v_stx_2329_);
v___x_2337_ = lean_box(0);
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; lean_object* v_opener_2339_; lean_object* v___x_2340_; lean_object* v_closer_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2338_ = lean_unsigned_to_nat(0u);
v_opener_2339_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2338_);
v___x_2340_ = lean_unsigned_to_nat(2u);
v_closer_2341_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2340_);
v___x_2342_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2342_, 0, v_stx_2329_);
lean_ctor_set(v___x_2342_, 1, v_opener_2339_);
lean_ctor_set(v___x_2342_, 2, v_contents_2334_);
lean_ctor_set(v___x_2342_, 3, v_closer_2341_);
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___impl(lean_object* v_x_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_obj_tag_nat(v_x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___impl___boxed(lean_object* v_x_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Doc_BlockView_ctorIdx___impl(v_x_2346_);
lean_dec_ref(v_x_2346_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___redArg(lean_object* v_t_2348_, lean_object* v_k_2349_){
_start:
{
lean_object* v_view_2350_; lean_object* v___x_2351_; 
v_view_2350_ = lean_ctor_get(v_t_2348_, 0);
lean_inc_ref(v_view_2350_);
lean_dec_ref(v_t_2348_);
v___x_2351_ = lean_apply_1(v_k_2349_, v_view_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim(lean_object* v_motive_2352_, lean_object* v_ctorIdx_2353_, lean_object* v_t_2354_, lean_object* v_h_2355_, lean_object* v_k_2356_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2354_, v_k_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___boxed(lean_object* v_motive_2358_, lean_object* v_ctorIdx_2359_, lean_object* v_t_2360_, lean_object* v_h_2361_, lean_object* v_k_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_Doc_BlockView_ctorElim(v_motive_2358_, v_ctorIdx_2359_, v_t_2360_, v_h_2361_, v_k_2362_);
lean_dec(v_ctorIdx_2359_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim___redArg(lean_object* v_t_2364_, lean_object* v_para_2365_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2364_, v_para_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim(lean_object* v_motive_2367_, lean_object* v_t_2368_, lean_object* v_h_2369_, lean_object* v_para_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2368_, v_para_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim___redArg(lean_object* v_t_2372_, lean_object* v_ul_2373_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2372_, v_ul_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim(lean_object* v_motive_2375_, lean_object* v_t_2376_, lean_object* v_h_2377_, lean_object* v_ul_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2376_, v_ul_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim___redArg(lean_object* v_t_2380_, lean_object* v_ol_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2380_, v_ol_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim(lean_object* v_motive_2383_, lean_object* v_t_2384_, lean_object* v_h_2385_, lean_object* v_ol_2386_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2384_, v_ol_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim___redArg(lean_object* v_t_2388_, lean_object* v_dl_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2388_, v_dl_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim(lean_object* v_motive_2391_, lean_object* v_t_2392_, lean_object* v_h_2393_, lean_object* v_dl_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2392_, v_dl_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim___redArg(lean_object* v_t_2396_, lean_object* v_blockquote_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2396_, v_blockquote_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim(lean_object* v_motive_2399_, lean_object* v_t_2400_, lean_object* v_h_2401_, lean_object* v_blockquote_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2400_, v_blockquote_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim___redArg(lean_object* v_t_2404_, lean_object* v_codeblock_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2404_, v_codeblock_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim(lean_object* v_motive_2407_, lean_object* v_t_2408_, lean_object* v_h_2409_, lean_object* v_codeblock_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2408_, v_codeblock_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim___redArg(lean_object* v_t_2412_, lean_object* v_directive_2413_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2412_, v_directive_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim(lean_object* v_motive_2415_, lean_object* v_t_2416_, lean_object* v_h_2417_, lean_object* v_directive_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2416_, v_directive_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim___redArg(lean_object* v_t_2420_, lean_object* v_command_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2420_, v_command_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim(lean_object* v_motive_2423_, lean_object* v_t_2424_, lean_object* v_h_2425_, lean_object* v_command_2426_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2424_, v_command_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim___redArg(lean_object* v_t_2428_, lean_object* v_header_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2428_, v_header_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim(lean_object* v_motive_2431_, lean_object* v_t_2432_, lean_object* v_h_2433_, lean_object* v_header_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2432_, v_header_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim___redArg(lean_object* v_t_2436_, lean_object* v_linkRef_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2436_, v_linkRef_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim(lean_object* v_motive_2439_, lean_object* v_t_2440_, lean_object* v_h_2441_, lean_object* v_linkRef_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2440_, v_linkRef_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim___redArg(lean_object* v_t_2444_, lean_object* v_footnoteRef_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2444_, v_footnoteRef_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim(lean_object* v_motive_2447_, lean_object* v_t_2448_, lean_object* v_h_2449_, lean_object* v_footnoteRef_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2448_, v_footnoteRef_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim___redArg(lean_object* v_t_2452_, lean_object* v_metadata_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2452_, v_metadata_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim(lean_object* v_motive_2455_, lean_object* v_t_2456_, lean_object* v_h_2457_, lean_object* v_metadata_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2456_, v_metadata_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeParaViewBlockView___lam__0(lean_object* v_view_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v_view_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0(lean_object* v_view_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_view_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0(lean_object* v_view_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_view_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDescListViewBlockView___lam__0(lean_object* v_view_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2477_, 0, v_view_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0(lean_object* v_view_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_view_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0(lean_object* v_view_2484_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_view_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0(lean_object* v_view_2488_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_view_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCommandViewBlockView___lam__0(lean_object* v_view_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2493_, 0, v_view_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___lam__0(lean_object* v_view_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_view_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0(lean_object* v_view_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_view_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0(lean_object* v_view_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_view_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___lam__0(lean_object* v_view_2508_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_view_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx(lean_object* v_x_2512_){
_start:
{
lean_object* v_view_2513_; lean_object* v_stx_2514_; 
v_view_2513_ = lean_ctor_get(v_x_2512_, 0);
v_stx_2514_ = lean_ctor_get(v_view_2513_, 0);
lean_inc(v_stx_2514_);
return v_stx_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx___boxed(lean_object* v_x_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Doc_BlockView_stx(v_x_2515_);
lean_dec_ref(v_x_2515_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_of(lean_object* v_stx_2517_){
_start:
{
lean_object* v___x_2518_; 
lean_inc(v_stx_2517_);
v___x_2518_ = l_Lean_Doc_ParaView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v___x_2519_; 
lean_inc(v_stx_2517_);
v___x_2519_ = l_Lean_Doc_UnorderedListView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v___x_2520_; 
lean_inc(v_stx_2517_);
v___x_2520_ = l_Lean_Doc_OrderedListView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v___x_2521_; 
lean_inc(v_stx_2517_);
v___x_2521_ = l_Lean_Doc_DescListView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v___x_2522_; 
lean_inc(v_stx_2517_);
v___x_2522_ = l_Lean_Doc_BlockquoteView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v___x_2523_; 
lean_inc(v_stx_2517_);
v___x_2523_ = l_Lean_Doc_CodeBlockView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v___x_2524_; 
lean_inc(v_stx_2517_);
v___x_2524_ = l_Lean_Doc_DirectiveView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v___x_2525_; 
lean_inc(v_stx_2517_);
v___x_2525_ = l_Lean_Doc_CommandView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v___x_2526_; 
lean_inc(v_stx_2517_);
v___x_2526_ = l_Lean_Doc_HeaderView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v___x_2527_; 
lean_inc(v_stx_2517_);
v___x_2527_ = l_Lean_Doc_LinkRefView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v___x_2528_; 
lean_inc(v_stx_2517_);
v___x_2528_ = l_Lean_Doc_FootnoteRefView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Doc_MetadataView_of(v_stx_2517_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_box(0);
return v___x_2530_;
}
else
{
lean_object* v_val_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2539_; 
v_val_2531_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2533_ = v___x_2529_;
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_val_2531_);
lean_dec(v___x_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_val_2531_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2535_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_object* v_val_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_stx_2517_);
v_val_2540_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2542_ = v___x_2528_;
v_isShared_2543_ = v_isSharedCheck_2548_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_val_2540_);
lean_dec(v___x_2528_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2548_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2544_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2544_, 0, v_val_2540_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v___x_2544_);
v___x_2546_ = v___x_2542_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v_val_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2557_; 
lean_dec(v_stx_2517_);
v_val_2549_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2551_ = v___x_2527_;
v_isShared_2552_ = v_isSharedCheck_2557_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_val_2549_);
lean_dec(v___x_2527_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2557_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2553_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_val_2549_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2553_);
v___x_2555_ = v___x_2551_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
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
lean_object* v_val_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_stx_2517_);
v_val_2558_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2560_ = v___x_2526_;
v_isShared_2561_ = v_isSharedCheck_2566_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_val_2558_);
lean_dec(v___x_2526_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2566_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2564_; 
v___x_2562_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_val_2558_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2562_);
v___x_2564_ = v___x_2560_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
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
else
{
lean_object* v_val_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_stx_2517_);
v_val_2567_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2569_ = v___x_2525_;
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_val_2567_);
lean_dec(v___x_2525_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2571_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_val_2567_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2571_);
v___x_2573_ = v___x_2569_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
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
else
{
lean_object* v_val_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v_stx_2517_);
v_val_2576_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2578_ = v___x_2524_;
v_isShared_2579_ = v_isSharedCheck_2584_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_val_2576_);
lean_dec(v___x_2524_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2584_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_val_2576_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___x_2580_);
v___x_2582_ = v___x_2578_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
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
else
{
lean_object* v_val_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_stx_2517_);
v_val_2585_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2587_ = v___x_2523_;
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_val_2585_);
lean_dec(v___x_2523_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2589_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2589_, 0, v_val_2585_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 0, v___x_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v_val_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v_stx_2517_);
v_val_2594_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2596_ = v___x_2522_;
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_val_2594_);
lean_dec(v___x_2522_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2598_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2598_, 0, v_val_2594_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2598_);
v___x_2600_ = v___x_2596_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v_val_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_stx_2517_);
v_val_2603_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2605_ = v___x_2521_;
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_val_2603_);
lean_dec(v___x_2521_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2611_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2607_, 0, v_val_2603_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2607_);
v___x_2609_ = v___x_2605_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v_val_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v_stx_2517_);
v_val_2612_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2614_ = v___x_2520_;
v_isShared_2615_ = v_isSharedCheck_2620_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_val_2612_);
lean_dec(v___x_2520_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2620_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2616_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_val_2612_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2616_);
v___x_2618_ = v___x_2614_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_val_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_stx_2517_);
v_val_2621_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2623_ = v___x_2519_;
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_val_2621_);
lean_dec(v___x_2519_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_val_2621_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2625_);
v___x_2627_ = v___x_2623_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_object* v_val_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2638_; 
lean_dec(v_stx_2517_);
v_val_2630_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2632_ = v___x_2518_;
v_isShared_2633_ = v_isSharedCheck_2638_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_val_2630_);
lean_dec(v___x_2518_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2638_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_val_2630_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v___x_2634_);
v___x_2636_ = v___x_2632_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoInline_view(lean_object* v_stx_2639_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_Doc_InlineView_of(v_stx_2639_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = ((lean_object*)(l_Lean_Doc_instInhabitedInlineView_default));
return v___x_2641_;
}
else
{
lean_object* v_val_2642_; 
v_val_2642_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_val_2642_);
lean_dec_ref_known(v___x_2640_, 1);
return v_val_2642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoBlock_view(lean_object* v_stx_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_Doc_BlockView_of(v_stx_2643_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2645_; 
v___x_2645_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlockView_default));
return v___x_2645_;
}
else
{
lean_object* v_val_2646_; 
v_val_2646_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_val_2646_);
lean_dec_ref_known(v___x_2644_, 1);
return v_val_2646_;
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
