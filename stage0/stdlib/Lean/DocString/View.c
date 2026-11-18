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
lean_object* v___x_90_; lean_object* v_s_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v_s_91_ = l_Lean_Syntax_getArg(v_stx_82_, v___x_90_);
lean_dec(v_stx_82_);
v___x_92_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__10));
lean_inc(v_s_91_);
v___x_93_ = l_Lean_Syntax_isOfKind(v_s_91_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec(v_s_91_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = l_Lean_TSyntax_getString(v_s_91_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_s_91_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
}
else
{
lean_object* v___x_98_; lean_object* v_n_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v_n_99_ = l_Lean_Syntax_getArg(v_stx_82_, v___x_98_);
lean_dec(v_stx_82_);
v___x_100_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__11));
lean_inc(v_n_99_);
v___x_101_ = l_Lean_Syntax_isOfKind(v_n_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
lean_dec(v_n_99_);
v___x_102_ = lean_box(0);
return v___x_102_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = l_Lean_TSyntax_getNat(v_n_99_);
v___x_104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_104_, 0, v_n_99_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
}
else
{
lean_object* v___x_106_; lean_object* v_x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_106_ = lean_unsigned_to_nat(0u);
v_x_107_ = l_Lean_Syntax_getArg(v_stx_82_, v___x_106_);
lean_dec(v_stx_82_);
v___x_108_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_107_);
v___x_109_ = l_Lean_Syntax_isOfKind(v_x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
lean_dec(v_x_107_);
v___x_110_ = lean_box(0);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v_x_107_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx___impl(lean_object* v_x_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_tag_nat(v_x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx___impl___boxed(lean_object* v_x_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Doc_ArgView_ctorIdx___impl(v_x_115_);
lean_dec_ref(v_x_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___redArg(lean_object* v_t_117_, lean_object* v_k_118_){
_start:
{
switch(lean_obj_tag(v_t_117_))
{
case 0:
{
lean_object* v_stx_119_; lean_object* v_val_120_; lean_object* v___x_121_; 
v_stx_119_ = lean_ctor_get(v_t_117_, 0);
lean_inc(v_stx_119_);
v_val_120_ = lean_ctor_get(v_t_117_, 1);
lean_inc(v_val_120_);
lean_dec_ref_known(v_t_117_, 2);
v___x_121_ = lean_apply_2(v_k_118_, v_stx_119_, v_val_120_);
return v___x_121_;
}
case 1:
{
lean_object* v_stx_122_; lean_object* v_parens_123_; lean_object* v_name_124_; lean_object* v_assign_125_; lean_object* v_val_126_; lean_object* v___x_127_; 
v_stx_122_ = lean_ctor_get(v_t_117_, 0);
lean_inc(v_stx_122_);
v_parens_123_ = lean_ctor_get(v_t_117_, 1);
lean_inc(v_parens_123_);
v_name_124_ = lean_ctor_get(v_t_117_, 2);
lean_inc(v_name_124_);
v_assign_125_ = lean_ctor_get(v_t_117_, 3);
lean_inc(v_assign_125_);
v_val_126_ = lean_ctor_get(v_t_117_, 4);
lean_inc(v_val_126_);
lean_dec_ref_known(v_t_117_, 5);
v___x_127_ = lean_apply_5(v_k_118_, v_stx_122_, v_parens_123_, v_name_124_, v_assign_125_, v_val_126_);
return v___x_127_;
}
default: 
{
lean_object* v_stx_128_; lean_object* v_sign_129_; lean_object* v_name_130_; uint8_t v_isOn_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_stx_128_ = lean_ctor_get(v_t_117_, 0);
lean_inc(v_stx_128_);
v_sign_129_ = lean_ctor_get(v_t_117_, 1);
lean_inc(v_sign_129_);
v_name_130_ = lean_ctor_get(v_t_117_, 2);
lean_inc(v_name_130_);
v_isOn_131_ = lean_ctor_get_uint8(v_t_117_, sizeof(void*)*3);
lean_dec_ref_known(v_t_117_, 3);
v___x_132_ = lean_box(v_isOn_131_);
v___x_133_ = lean_apply_4(v_k_118_, v_stx_128_, v_sign_129_, v_name_130_, v___x_132_);
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim(lean_object* v_motive_134_, lean_object* v_ctorIdx_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_k_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_136_, v_k_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___boxed(lean_object* v_motive_140_, lean_object* v_ctorIdx_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_k_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Doc_ArgView_ctorElim(v_motive_140_, v_ctorIdx_141_, v_t_142_, v_h_143_, v_k_144_);
lean_dec(v_ctorIdx_141_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim___redArg(lean_object* v_t_146_, lean_object* v_anon_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_146_, v_anon_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim(lean_object* v_motive_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_anon_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_150_, v_anon_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim___redArg(lean_object* v_t_154_, lean_object* v_named_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_154_, v_named_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim(lean_object* v_motive_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_named_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_158_, v_named_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim___redArg(lean_object* v_t_162_, lean_object* v_flag_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_162_, v_flag_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim(lean_object* v_motive_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_flag_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_166_, v_flag_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx(lean_object* v_x_170_){
_start:
{
lean_object* v_stx_171_; 
v_stx_171_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_stx_171_);
return v_stx_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx___boxed(lean_object* v_x_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Doc_ArgView_stx(v_x_172_);
lean_dec_ref(v_x_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_of(lean_object* v_stx_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__2));
lean_inc(v_stx_210_);
v___x_212_ = l_Lean_Syntax_isOfKind(v_stx_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__4));
lean_inc(v_stx_210_);
v___x_214_ = l_Lean_Syntax_isOfKind(v_stx_210_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__6));
lean_inc(v_stx_210_);
v___x_216_ = l_Lean_Syntax_isOfKind(v_stx_210_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__8));
lean_inc(v_stx_210_);
v___x_218_ = l_Lean_Syntax_isOfKind(v_stx_210_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__10));
lean_inc(v_stx_210_);
v___x_220_ = l_Lean_Syntax_isOfKind(v_stx_210_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec(v_stx_210_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v_x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_222_ = lean_unsigned_to_nat(1u);
v_x_223_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_222_);
v___x_224_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_223_);
v___x_225_ = l_Lean_Syntax_isOfKind(v_x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_dec(v_x_223_);
lean_dec(v_stx_210_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v_tk_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v_tk_228_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_227_);
v___x_229_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_229_, 0, v_stx_210_);
lean_ctor_set(v___x_229_, 1, v_tk_228_);
lean_ctor_set(v___x_229_, 2, v_x_223_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*3, v___x_218_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
}
else
{
lean_object* v___x_231_; lean_object* v_x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v_x_232_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_231_);
v___x_233_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_232_);
v___x_234_ = l_Lean_Syntax_isOfKind(v_x_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
lean_dec(v_x_232_);
lean_dec(v_stx_210_);
v___x_235_ = lean_box(0);
return v___x_235_;
}
else
{
lean_object* v___x_236_; lean_object* v_tk_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = lean_unsigned_to_nat(0u);
v_tk_237_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_236_);
v___x_238_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_238_, 0, v_stx_210_);
lean_ctor_set(v___x_238_, 1, v_tk_237_);
lean_ctor_set(v___x_238_, 2, v_x_232_);
lean_ctor_set_uint8(v___x_238_, sizeof(void*)*3, v___x_234_);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
}
else
{
lean_object* v___x_240_; lean_object* v_x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v_x_241_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_240_);
v___x_242_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_241_);
v___x_243_ = l_Lean_Syntax_isOfKind(v_x_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
lean_dec(v_x_241_);
lean_dec(v_stx_210_);
v___x_244_ = lean_box(0);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v_eq_246_; lean_object* v___x_247_; lean_object* v_v_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_245_ = lean_unsigned_to_nat(1u);
v_eq_246_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_245_);
v___x_247_ = lean_unsigned_to_nat(2u);
v_v_248_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_247_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(v___x_250_, 0, v_stx_210_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
lean_ctor_set(v___x_250_, 2, v_x_241_);
lean_ctor_set(v___x_250_, 3, v_eq_246_);
lean_ctor_set(v___x_250_, 4, v_v_248_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
}
else
{
lean_object* v___x_252_; lean_object* v_x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_252_ = lean_unsigned_to_nat(1u);
v_x_253_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_252_);
v___x_254_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_253_);
v___x_255_ = l_Lean_Syntax_isOfKind(v_x_253_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v_x_253_);
lean_dec(v_stx_210_);
v___x_256_ = lean_box(0);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v_po_258_; lean_object* v___x_259_; lean_object* v_eq_260_; lean_object* v___x_261_; lean_object* v_v_262_; lean_object* v___x_263_; lean_object* v_pc_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v_po_258_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_257_);
v___x_259_ = lean_unsigned_to_nat(2u);
v_eq_260_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_259_);
v___x_261_ = lean_unsigned_to_nat(3u);
v_v_262_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(4u);
v_pc_264_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v_po_258_);
lean_ctor_set(v___x_265_, 1, v_pc_264_);
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
v___x_267_ = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(v___x_267_, 0, v_stx_210_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
lean_ctor_set(v___x_267_, 2, v_x_253_);
lean_ctor_set(v___x_267_, 3, v_eq_260_);
lean_ctor_set(v___x_267_, 4, v_v_262_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
}
else
{
lean_object* v___x_269_; lean_object* v_v_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_269_ = lean_unsigned_to_nat(0u);
v_v_270_ = l_Lean_Syntax_getArg(v_stx_210_, v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v_stx_210_);
lean_ctor_set(v___x_271_, 1, v_v_270_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx___impl(lean_object* v_x_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_tag_nat(v_x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx___impl___boxed(lean_object* v_x_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Doc_LinkTargetView_ctorIdx___impl(v_x_275_);
lean_dec_ref(v_x_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___redArg(lean_object* v_t_277_, lean_object* v_k_278_){
_start:
{
lean_object* v_stx_279_; lean_object* v_opener_280_; lean_object* v_url_281_; lean_object* v_closer_282_; lean_object* v___x_283_; 
v_stx_279_ = lean_ctor_get(v_t_277_, 0);
lean_inc(v_stx_279_);
v_opener_280_ = lean_ctor_get(v_t_277_, 1);
lean_inc(v_opener_280_);
v_url_281_ = lean_ctor_get(v_t_277_, 2);
lean_inc(v_url_281_);
v_closer_282_ = lean_ctor_get(v_t_277_, 3);
lean_inc(v_closer_282_);
lean_dec_ref(v_t_277_);
v___x_283_ = lean_apply_4(v_k_278_, v_stx_279_, v_opener_280_, v_url_281_, v_closer_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim(lean_object* v_motive_284_, lean_object* v_ctorIdx_285_, lean_object* v_t_286_, lean_object* v_h_287_, lean_object* v_k_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_286_, v_k_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___boxed(lean_object* v_motive_290_, lean_object* v_ctorIdx_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_k_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Doc_LinkTargetView_ctorElim(v_motive_290_, v_ctorIdx_291_, v_t_292_, v_h_293_, v_k_294_);
lean_dec(v_ctorIdx_291_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim___redArg(lean_object* v_t_296_, lean_object* v_url_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_296_, v_url_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim(lean_object* v_motive_299_, lean_object* v_t_300_, lean_object* v_h_301_, lean_object* v_url_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_300_, v_url_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim___redArg(lean_object* v_t_304_, lean_object* v_ref_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_304_, v_ref_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim(lean_object* v_motive_307_, lean_object* v_t_308_, lean_object* v_h_309_, lean_object* v_ref_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_308_, v_ref_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(lean_object* v_tok_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Syntax_getHeadInfo(v_tok_312_);
switch(lean_obj_tag(v___x_313_))
{
case 0:
{
lean_object* v_leading_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_335_; 
v_leading_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; lean_object* v_unused_337_; lean_object* v_unused_338_; 
v_unused_336_ = lean_ctor_get(v___x_313_, 3);
lean_dec(v_unused_336_);
v_unused_337_ = lean_ctor_get(v___x_313_, 2);
lean_dec(v_unused_337_);
v_unused_338_ = lean_ctor_get(v___x_313_, 1);
lean_dec(v_unused_338_);
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_335_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_leading_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_335_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
uint8_t v___x_318_; lean_object* v___x_319_; 
v___x_318_ = 0;
v___x_319_ = l_Lean_Syntax_getPos_x3f(v_tok_312_, v___x_318_);
if (lean_obj_tag(v___x_319_) == 1)
{
lean_object* v_val_320_; lean_object* v_str_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_331_; 
v_val_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v___x_319_, 1);
v_str_321_ = lean_ctor_get(v_leading_314_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_leading_314_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; lean_object* v_unused_333_; 
v_unused_332_ = lean_ctor_get(v_leading_314_, 2);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_leading_314_, 1);
lean_dec(v_unused_333_);
v___x_323_ = v_leading_314_;
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_str_321_);
lean_dec(v_leading_314_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
lean_inc_n(v_val_320_, 2);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 2, v_val_320_);
lean_ctor_set(v___x_323_, 1, v_val_320_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_str_321_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_val_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_val_320_);
v___x_326_ = v_reuseFailAlloc_330_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
lean_inc(v_val_320_);
lean_inc_ref(v___x_326_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 3, v_val_320_);
lean_ctor_set(v___x_316_, 2, v___x_326_);
lean_ctor_set(v___x_316_, 1, v_val_320_);
lean_ctor_set(v___x_316_, 0, v___x_326_);
v___x_328_ = v___x_316_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_val_320_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v_val_320_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v___x_334_; 
lean_dec(v___x_319_);
lean_del_object(v___x_316_);
lean_dec_ref(v_leading_314_);
v___x_334_ = lean_box(2);
return v___x_334_;
}
}
}
case 1:
{
uint8_t v_canonical_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_350_; 
v_canonical_339_ = lean_ctor_get_uint8(v___x_313_, sizeof(void*)*2);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_351_ = lean_ctor_get(v___x_313_, 1);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v___x_313_, 0);
lean_dec(v_unused_352_);
v___x_341_ = v___x_313_;
v_isShared_342_ = v_isSharedCheck_350_;
goto v_resetjp_340_;
}
else
{
lean_dec(v___x_313_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_350_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
uint8_t v___x_343_; lean_object* v___x_344_; 
v___x_343_ = 0;
v___x_344_ = l_Lean_Syntax_getPos_x3f(v_tok_312_, v___x_343_);
if (lean_obj_tag(v___x_344_) == 1)
{
lean_object* v_val_345_; lean_object* v___x_347_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc_n(v_val_345_, 2);
lean_dec_ref_known(v___x_344_, 1);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v_val_345_);
lean_ctor_set(v___x_341_, 0, v_val_345_);
v___x_347_ = v___x_341_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_val_345_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_val_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_348_, sizeof(void*)*2, v_canonical_339_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
else
{
lean_object* v___x_349_; 
lean_dec(v___x_344_);
lean_del_object(v___x_341_);
v___x_349_ = lean_box(2);
return v___x_349_;
}
}
}
default: 
{
lean_object* v___x_353_; 
lean_dec(v___x_313_);
v___x_353_ = lean_box(2);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo___boxed(lean_object* v_tok_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v_tok_354_);
lean_dec(v_tok_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(lean_object* v___x_357_, lean_object* v_value_358_, lean_object* v_a_359_, lean_object* v_b_360_){
_start:
{
uint8_t v_decide_361_; 
v_decide_361_ = lean_nat_dec_eq(v_a_359_, v___x_357_);
if (v_decide_361_ == 0)
{
uint32_t v___x_362_; lean_object* v___x_363_; uint32_t v___x_364_; uint8_t v___x_365_; 
v___x_362_ = lean_string_utf8_get_fast(v_value_358_, v_a_359_);
v___x_363_ = lean_string_utf8_next_fast(v_value_358_, v_a_359_);
lean_dec(v_a_359_);
v___x_364_ = 92;
v___x_365_ = lean_uint32_dec_eq(v___x_362_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
v___x_366_ = lean_string_push(v_b_360_, v___x_362_);
v_a_359_ = v___x_363_;
v_b_360_ = v___x_366_;
goto _start;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0));
v___x_369_ = lean_string_append(v_b_360_, v___x_368_);
v_a_359_ = v___x_363_;
v_b_360_ = v___x_369_;
goto _start;
}
}
else
{
lean_dec(v_a_359_);
return v_b_360_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___boxed(lean_object* v___x_371_, lean_object* v_value_372_, lean_object* v_a_373_, lean_object* v_b_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_371_, v_value_372_, v_a_373_, v_b_374_);
lean_dec_ref(v_value_372_);
lean_dec(v___x_371_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(lean_object* v_value_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_378_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0));
v___x_379_ = lean_string_utf8_byte_size(v_value_377_);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_379_, v_value_377_, v___x_380_, v___x_378_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___boxed(lean_object* v_value_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_382_);
lean_dec_ref(v_value_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(lean_object* v___x_384_, lean_object* v___x_385_, lean_object* v_value_386_, lean_object* v_inst_387_, lean_object* v_R_388_, lean_object* v_a_389_, lean_object* v_b_390_, lean_object* v_c_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_385_, v_value_386_, v_a_389_, v_b_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___boxed(lean_object* v___x_393_, lean_object* v___x_394_, lean_object* v_value_395_, lean_object* v_inst_396_, lean_object* v_R_397_, lean_object* v_a_398_, lean_object* v_b_399_, lean_object* v_c_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(v___x_393_, v___x_394_, v_value_395_, v_inst_396_, v_R_397_, v_a_398_, v_b_399_, v_c_400_);
lean_dec_ref(v_value_395_);
lean_dec(v___x_394_);
lean_dec_ref(v___x_393_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom(lean_object* v_src_402_, lean_object* v_value_403_, uint8_t v_canonical_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = l_Lean_Doc_versoTextKind;
v___x_406_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_403_);
v___x_407_ = l_Lean_SourceInfo_fromRef(v_src_402_, v_canonical_404_);
v___x_408_ = l_Lean_Syntax_mkLit(v___x_405_, v___x_406_, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom___boxed(lean_object* v_src_409_, lean_object* v_value_410_, lean_object* v_canonical_411_){
_start:
{
uint8_t v_canonical_boxed_412_; lean_object* v_res_413_; 
v_canonical_boxed_412_ = lean_unbox(v_canonical_411_);
v_res_413_ = l_Lean_Doc_mkVersoTextFrom(v_src_409_, v_value_410_, v_canonical_boxed_412_);
lean_dec_ref(v_value_410_);
lean_dec(v_src_409_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom(lean_object* v_src_414_, lean_object* v_value_415_, uint8_t v_canonical_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = l_Lean_Doc_versoRefKind;
v___x_418_ = l_Lean_SourceInfo_fromRef(v_src_414_, v_canonical_416_);
v___x_419_ = l_Lean_Syntax_mkLit(v___x_417_, v_value_415_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom___boxed(lean_object* v_src_420_, lean_object* v_value_421_, lean_object* v_canonical_422_){
_start:
{
uint8_t v_canonical_boxed_423_; lean_object* v_res_424_; 
v_canonical_boxed_423_ = lean_unbox(v_canonical_422_);
v_res_424_ = l_Lean_Doc_mkVersoRefNameFrom(v_src_420_, v_value_421_, v_canonical_boxed_423_);
lean_dec(v_src_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom(lean_object* v_src_425_, lean_object* v_value_426_, uint8_t v_canonical_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = l_Lean_Doc_versoLinkUrlKind;
v___x_429_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_426_);
v___x_430_ = l_Lean_SourceInfo_fromRef(v_src_425_, v_canonical_427_);
v___x_431_ = l_Lean_Syntax_mkLit(v___x_428_, v___x_429_, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom___boxed(lean_object* v_src_432_, lean_object* v_value_433_, lean_object* v_canonical_434_){
_start:
{
uint8_t v_canonical_boxed_435_; lean_object* v_res_436_; 
v_canonical_boxed_435_ = lean_unbox(v_canonical_434_);
v_res_436_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_src_432_, v_value_433_, v_canonical_boxed_435_);
lean_dec_ref(v_value_433_);
lean_dec(v_src_432_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom(lean_object* v_src_437_, lean_object* v_value_438_, uint8_t v_canonical_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = l_Lean_Doc_versoImageAltKind;
v___x_441_ = l_Lean_Doc_escapeVersoImageAlt(v_value_438_);
v___x_442_ = l_Lean_SourceInfo_fromRef(v_src_437_, v_canonical_439_);
v___x_443_ = l_Lean_Syntax_mkLit(v___x_440_, v___x_441_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom___boxed(lean_object* v_src_444_, lean_object* v_value_445_, lean_object* v_canonical_446_){
_start:
{
uint8_t v_canonical_boxed_447_; lean_object* v_res_448_; 
v_canonical_boxed_447_ = lean_unbox(v_canonical_446_);
v_res_448_ = l_Lean_Doc_mkVersoImageAltFrom(v_src_444_, v_value_445_, v_canonical_boxed_447_);
lean_dec_ref(v_value_445_);
lean_dec(v_src_444_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom(lean_object* v_src_449_, lean_object* v_value_450_, uint8_t v_canonical_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = l_Lean_Doc_versoLinkRefUrlKind;
v___x_453_ = l_Lean_SourceInfo_fromRef(v_src_449_, v_canonical_451_);
v___x_454_ = l_Lean_Syntax_mkLit(v___x_452_, v_value_450_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom___boxed(lean_object* v_src_455_, lean_object* v_value_456_, lean_object* v_canonical_457_){
_start:
{
uint8_t v_canonical_boxed_458_; lean_object* v_res_459_; 
v_canonical_boxed_458_ = lean_unbox(v_canonical_457_);
v_res_459_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_src_455_, v_value_456_, v_canonical_boxed_458_);
lean_dec(v_src_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(lean_object* v_info_460_, lean_object* v___x_461_, lean_object* v_value_462_, lean_object* v_a_463_, lean_object* v_b_464_){
_start:
{
uint8_t v_decide_465_; 
v_decide_465_ = lean_nat_dec_eq(v_a_463_, v___x_461_);
if (v_decide_465_ == 0)
{
lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_488_; 
v_fst_466_ = lean_ctor_get(v_b_464_, 0);
v_snd_467_ = lean_ctor_get(v_b_464_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_b_464_);
if (v_isSharedCheck_488_ == 0)
{
v___x_469_ = v_b_464_;
v_isShared_470_ = v_isSharedCheck_488_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_467_);
lean_inc(v_fst_466_);
lean_dec(v_b_464_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_488_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
uint32_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint32_t v___x_474_; uint8_t v___x_475_; 
v___x_471_ = lean_string_utf8_get_fast(v_value_462_, v_a_463_);
v___x_472_ = lean_string_utf8_next_fast(v_value_462_, v_a_463_);
lean_dec(v_a_463_);
v___x_473_ = lean_string_push(v_snd_467_, v___x_471_);
v___x_474_ = 10;
v___x_475_ = lean_uint32_dec_eq(v___x_471_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_477_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v___x_473_);
v___x_477_ = v___x_469_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_fst_466_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_473_);
v___x_477_ = v_reuseFailAlloc_479_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
v_a_463_ = v___x_472_;
v_b_464_ = v___x_477_;
goto _start;
}
}
else
{
lean_object* v_line_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v_line_480_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0));
v___x_481_ = l_Lean_Doc_versoCodeLineKind;
lean_inc(v_info_460_);
v___x_482_ = l_Lean_Syntax_mkLit(v___x_481_, v___x_473_, v_info_460_);
v___x_483_ = lean_array_push(v_fst_466_, v___x_482_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v_line_480_);
lean_ctor_set(v___x_469_, 0, v___x_483_);
v___x_485_ = v___x_469_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_line_480_);
v___x_485_ = v_reuseFailAlloc_487_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
v_a_463_ = v___x_472_;
v_b_464_ = v___x_485_;
goto _start;
}
}
}
}
else
{
lean_dec(v_a_463_);
lean_dec(v_info_460_);
return v_b_464_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg___boxed(lean_object* v_info_489_, lean_object* v___x_490_, lean_object* v_value_491_, lean_object* v_a_492_, lean_object* v_b_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_489_, v___x_490_, v_value_491_, v_a_492_, v_b_493_);
lean_dec_ref(v_value_491_);
lean_dec(v___x_490_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(lean_object* v_info_500_, lean_object* v_value_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__1));
v___x_504_ = lean_string_utf8_byte_size(v_value_501_);
lean_inc(v_info_500_);
v___x_505_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_500_, v___x_504_, v_value_501_, v___x_502_, v___x_503_);
v_fst_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_fst_506_);
v_snd_507_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_snd_507_);
lean_dec_ref(v___x_505_);
v___x_512_ = lean_string_utf8_byte_size(v_snd_507_);
v___x_513_ = lean_nat_dec_eq(v___x_512_, v___x_502_);
if (v___x_513_ == 0)
{
goto v___jp_508_;
}
else
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_array_get_size(v_fst_506_);
v___x_515_ = lean_nat_dec_eq(v___x_514_, v___x_502_);
if (v___x_515_ == 0)
{
lean_dec(v_snd_507_);
lean_dec(v_info_500_);
return v_fst_506_;
}
else
{
goto v___jp_508_;
}
}
v___jp_508_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = l_Lean_Doc_versoCodeLineKind;
v___x_510_ = l_Lean_Syntax_mkLit(v___x_509_, v_snd_507_, v_info_500_);
v___x_511_ = lean_array_push(v_fst_506_, v___x_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___boxed(lean_object* v_info_516_, lean_object* v_value_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_516_, v_value_517_);
lean_dec_ref(v_value_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(lean_object* v_info_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v_value_522_, lean_object* v_inst_523_, lean_object* v_R_524_, lean_object* v_a_525_, lean_object* v_b_526_, lean_object* v_c_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_519_, v___x_521_, v_value_522_, v_a_525_, v_b_526_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___boxed(lean_object* v_info_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v_value_532_, lean_object* v_inst_533_, lean_object* v_R_534_, lean_object* v_a_535_, lean_object* v_b_536_, lean_object* v_c_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(v_info_529_, v___x_530_, v___x_531_, v_value_532_, v_inst_533_, v_R_534_, v_a_535_, v_b_536_, v_c_537_);
lean_dec_ref(v_value_532_);
lean_dec(v___x_531_);
lean_dec_ref(v___x_530_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom(lean_object* v_src_542_, lean_object* v_value_543_, uint8_t v_canonical_544_){
_start:
{
lean_object* v_info_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_info_545_ = l_Lean_SourceInfo_fromRef(v_src_542_, v_canonical_544_);
v___x_546_ = l_Lean_Doc_versoCodeKind;
lean_inc(v_info_545_);
v___x_547_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_545_, v_value_543_);
v___x_548_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_549_ = lean_box(2);
v___x_550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
lean_ctor_set(v___x_550_, 2, v___x_547_);
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = lean_mk_empty_array_with_capacity(v___x_551_);
v___x_553_ = lean_array_push(v___x_552_, v___x_550_);
v___x_554_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_554_, 0, v_info_545_);
lean_ctor_set(v___x_554_, 1, v___x_546_);
lean_ctor_set(v___x_554_, 2, v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom___boxed(lean_object* v_src_555_, lean_object* v_value_556_, lean_object* v_canonical_557_){
_start:
{
uint8_t v_canonical_boxed_558_; lean_object* v_res_559_; 
v_canonical_boxed_558_ = lean_unbox(v_canonical_557_);
v_res_559_ = l_Lean_Doc_mkVersoCodeFrom(v_src_555_, v_value_556_, v_canonical_boxed_558_);
lean_dec_ref(v_value_556_);
lean_dec(v_src_555_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom(lean_object* v_src_560_, lean_object* v_value_561_, uint8_t v_canonical_562_){
_start:
{
lean_object* v_info_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_info_563_ = l_Lean_SourceInfo_fromRef(v_src_560_, v_canonical_562_);
v___x_564_ = l_Lean_Doc_versoCodeBlockKind;
lean_inc(v_info_563_);
v___x_565_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_563_, v_value_561_);
v___x_566_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_567_ = lean_box(2);
v___x_568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_566_);
lean_ctor_set(v___x_568_, 2, v___x_565_);
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_mk_empty_array_with_capacity(v___x_569_);
v___x_571_ = lean_array_push(v___x_570_, v___x_568_);
v___x_572_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_572_, 0, v_info_563_);
lean_ctor_set(v___x_572_, 1, v___x_564_);
lean_ctor_set(v___x_572_, 2, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___boxed(lean_object* v_src_573_, lean_object* v_value_574_, lean_object* v_canonical_575_){
_start:
{
uint8_t v_canonical_boxed_576_; lean_object* v_res_577_; 
v_canonical_boxed_576_ = lean_unbox(v_canonical_575_);
v_res_577_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_src_573_, v_value_574_, v_canonical_boxed_576_);
lean_dec_ref(v_value_574_);
lean_dec(v_src_573_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom(lean_object* v_src_587_, uint8_t v_canonical_588_){
_start:
{
lean_object* v_info_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_info_589_ = l_Lean_SourceInfo_fromRef(v_src_587_, v_canonical_588_);
v___x_590_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
v___x_591_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__3));
lean_inc(v_info_589_);
v___x_592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_592_, 0, v_info_589_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_mk_empty_array_with_capacity(v___x_593_);
v___x_595_ = lean_array_push(v___x_594_, v___x_592_);
v___x_596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_596_, 0, v_info_589_);
lean_ctor_set(v___x_596_, 1, v___x_590_);
lean_ctor_set(v___x_596_, 2, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom___boxed(lean_object* v_src_597_, lean_object* v_canonical_598_){
_start:
{
uint8_t v_canonical_boxed_599_; lean_object* v_res_600_; 
v_canonical_boxed_599_ = lean_unbox(v_canonical_598_);
v_res_600_ = l_Lean_Doc_mkVersoLinebreakFrom(v_src_597_, v_canonical_boxed_599_);
lean_dec(v_src_597_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(uint8_t v_canonical_601_, lean_object* v_toPure_602_, lean_object* v_____do__lift_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = l_Lean_Doc_mkVersoLinebreakFrom(v_____do__lift_603_, v_canonical_601_);
v___x_605_ = lean_apply_2(v_toPure_602_, lean_box(0), v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed(lean_object* v_canonical_606_, lean_object* v_toPure_607_, lean_object* v_____do__lift_608_){
_start:
{
uint8_t v_canonical_boxed_609_; lean_object* v_res_610_; 
v_canonical_boxed_609_ = lean_unbox(v_canonical_606_);
v_res_610_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(v_canonical_boxed_609_, v_toPure_607_, v_____do__lift_608_);
lean_dec(v_____do__lift_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg(lean_object* v_inst_611_, lean_object* v_inst_612_, uint8_t v_canonical_613_){
_start:
{
lean_object* v_toApplicative_614_; lean_object* v_toBind_615_; lean_object* v_getRef_616_; lean_object* v_toPure_617_; lean_object* v___x_618_; lean_object* v___f_619_; lean_object* v___x_620_; 
v_toApplicative_614_ = lean_ctor_get(v_inst_611_, 0);
lean_inc_ref(v_toApplicative_614_);
v_toBind_615_ = lean_ctor_get(v_inst_611_, 1);
lean_inc(v_toBind_615_);
lean_dec_ref(v_inst_611_);
v_getRef_616_ = lean_ctor_get(v_inst_612_, 0);
lean_inc(v_getRef_616_);
lean_dec_ref(v_inst_612_);
v_toPure_617_ = lean_ctor_get(v_toApplicative_614_, 1);
lean_inc(v_toPure_617_);
lean_dec_ref(v_toApplicative_614_);
v___x_618_ = lean_box(v_canonical_613_);
v___f_619_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_619_, 0, v___x_618_);
lean_closure_set(v___f_619_, 1, v_toPure_617_);
v___x_620_ = lean_apply_4(v_toBind_615_, lean_box(0), lean_box(0), v_getRef_616_, v___f_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___boxed(lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_canonical_623_){
_start:
{
uint8_t v_canonical_boxed_624_; lean_object* v_res_625_; 
v_canonical_boxed_624_ = lean_unbox(v_canonical_623_);
v_res_625_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_621_, v_inst_622_, v_canonical_boxed_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef(lean_object* v_m_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, uint8_t v_canonical_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_627_, v_inst_628_, v_canonical_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___boxed(lean_object* v_m_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_canonical_634_){
_start:
{
uint8_t v_canonical_boxed_635_; lean_object* v_res_636_; 
v_canonical_boxed_635_ = lean_unbox(v_canonical_634_);
v_res_636_ = l_Lean_Doc_mkVersoLinebreakFromRef(v_m_631_, v_inst_632_, v_inst_633_, v_canonical_boxed_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(lean_object* v_value_637_, uint8_t v_canonical_638_, lean_object* v_toPure_639_, lean_object* v_____do__lift_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = l_Lean_Doc_mkVersoTextFrom(v_____do__lift_640_, v_value_637_, v_canonical_638_);
v___x_642_ = lean_apply_2(v_toPure_639_, lean_box(0), v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed(lean_object* v_value_643_, lean_object* v_canonical_644_, lean_object* v_toPure_645_, lean_object* v_____do__lift_646_){
_start:
{
uint8_t v_canonical_boxed_647_; lean_object* v_res_648_; 
v_canonical_boxed_647_ = lean_unbox(v_canonical_644_);
v_res_648_ = l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(v_value_643_, v_canonical_boxed_647_, v_toPure_645_, v_____do__lift_646_);
lean_dec(v_____do__lift_646_);
lean_dec_ref(v_value_643_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg(lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_value_651_, uint8_t v_canonical_652_){
_start:
{
lean_object* v_toApplicative_653_; lean_object* v_toBind_654_; lean_object* v_getRef_655_; lean_object* v_toPure_656_; lean_object* v___x_657_; lean_object* v___f_658_; lean_object* v___x_659_; 
v_toApplicative_653_ = lean_ctor_get(v_inst_649_, 0);
lean_inc_ref(v_toApplicative_653_);
v_toBind_654_ = lean_ctor_get(v_inst_649_, 1);
lean_inc(v_toBind_654_);
lean_dec_ref(v_inst_649_);
v_getRef_655_ = lean_ctor_get(v_inst_650_, 0);
lean_inc(v_getRef_655_);
lean_dec_ref(v_inst_650_);
v_toPure_656_ = lean_ctor_get(v_toApplicative_653_, 1);
lean_inc(v_toPure_656_);
lean_dec_ref(v_toApplicative_653_);
v___x_657_ = lean_box(v_canonical_652_);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_658_, 0, v_value_651_);
lean_closure_set(v___f_658_, 1, v___x_657_);
lean_closure_set(v___f_658_, 2, v_toPure_656_);
v___x_659_ = lean_apply_4(v_toBind_654_, lean_box(0), lean_box(0), v_getRef_655_, v___f_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___boxed(lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_value_662_, lean_object* v_canonical_663_){
_start:
{
uint8_t v_canonical_boxed_664_; lean_object* v_res_665_; 
v_canonical_boxed_664_ = lean_unbox(v_canonical_663_);
v_res_665_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_660_, v_inst_661_, v_value_662_, v_canonical_boxed_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef(lean_object* v_m_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_value_669_, uint8_t v_canonical_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_667_, v_inst_668_, v_value_669_, v_canonical_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___boxed(lean_object* v_m_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_value_675_, lean_object* v_canonical_676_){
_start:
{
uint8_t v_canonical_boxed_677_; lean_object* v_res_678_; 
v_canonical_boxed_677_ = lean_unbox(v_canonical_676_);
v_res_678_ = l_Lean_Doc_mkVersoTextFromRef(v_m_672_, v_inst_673_, v_inst_674_, v_value_675_, v_canonical_boxed_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(lean_object* v_value_679_, uint8_t v_canonical_680_, lean_object* v_toPure_681_, lean_object* v_____do__lift_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = l_Lean_Doc_mkVersoRefNameFrom(v_____do__lift_682_, v_value_679_, v_canonical_680_);
v___x_684_ = lean_apply_2(v_toPure_681_, lean_box(0), v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed(lean_object* v_value_685_, lean_object* v_canonical_686_, lean_object* v_toPure_687_, lean_object* v_____do__lift_688_){
_start:
{
uint8_t v_canonical_boxed_689_; lean_object* v_res_690_; 
v_canonical_boxed_689_ = lean_unbox(v_canonical_686_);
v_res_690_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(v_value_685_, v_canonical_boxed_689_, v_toPure_687_, v_____do__lift_688_);
lean_dec(v_____do__lift_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg(lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_value_693_, uint8_t v_canonical_694_){
_start:
{
lean_object* v_toApplicative_695_; lean_object* v_toBind_696_; lean_object* v_getRef_697_; lean_object* v_toPure_698_; lean_object* v___x_699_; lean_object* v___f_700_; lean_object* v___x_701_; 
v_toApplicative_695_ = lean_ctor_get(v_inst_691_, 0);
lean_inc_ref(v_toApplicative_695_);
v_toBind_696_ = lean_ctor_get(v_inst_691_, 1);
lean_inc(v_toBind_696_);
lean_dec_ref(v_inst_691_);
v_getRef_697_ = lean_ctor_get(v_inst_692_, 0);
lean_inc(v_getRef_697_);
lean_dec_ref(v_inst_692_);
v_toPure_698_ = lean_ctor_get(v_toApplicative_695_, 1);
lean_inc(v_toPure_698_);
lean_dec_ref(v_toApplicative_695_);
v___x_699_ = lean_box(v_canonical_694_);
v___f_700_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_700_, 0, v_value_693_);
lean_closure_set(v___f_700_, 1, v___x_699_);
lean_closure_set(v___f_700_, 2, v_toPure_698_);
v___x_701_ = lean_apply_4(v_toBind_696_, lean_box(0), lean_box(0), v_getRef_697_, v___f_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___boxed(lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_value_704_, lean_object* v_canonical_705_){
_start:
{
uint8_t v_canonical_boxed_706_; lean_object* v_res_707_; 
v_canonical_boxed_706_ = lean_unbox(v_canonical_705_);
v_res_707_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_702_, v_inst_703_, v_value_704_, v_canonical_boxed_706_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef(lean_object* v_m_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_value_711_, uint8_t v_canonical_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_709_, v_inst_710_, v_value_711_, v_canonical_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___boxed(lean_object* v_m_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_value_717_, lean_object* v_canonical_718_){
_start:
{
uint8_t v_canonical_boxed_719_; lean_object* v_res_720_; 
v_canonical_boxed_719_ = lean_unbox(v_canonical_718_);
v_res_720_ = l_Lean_Doc_mkVersoRefNameFromRef(v_m_714_, v_inst_715_, v_inst_716_, v_value_717_, v_canonical_boxed_719_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(lean_object* v_value_721_, uint8_t v_canonical_722_, lean_object* v_toPure_723_, lean_object* v_____do__lift_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_____do__lift_724_, v_value_721_, v_canonical_722_);
v___x_726_ = lean_apply_2(v_toPure_723_, lean_box(0), v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_727_, lean_object* v_canonical_728_, lean_object* v_toPure_729_, lean_object* v_____do__lift_730_){
_start:
{
uint8_t v_canonical_boxed_731_; lean_object* v_res_732_; 
v_canonical_boxed_731_ = lean_unbox(v_canonical_728_);
v_res_732_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(v_value_727_, v_canonical_boxed_731_, v_toPure_729_, v_____do__lift_730_);
lean_dec(v_____do__lift_730_);
lean_dec_ref(v_value_727_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_value_735_, uint8_t v_canonical_736_){
_start:
{
lean_object* v_toApplicative_737_; lean_object* v_toBind_738_; lean_object* v_getRef_739_; lean_object* v_toPure_740_; lean_object* v___x_741_; lean_object* v___f_742_; lean_object* v___x_743_; 
v_toApplicative_737_ = lean_ctor_get(v_inst_733_, 0);
lean_inc_ref(v_toApplicative_737_);
v_toBind_738_ = lean_ctor_get(v_inst_733_, 1);
lean_inc(v_toBind_738_);
lean_dec_ref(v_inst_733_);
v_getRef_739_ = lean_ctor_get(v_inst_734_, 0);
lean_inc(v_getRef_739_);
lean_dec_ref(v_inst_734_);
v_toPure_740_ = lean_ctor_get(v_toApplicative_737_, 1);
lean_inc(v_toPure_740_);
lean_dec_ref(v_toApplicative_737_);
v___x_741_ = lean_box(v_canonical_736_);
v___f_742_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_742_, 0, v_value_735_);
lean_closure_set(v___f_742_, 1, v___x_741_);
lean_closure_set(v___f_742_, 2, v_toPure_740_);
v___x_743_ = lean_apply_4(v_toBind_738_, lean_box(0), lean_box(0), v_getRef_739_, v___f_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___boxed(lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_value_746_, lean_object* v_canonical_747_){
_start:
{
uint8_t v_canonical_boxed_748_; lean_object* v_res_749_; 
v_canonical_boxed_748_ = lean_unbox(v_canonical_747_);
v_res_749_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_744_, v_inst_745_, v_value_746_, v_canonical_boxed_748_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef(lean_object* v_m_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_value_753_, uint8_t v_canonical_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_751_, v_inst_752_, v_value_753_, v_canonical_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___boxed(lean_object* v_m_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_value_759_, lean_object* v_canonical_760_){
_start:
{
uint8_t v_canonical_boxed_761_; lean_object* v_res_762_; 
v_canonical_boxed_761_ = lean_unbox(v_canonical_760_);
v_res_762_ = l_Lean_Doc_mkVersoLinkUrlFromRef(v_m_756_, v_inst_757_, v_inst_758_, v_value_759_, v_canonical_boxed_761_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(lean_object* v_value_763_, uint8_t v_canonical_764_, lean_object* v_toPure_765_, lean_object* v_____do__lift_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = l_Lean_Doc_mkVersoImageAltFrom(v_____do__lift_766_, v_value_763_, v_canonical_764_);
v___x_768_ = lean_apply_2(v_toPure_765_, lean_box(0), v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed(lean_object* v_value_769_, lean_object* v_canonical_770_, lean_object* v_toPure_771_, lean_object* v_____do__lift_772_){
_start:
{
uint8_t v_canonical_boxed_773_; lean_object* v_res_774_; 
v_canonical_boxed_773_ = lean_unbox(v_canonical_770_);
v_res_774_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(v_value_769_, v_canonical_boxed_773_, v_toPure_771_, v_____do__lift_772_);
lean_dec(v_____do__lift_772_);
lean_dec_ref(v_value_769_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg(lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_value_777_, uint8_t v_canonical_778_){
_start:
{
lean_object* v_toApplicative_779_; lean_object* v_toBind_780_; lean_object* v_getRef_781_; lean_object* v_toPure_782_; lean_object* v___x_783_; lean_object* v___f_784_; lean_object* v___x_785_; 
v_toApplicative_779_ = lean_ctor_get(v_inst_775_, 0);
lean_inc_ref(v_toApplicative_779_);
v_toBind_780_ = lean_ctor_get(v_inst_775_, 1);
lean_inc(v_toBind_780_);
lean_dec_ref(v_inst_775_);
v_getRef_781_ = lean_ctor_get(v_inst_776_, 0);
lean_inc(v_getRef_781_);
lean_dec_ref(v_inst_776_);
v_toPure_782_ = lean_ctor_get(v_toApplicative_779_, 1);
lean_inc(v_toPure_782_);
lean_dec_ref(v_toApplicative_779_);
v___x_783_ = lean_box(v_canonical_778_);
v___f_784_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_784_, 0, v_value_777_);
lean_closure_set(v___f_784_, 1, v___x_783_);
lean_closure_set(v___f_784_, 2, v_toPure_782_);
v___x_785_ = lean_apply_4(v_toBind_780_, lean_box(0), lean_box(0), v_getRef_781_, v___f_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___boxed(lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_value_788_, lean_object* v_canonical_789_){
_start:
{
uint8_t v_canonical_boxed_790_; lean_object* v_res_791_; 
v_canonical_boxed_790_ = lean_unbox(v_canonical_789_);
v_res_791_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_786_, v_inst_787_, v_value_788_, v_canonical_boxed_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef(lean_object* v_m_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_value_795_, uint8_t v_canonical_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_793_, v_inst_794_, v_value_795_, v_canonical_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___boxed(lean_object* v_m_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_value_801_, lean_object* v_canonical_802_){
_start:
{
uint8_t v_canonical_boxed_803_; lean_object* v_res_804_; 
v_canonical_boxed_803_ = lean_unbox(v_canonical_802_);
v_res_804_ = l_Lean_Doc_mkVersoImageAltFromRef(v_m_798_, v_inst_799_, v_inst_800_, v_value_801_, v_canonical_boxed_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(lean_object* v_value_805_, uint8_t v_canonical_806_, lean_object* v_toPure_807_, lean_object* v_____do__lift_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_____do__lift_808_, v_value_805_, v_canonical_806_);
v___x_810_ = lean_apply_2(v_toPure_807_, lean_box(0), v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_811_, lean_object* v_canonical_812_, lean_object* v_toPure_813_, lean_object* v_____do__lift_814_){
_start:
{
uint8_t v_canonical_boxed_815_; lean_object* v_res_816_; 
v_canonical_boxed_815_ = lean_unbox(v_canonical_812_);
v_res_816_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(v_value_811_, v_canonical_boxed_815_, v_toPure_813_, v_____do__lift_814_);
lean_dec(v_____do__lift_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_value_819_, uint8_t v_canonical_820_){
_start:
{
lean_object* v_toApplicative_821_; lean_object* v_toBind_822_; lean_object* v_getRef_823_; lean_object* v_toPure_824_; lean_object* v___x_825_; lean_object* v___f_826_; lean_object* v___x_827_; 
v_toApplicative_821_ = lean_ctor_get(v_inst_817_, 0);
lean_inc_ref(v_toApplicative_821_);
v_toBind_822_ = lean_ctor_get(v_inst_817_, 1);
lean_inc(v_toBind_822_);
lean_dec_ref(v_inst_817_);
v_getRef_823_ = lean_ctor_get(v_inst_818_, 0);
lean_inc(v_getRef_823_);
lean_dec_ref(v_inst_818_);
v_toPure_824_ = lean_ctor_get(v_toApplicative_821_, 1);
lean_inc(v_toPure_824_);
lean_dec_ref(v_toApplicative_821_);
v___x_825_ = lean_box(v_canonical_820_);
v___f_826_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_826_, 0, v_value_819_);
lean_closure_set(v___f_826_, 1, v___x_825_);
lean_closure_set(v___f_826_, 2, v_toPure_824_);
v___x_827_ = lean_apply_4(v_toBind_822_, lean_box(0), lean_box(0), v_getRef_823_, v___f_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___boxed(lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_value_830_, lean_object* v_canonical_831_){
_start:
{
uint8_t v_canonical_boxed_832_; lean_object* v_res_833_; 
v_canonical_boxed_832_ = lean_unbox(v_canonical_831_);
v_res_833_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_828_, v_inst_829_, v_value_830_, v_canonical_boxed_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef(lean_object* v_m_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_value_837_, uint8_t v_canonical_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_835_, v_inst_836_, v_value_837_, v_canonical_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___boxed(lean_object* v_m_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_value_843_, lean_object* v_canonical_844_){
_start:
{
uint8_t v_canonical_boxed_845_; lean_object* v_res_846_; 
v_canonical_boxed_845_ = lean_unbox(v_canonical_844_);
v_res_846_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef(v_m_840_, v_inst_841_, v_inst_842_, v_value_843_, v_canonical_boxed_845_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(lean_object* v_value_847_, uint8_t v_canonical_848_, lean_object* v_toPure_849_, lean_object* v_____do__lift_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = l_Lean_Doc_mkVersoCodeFrom(v_____do__lift_850_, v_value_847_, v_canonical_848_);
v___x_852_ = lean_apply_2(v_toPure_849_, lean_box(0), v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed(lean_object* v_value_853_, lean_object* v_canonical_854_, lean_object* v_toPure_855_, lean_object* v_____do__lift_856_){
_start:
{
uint8_t v_canonical_boxed_857_; lean_object* v_res_858_; 
v_canonical_boxed_857_ = lean_unbox(v_canonical_854_);
v_res_858_ = l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(v_value_853_, v_canonical_boxed_857_, v_toPure_855_, v_____do__lift_856_);
lean_dec(v_____do__lift_856_);
lean_dec_ref(v_value_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg(lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_value_861_, uint8_t v_canonical_862_){
_start:
{
lean_object* v_toApplicative_863_; lean_object* v_toBind_864_; lean_object* v_getRef_865_; lean_object* v_toPure_866_; lean_object* v___x_867_; lean_object* v___f_868_; lean_object* v___x_869_; 
v_toApplicative_863_ = lean_ctor_get(v_inst_859_, 0);
lean_inc_ref(v_toApplicative_863_);
v_toBind_864_ = lean_ctor_get(v_inst_859_, 1);
lean_inc(v_toBind_864_);
lean_dec_ref(v_inst_859_);
v_getRef_865_ = lean_ctor_get(v_inst_860_, 0);
lean_inc(v_getRef_865_);
lean_dec_ref(v_inst_860_);
v_toPure_866_ = lean_ctor_get(v_toApplicative_863_, 1);
lean_inc(v_toPure_866_);
lean_dec_ref(v_toApplicative_863_);
v___x_867_ = lean_box(v_canonical_862_);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_868_, 0, v_value_861_);
lean_closure_set(v___f_868_, 1, v___x_867_);
lean_closure_set(v___f_868_, 2, v_toPure_866_);
v___x_869_ = lean_apply_4(v_toBind_864_, lean_box(0), lean_box(0), v_getRef_865_, v___f_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___boxed(lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_value_872_, lean_object* v_canonical_873_){
_start:
{
uint8_t v_canonical_boxed_874_; lean_object* v_res_875_; 
v_canonical_boxed_874_ = lean_unbox(v_canonical_873_);
v_res_875_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_870_, v_inst_871_, v_value_872_, v_canonical_boxed_874_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef(lean_object* v_m_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_value_879_, uint8_t v_canonical_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_877_, v_inst_878_, v_value_879_, v_canonical_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___boxed(lean_object* v_m_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_value_885_, lean_object* v_canonical_886_){
_start:
{
uint8_t v_canonical_boxed_887_; lean_object* v_res_888_; 
v_canonical_boxed_887_ = lean_unbox(v_canonical_886_);
v_res_888_ = l_Lean_Doc_mkVersoCodeFromRef(v_m_882_, v_inst_883_, v_inst_884_, v_value_885_, v_canonical_boxed_887_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(lean_object* v_value_889_, uint8_t v_canonical_890_, lean_object* v_toPure_891_, lean_object* v_____do__lift_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_____do__lift_892_, v_value_889_, v_canonical_890_);
v___x_894_ = lean_apply_2(v_toPure_891_, lean_box(0), v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed(lean_object* v_value_895_, lean_object* v_canonical_896_, lean_object* v_toPure_897_, lean_object* v_____do__lift_898_){
_start:
{
uint8_t v_canonical_boxed_899_; lean_object* v_res_900_; 
v_canonical_boxed_899_ = lean_unbox(v_canonical_896_);
v_res_900_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(v_value_895_, v_canonical_boxed_899_, v_toPure_897_, v_____do__lift_898_);
lean_dec(v_____do__lift_898_);
lean_dec_ref(v_value_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v_value_903_, uint8_t v_canonical_904_){
_start:
{
lean_object* v_toApplicative_905_; lean_object* v_toBind_906_; lean_object* v_getRef_907_; lean_object* v_toPure_908_; lean_object* v___x_909_; lean_object* v___f_910_; lean_object* v___x_911_; 
v_toApplicative_905_ = lean_ctor_get(v_inst_901_, 0);
lean_inc_ref(v_toApplicative_905_);
v_toBind_906_ = lean_ctor_get(v_inst_901_, 1);
lean_inc(v_toBind_906_);
lean_dec_ref(v_inst_901_);
v_getRef_907_ = lean_ctor_get(v_inst_902_, 0);
lean_inc(v_getRef_907_);
lean_dec_ref(v_inst_902_);
v_toPure_908_ = lean_ctor_get(v_toApplicative_905_, 1);
lean_inc(v_toPure_908_);
lean_dec_ref(v_toApplicative_905_);
v___x_909_ = lean_box(v_canonical_904_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_910_, 0, v_value_903_);
lean_closure_set(v___f_910_, 1, v___x_909_);
lean_closure_set(v___f_910_, 2, v_toPure_908_);
v___x_911_ = lean_apply_4(v_toBind_906_, lean_box(0), lean_box(0), v_getRef_907_, v___f_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___boxed(lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_value_914_, lean_object* v_canonical_915_){
_start:
{
uint8_t v_canonical_boxed_916_; lean_object* v_res_917_; 
v_canonical_boxed_916_ = lean_unbox(v_canonical_915_);
v_res_917_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_912_, v_inst_913_, v_value_914_, v_canonical_boxed_916_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef(lean_object* v_m_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_value_921_, uint8_t v_canonical_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_919_, v_inst_920_, v_value_921_, v_canonical_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___boxed(lean_object* v_m_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_value_927_, lean_object* v_canonical_928_){
_start:
{
uint8_t v_canonical_boxed_929_; lean_object* v_res_930_; 
v_canonical_boxed_929_ = lean_unbox(v_canonical_928_);
v_res_930_ = l_Lean_Doc_mkVersoCodeBlockFromRef(v_m_924_, v_inst_925_, v_inst_926_, v_value_927_, v_canonical_boxed_929_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_of(lean_object* v_stx_958_){
_start:
{
lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__2));
lean_inc(v_stx_958_);
v___x_960_ = l_Lean_Syntax_isOfKind(v_stx_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__4));
lean_inc(v_stx_958_);
v___x_962_ = l_Lean_Syntax_isOfKind(v_stx_958_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec(v_stx_958_);
v___x_963_ = lean_box(0);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v_name_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_964_ = lean_unsigned_to_nat(1u);
v_name_965_ = l_Lean_Syntax_getArg(v_stx_958_, v___x_964_);
v___x_966_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_965_);
v___x_967_ = l_Lean_Syntax_isOfKind(v_name_965_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
lean_dec(v_name_965_);
lean_dec(v_stx_958_);
v___x_968_ = lean_box(0);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v_o_970_; lean_object* v___x_971_; lean_object* v_c_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v_o_970_ = l_Lean_Syntax_getArg(v_stx_958_, v___x_969_);
v___x_971_ = lean_unsigned_to_nat(2u);
v_c_972_ = l_Lean_Syntax_getArg(v_stx_958_, v___x_971_);
v___x_973_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_973_, 0, v_stx_958_);
lean_ctor_set(v___x_973_, 1, v_o_970_);
lean_ctor_set(v___x_973_, 2, v_name_965_);
lean_ctor_set(v___x_973_, 3, v_c_972_);
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
}
else
{
lean_object* v___x_975_; lean_object* v_url_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_975_ = lean_unsigned_to_nat(1u);
v_url_976_ = l_Lean_Syntax_getArg(v_stx_958_, v___x_975_);
v___x_977_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__8));
lean_inc(v_url_976_);
v___x_978_ = l_Lean_Syntax_isOfKind(v_url_976_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_dec(v_url_976_);
lean_dec(v_stx_958_);
v___x_979_ = lean_box(0);
return v___x_979_;
}
else
{
lean_object* v___x_980_; lean_object* v_o_981_; lean_object* v___x_982_; lean_object* v_c_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_980_ = lean_unsigned_to_nat(0u);
v_o_981_ = l_Lean_Syntax_getArg(v_stx_958_, v___x_980_);
v___x_982_ = lean_unsigned_to_nat(2u);
v_c_983_ = l_Lean_Syntax_getArg(v_stx_958_, v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_984_, 0, v_stx_958_);
lean_ctor_set(v___x_984_, 1, v_o_981_);
lean_ctor_set(v___x_984_, 2, v_url_976_);
lean_ctor_set(v___x_984_, 3, v_c_983_);
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText(lean_object* v_v_990_){
_start:
{
lean_object* v_content_991_; lean_object* v___x_992_; 
v_content_991_ = lean_ctor_get(v_v_990_, 1);
v___x_992_ = l_Lean_TSyntax_getVersoText(v_content_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText___boxed(lean_object* v_v_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Doc_TextView_getVersoText(v_v_993_);
lean_dec_ref(v_v_993_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object* v_v_995_){
_start:
{
lean_object* v_content_996_; lean_object* v___x_997_; 
v_content_996_ = lean_ctor_get(v_v_995_, 1);
v___x_997_ = l_Lean_TSyntax_getVersoTextSource(v_content_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource___boxed(lean_object* v_v_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Doc_TextView_getVersoTextSource(v_v_998_);
lean_dec_ref(v_v_998_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_of(lean_object* v_stx_1013_){
_start:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__1));
lean_inc(v_stx_1013_);
v___x_1015_ = l_Lean_Syntax_isOfKind(v_stx_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
lean_dec(v_stx_1013_);
v___x_1016_ = lean_box(0);
return v___x_1016_;
}
else
{
lean_object* v___x_1017_; lean_object* v_s_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v_s_1018_ = l_Lean_Syntax_getArg(v_stx_1013_, v___x_1017_);
v___x_1019_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__3));
lean_inc(v_s_1018_);
v___x_1020_ = l_Lean_Syntax_isOfKind(v_s_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec(v_s_1018_);
lean_dec(v_stx_1013_);
v___x_1021_ = lean_box(0);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_stx_1013_);
lean_ctor_set(v___x_1022_, 1, v_s_1018_);
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_EmphView_of(lean_object* v_stx_1037_){
_start:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_Doc_EmphView_of___closed__1));
lean_inc(v_stx_1037_);
v___x_1039_ = l_Lean_Syntax_isOfKind(v_stx_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec(v_stx_1037_);
v___x_1040_ = lean_box(0);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; lean_object* v_o_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1041_ = lean_unsigned_to_nat(0u);
v_o_1042_ = l_Lean_Syntax_getArg(v_stx_1037_, v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_Doc_EmphView_of___closed__3));
lean_inc(v_o_1042_);
v___x_1044_ = l_Lean_Syntax_isOfKind(v_o_1042_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
lean_dec(v_o_1042_);
lean_dec(v_stx_1037_);
v___x_1045_ = lean_box(0);
return v___x_1045_;
}
else
{
lean_object* v___x_1046_; lean_object* v_c_1047_; uint8_t v___x_1048_; 
v___x_1046_ = lean_unsigned_to_nat(2u);
v_c_1047_ = l_Lean_Syntax_getArg(v_stx_1037_, v___x_1046_);
lean_inc(v_c_1047_);
v___x_1048_ = l_Lean_Syntax_isOfKind(v_c_1047_, v___x_1043_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec(v_c_1047_);
lean_dec(v_o_1042_);
lean_dec(v_stx_1037_);
v___x_1049_ = lean_box(0);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v_inl_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = l_Lean_Syntax_getArg(v_stx_1037_, v___x_1050_);
v_inl_1052_ = l_Lean_Syntax_getArgs(v___x_1051_);
lean_dec(v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1053_, 0, v_stx_1037_);
lean_ctor_set(v___x_1053_, 1, v_o_1042_);
lean_ctor_set(v___x_1053_, 2, v_inl_1052_);
lean_ctor_set(v___x_1053_, 3, v_c_1047_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BoldView_of(lean_object* v_stx_1068_){
_start:
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_Doc_BoldView_of___closed__1));
lean_inc(v_stx_1068_);
v___x_1070_ = l_Lean_Syntax_isOfKind(v_stx_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_dec(v_stx_1068_);
v___x_1071_ = lean_box(0);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; lean_object* v_o_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v_o_1073_ = l_Lean_Syntax_getArg(v_stx_1068_, v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Lean_Doc_BoldView_of___closed__3));
lean_inc(v_o_1073_);
v___x_1075_ = l_Lean_Syntax_isOfKind(v_o_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
lean_dec(v_o_1073_);
lean_dec(v_stx_1068_);
v___x_1076_ = lean_box(0);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; lean_object* v_c_1078_; uint8_t v___x_1079_; 
v___x_1077_ = lean_unsigned_to_nat(2u);
v_c_1078_ = l_Lean_Syntax_getArg(v_stx_1068_, v___x_1077_);
lean_inc(v_c_1078_);
v___x_1079_ = l_Lean_Syntax_isOfKind(v_c_1078_, v___x_1074_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
lean_dec(v_c_1078_);
lean_dec(v_o_1073_);
lean_dec(v_stx_1068_);
v___x_1080_ = lean_box(0);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v_inl_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = l_Lean_Syntax_getArg(v_stx_1068_, v___x_1081_);
v_inl_1083_ = l_Lean_Syntax_getArgs(v___x_1082_);
lean_dec(v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1084_, 0, v_stx_1068_);
lean_ctor_set(v___x_1084_, 1, v_o_1073_);
lean_ctor_set(v___x_1084_, 2, v_inl_1083_);
lean_ctor_set(v___x_1084_, 3, v_c_1078_);
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object* v_v_1086_){
_start:
{
lean_object* v_content_1087_; lean_object* v___x_1088_; 
v_content_1087_ = lean_ctor_get(v_v_1086_, 2);
v___x_1088_ = l_Lean_TSyntax_getVersoCode(v_content_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode___boxed(lean_object* v_v_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Doc_CodeView_getVersoCode(v_v_1089_);
lean_dec_ref(v_v_1089_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_of(lean_object* v_stx_1110_){
_start:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v_stx_1110_);
v___x_1112_ = l_Lean_Syntax_isOfKind(v_stx_1110_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec(v_stx_1110_);
v___x_1113_ = lean_box(0);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; lean_object* v_o_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1114_ = lean_unsigned_to_nat(0u);
v_o_1115_ = l_Lean_Syntax_getArg(v_stx_1110_, v___x_1114_);
v___x_1116_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__3));
lean_inc(v_o_1115_);
v___x_1117_ = l_Lean_Syntax_isOfKind(v_o_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_dec(v_o_1115_);
lean_dec(v_stx_1110_);
v___x_1118_ = lean_box(0);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; lean_object* v_s_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1119_ = lean_unsigned_to_nat(1u);
v_s_1120_ = l_Lean_Syntax_getArg(v_stx_1110_, v___x_1119_);
v___x_1121_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__5));
lean_inc(v_s_1120_);
v___x_1122_ = l_Lean_Syntax_isOfKind(v_s_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec(v_s_1120_);
lean_dec(v_o_1115_);
lean_dec(v_stx_1110_);
v___x_1123_ = lean_box(0);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; lean_object* v_c_1125_; uint8_t v___x_1126_; 
v___x_1124_ = lean_unsigned_to_nat(2u);
v_c_1125_ = l_Lean_Syntax_getArg(v_stx_1110_, v___x_1124_);
lean_inc(v_c_1125_);
v___x_1126_ = l_Lean_Syntax_isOfKind(v_c_1125_, v___x_1116_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
lean_dec(v_c_1125_);
lean_dec(v_s_1120_);
lean_dec(v_o_1115_);
lean_dec(v_stx_1110_);
v___x_1127_ = lean_box(0);
return v___x_1127_;
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1128_, 0, v_stx_1110_);
lean_ctor_set(v___x_1128_, 1, v_o_1115_);
lean_ctor_set(v___x_1128_, 2, v_s_1120_);
lean_ctor_set(v___x_1128_, 3, v_c_1125_);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object* v_v_1130_){
_start:
{
lean_object* v_code_1131_; lean_object* v___x_1132_; 
v_code_1131_ = lean_ctor_get(v_v_1130_, 2);
v___x_1132_ = l_Lean_Doc_CodeView_getVersoCode(v_code_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode___boxed(lean_object* v_v_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Doc_MathView_getVersoCode(v_v_1133_);
lean_dec_ref(v_v_1133_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_of(lean_object* v_stx_1161_){
_start:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__1));
lean_inc(v_stx_1161_);
v___x_1163_ = l_Lean_Syntax_isOfKind(v_stx_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__3));
lean_inc(v_stx_1161_);
v___x_1165_ = l_Lean_Syntax_isOfKind(v_stx_1161_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec(v_stx_1161_);
v___x_1166_ = lean_box(0);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = l_Lean_Syntax_getArg(v_stx_1161_, v___x_1167_);
v___x_1169_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__5));
lean_inc(v___x_1168_);
v___x_1170_ = l_Lean_Syntax_isOfKind(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_dec(v___x_1168_);
lean_dec(v_stx_1161_);
v___x_1171_ = lean_box(0);
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = l_Lean_Syntax_getArg(v_stx_1161_, v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v___x_1173_);
v___x_1175_ = l_Lean_Syntax_isOfKind(v___x_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
lean_dec(v___x_1173_);
lean_dec(v___x_1168_);
lean_dec(v_stx_1161_);
v___x_1176_ = lean_box(0);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_Doc_CodeView_of(v___x_1173_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v___x_1178_; 
lean_dec(v___x_1168_);
lean_dec(v_stx_1161_);
v___x_1178_ = lean_box(0);
return v___x_1178_;
}
else
{
lean_object* v_val_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1188_; 
v_val_1179_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1181_ = v___x_1177_;
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_val_1179_);
lean_dec(v___x_1177_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
uint8_t v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1183_ = 1;
v___x_1184_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1184_, 0, v_stx_1161_);
lean_ctor_set(v___x_1184_, 1, v___x_1168_);
lean_ctor_set(v___x_1184_, 2, v_val_1179_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*3, v___x_1183_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1184_);
v___x_1186_ = v___x_1181_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = l_Lean_Syntax_getArg(v_stx_1161_, v___x_1189_);
v___x_1191_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__7));
lean_inc(v___x_1190_);
v___x_1192_ = l_Lean_Syntax_isOfKind(v___x_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
lean_dec(v___x_1190_);
lean_dec(v_stx_1161_);
v___x_1193_ = lean_box(0);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = l_Lean_Syntax_getArg(v_stx_1161_, v___x_1194_);
v___x_1196_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v___x_1195_);
v___x_1197_ = l_Lean_Syntax_isOfKind(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec(v___x_1195_);
lean_dec(v___x_1190_);
lean_dec(v_stx_1161_);
v___x_1198_ = lean_box(0);
return v___x_1198_;
}
else
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Doc_CodeView_of(v___x_1195_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v___x_1200_; 
lean_dec(v___x_1190_);
lean_dec(v_stx_1161_);
v___x_1200_ = lean_box(0);
return v___x_1200_;
}
else
{
lean_object* v_val_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1210_; 
v_val_1201_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1203_ = v___x_1199_;
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_val_1201_);
lean_dec(v___x_1199_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1205_ = 0;
v___x_1206_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1206_, 0, v_stx_1161_);
lean_ctor_set(v___x_1206_, 1, v___x_1190_);
lean_ctor_set(v___x_1206_, 2, v_val_1201_);
lean_ctor_set_uint8(v___x_1206_, sizeof(void*)*3, v___x_1205_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1206_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkView_of(lean_object* v_stx_1218_){
_start:
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Doc_LinkView_of___closed__1));
lean_inc(v_stx_1218_);
v___x_1220_ = l_Lean_Syntax_isOfKind(v_stx_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
lean_dec(v_stx_1218_);
v___x_1221_ = lean_box(0);
return v___x_1221_;
}
else
{
lean_object* v___x_1222_; lean_object* v_tgt_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_unsigned_to_nat(3u);
v_tgt_1223_ = l_Lean_Syntax_getArg(v_stx_1218_, v___x_1222_);
v___x_1224_ = l_Lean_Doc_LinkTargetView_of(v_tgt_1223_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v___x_1225_; 
lean_dec(v_stx_1218_);
v___x_1225_ = lean_box(0);
return v___x_1225_;
}
else
{
lean_object* v_val_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1241_; 
v_val_1226_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1228_ = v___x_1224_;
v_isShared_1229_ = v_isSharedCheck_1241_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_val_1226_);
lean_dec(v___x_1224_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1241_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v_o_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_c_1235_; lean_object* v_inl_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1230_ = lean_unsigned_to_nat(0u);
v_o_1231_ = l_Lean_Syntax_getArg(v_stx_1218_, v___x_1230_);
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = l_Lean_Syntax_getArg(v_stx_1218_, v___x_1232_);
v___x_1234_ = lean_unsigned_to_nat(2u);
v_c_1235_ = l_Lean_Syntax_getArg(v_stx_1218_, v___x_1234_);
v_inl_1236_ = l_Lean_Syntax_getArgs(v___x_1233_);
lean_dec(v___x_1233_);
v___x_1237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1237_, 0, v_stx_1218_);
lean_ctor_set(v___x_1237_, 1, v_o_1231_);
lean_ctor_set(v___x_1237_, 2, v_inl_1236_);
lean_ctor_set(v___x_1237_, 3, v_c_1235_);
lean_ctor_set(v___x_1237_, 4, v_val_1226_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1237_);
v___x_1239_ = v___x_1228_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt(lean_object* v_v_1242_){
_start:
{
lean_object* v_alt_1243_; lean_object* v___x_1244_; 
v_alt_1243_ = lean_ctor_get(v_v_1242_, 2);
v___x_1244_ = l_Lean_TSyntax_getVersoImageAlt(v_alt_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt___boxed(lean_object* v_v_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Doc_ImageView_getAlt(v_v_1245_);
lean_dec_ref(v_v_1245_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_of(lean_object* v_stx_1260_){
_start:
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__1));
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
lean_object* v___x_1264_; lean_object* v_alt_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1264_ = lean_unsigned_to_nat(1u);
v_alt_1265_ = l_Lean_Syntax_getArg(v_stx_1260_, v___x_1264_);
v___x_1266_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__3));
lean_inc(v_alt_1265_);
v___x_1267_ = l_Lean_Syntax_isOfKind(v_alt_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec(v_alt_1265_);
lean_dec(v_stx_1260_);
v___x_1268_ = lean_box(0);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; lean_object* v_tgt_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_unsigned_to_nat(3u);
v_tgt_1270_ = l_Lean_Syntax_getArg(v_stx_1260_, v___x_1269_);
v___x_1271_ = l_Lean_Doc_LinkTargetView_of(v_tgt_1270_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1272_; 
lean_dec(v_alt_1265_);
lean_dec(v_stx_1260_);
v___x_1272_ = lean_box(0);
return v___x_1272_;
}
else
{
lean_object* v_val_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1285_; 
v_val_1273_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1275_ = v___x_1271_;
v_isShared_1276_ = v_isSharedCheck_1285_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_val_1273_);
lean_dec(v___x_1271_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1285_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v_o_1278_; lean_object* v___x_1279_; lean_object* v_c_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1277_ = lean_unsigned_to_nat(0u);
v_o_1278_ = l_Lean_Syntax_getArg(v_stx_1260_, v___x_1277_);
v___x_1279_ = lean_unsigned_to_nat(2u);
v_c_1280_ = l_Lean_Syntax_getArg(v_stx_1260_, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1281_, 0, v_stx_1260_);
lean_ctor_set(v___x_1281_, 1, v_o_1278_);
lean_ctor_set(v___x_1281_, 2, v_alt_1265_);
lean_ctor_set(v___x_1281_, 3, v_c_1280_);
lean_ctor_set(v___x_1281_, 4, v_val_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1281_);
v___x_1283_ = v___x_1275_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName(lean_object* v_v_1286_){
_start:
{
lean_object* v_name_1287_; lean_object* v___x_1288_; 
v_name_1287_ = lean_ctor_get(v_v_1286_, 2);
v___x_1288_ = l_Lean_TSyntax_getVersoRefName(v_name_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName___boxed(lean_object* v_v_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Doc_FootnoteView_getName(v_v_1289_);
lean_dec_ref(v_v_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_of(lean_object* v_stx_1298_){
_start:
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_Doc_FootnoteView_of___closed__1));
lean_inc(v_stx_1298_);
v___x_1300_ = l_Lean_Syntax_isOfKind(v_stx_1298_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
lean_dec(v_stx_1298_);
v___x_1301_ = lean_box(0);
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; lean_object* v_name_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1302_ = lean_unsigned_to_nat(1u);
v_name_1303_ = l_Lean_Syntax_getArg(v_stx_1298_, v___x_1302_);
v___x_1304_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_1303_);
v___x_1305_ = l_Lean_Syntax_isOfKind(v_name_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_dec(v_name_1303_);
lean_dec(v_stx_1298_);
v___x_1306_ = lean_box(0);
return v___x_1306_;
}
else
{
lean_object* v___x_1307_; lean_object* v_o_1308_; lean_object* v___x_1309_; lean_object* v_c_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1307_ = lean_unsigned_to_nat(0u);
v_o_1308_ = l_Lean_Syntax_getArg(v_stx_1298_, v___x_1307_);
v___x_1309_ = lean_unsigned_to_nat(2u);
v_c_1310_ = l_Lean_Syntax_getArg(v_stx_1298_, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1311_, 0, v_stx_1298_);
lean_ctor_set(v___x_1311_, 1, v_o_1308_);
lean_ctor_set(v___x_1311_, 2, v_name_1303_);
lean_ctor_set(v___x_1311_, 3, v_c_1310_);
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinebreakView_of(lean_object* v_stx_1313_){
_start:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
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
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = l_Lean_Syntax_getArg(v_stx_1313_, v___x_1317_);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v_stx_1313_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_RoleView_of(lean_object* v_stx_1328_){
_start:
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_Doc_RoleView_of___closed__1));
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
lean_object* v___x_1332_; lean_object* v_name_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1332_ = lean_unsigned_to_nat(1u);
v_name_1333_ = l_Lean_Syntax_getArg(v_stx_1328_, v___x_1332_);
v___x_1334_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_1333_);
v___x_1335_ = l_Lean_Syntax_isOfKind(v_name_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_dec(v_name_1333_);
lean_dec(v_stx_1328_);
v___x_1336_ = lean_box(0);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; lean_object* v_bo_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_bc_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1337_ = lean_unsigned_to_nat(0u);
v_bo_1338_ = l_Lean_Syntax_getArg(v_stx_1328_, v___x_1337_);
v___x_1339_ = lean_unsigned_to_nat(2u);
v___x_1340_ = l_Lean_Syntax_getArg(v_stx_1328_, v___x_1339_);
v___x_1341_ = lean_unsigned_to_nat(3u);
v_bc_1342_ = l_Lean_Syntax_getArg(v_stx_1328_, v___x_1341_);
v___x_1343_ = lean_unsigned_to_nat(4u);
v___x_1344_ = l_Lean_Syntax_getArg(v_stx_1328_, v___x_1343_);
lean_inc(v___x_1344_);
v___x_1345_ = l_Lean_Syntax_matchesNull(v___x_1344_, v___x_1332_);
if (v___x_1345_ == 0)
{
uint8_t v___x_1346_; 
v___x_1346_ = l_Lean_Syntax_matchesNull(v___x_1344_, v___x_1337_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec(v_bc_1342_);
lean_dec(v___x_1340_);
lean_dec(v_bo_1338_);
lean_dec(v_name_1333_);
lean_dec(v_stx_1328_);
v___x_1347_ = lean_box(0);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = lean_unsigned_to_nat(6u);
v___x_1349_ = l_Lean_Syntax_getArg(v_stx_1328_, v___x_1348_);
v___x_1350_ = l_Lean_Syntax_matchesNull(v___x_1349_, v___x_1337_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_dec(v_bc_1342_);
lean_dec(v___x_1340_);
lean_dec(v_bo_1338_);
lean_dec(v_name_1333_);
lean_dec(v_stx_1328_);
v___x_1351_ = lean_box(0);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v_inl_1354_; lean_object* v_args_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1352_ = lean_unsigned_to_nat(5u);
v___x_1353_ = l_Lean_Syntax_getArg(v_stx_1328_, v___x_1352_);
v_inl_1354_ = l_Lean_Syntax_getArgs(v___x_1353_);
lean_dec(v___x_1353_);
v_args_1355_ = l_Lean_Syntax_getArgs(v___x_1340_);
lean_dec(v___x_1340_);
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1357_, 0, v_stx_1328_);
lean_ctor_set(v___x_1357_, 1, v_bo_1338_);
lean_ctor_set(v___x_1357_, 2, v_name_1333_);
lean_ctor_set(v___x_1357_, 3, v_args_1355_);
lean_ctor_set(v___x_1357_, 4, v_bc_1342_);
lean_ctor_set(v___x_1357_, 5, v___x_1356_);
lean_ctor_set(v___x_1357_, 6, v_inl_1354_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1359_ = lean_unsigned_to_nat(6u);
v___x_1360_ = l_Lean_Syntax_getArg(v_stx_1328_, v___x_1359_);
lean_inc(v___x_1360_);
v___x_1361_ = l_Lean_Syntax_matchesNull(v___x_1360_, v___x_1332_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_dec(v___x_1360_);
lean_dec(v___x_1344_);
lean_dec(v_bc_1342_);
lean_dec(v___x_1340_);
lean_dec(v_bo_1338_);
lean_dec(v_name_1333_);
lean_dec(v_stx_1328_);
v___x_1362_ = lean_box(0);
return v___x_1362_;
}
else
{
lean_object* v_so_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_sc_1366_; lean_object* v_inl_1367_; lean_object* v_args_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_so_1363_ = l_Lean_Syntax_getArg(v___x_1344_, v___x_1337_);
lean_dec(v___x_1344_);
v___x_1364_ = lean_unsigned_to_nat(5u);
v___x_1365_ = l_Lean_Syntax_getArg(v_stx_1328_, v___x_1364_);
v_sc_1366_ = l_Lean_Syntax_getArg(v___x_1360_, v___x_1337_);
lean_dec(v___x_1360_);
v_inl_1367_ = l_Lean_Syntax_getArgs(v___x_1365_);
lean_dec(v___x_1365_);
v_args_1368_ = l_Lean_Syntax_getArgs(v___x_1340_);
lean_dec(v___x_1340_);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_so_1363_);
lean_ctor_set(v___x_1369_, 1, v_sc_1366_);
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
v___x_1371_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1371_, 0, v_stx_1328_);
lean_ctor_set(v___x_1371_, 1, v_bo_1338_);
lean_ctor_set(v___x_1371_, 2, v_name_1333_);
lean_ctor_set(v___x_1371_, 3, v_args_1368_);
lean_ctor_set(v___x_1371_, 4, v_bc_1342_);
lean_ctor_set(v___x_1371_, 5, v___x_1370_);
lean_ctor_set(v___x_1371_, 6, v_inl_1367_);
v___x_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___impl(lean_object* v_x_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_obj_tag_nat(v_x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___impl___boxed(lean_object* v_x_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_Doc_InlineView_ctorIdx___impl(v_x_1375_);
lean_dec_ref(v_x_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___redArg(lean_object* v_t_1377_, lean_object* v_k_1378_){
_start:
{
lean_object* v_view_1379_; lean_object* v___x_1380_; 
v_view_1379_ = lean_ctor_get(v_t_1377_, 0);
lean_inc_ref(v_view_1379_);
lean_dec_ref(v_t_1377_);
v___x_1380_ = lean_apply_1(v_k_1378_, v_view_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim(lean_object* v_motive_1381_, lean_object* v_ctorIdx_1382_, lean_object* v_t_1383_, lean_object* v_h_1384_, lean_object* v_k_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1383_, v_k_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___boxed(lean_object* v_motive_1387_, lean_object* v_ctorIdx_1388_, lean_object* v_t_1389_, lean_object* v_h_1390_, lean_object* v_k_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Doc_InlineView_ctorElim(v_motive_1387_, v_ctorIdx_1388_, v_t_1389_, v_h_1390_, v_k_1391_);
lean_dec(v_ctorIdx_1388_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim___redArg(lean_object* v_t_1393_, lean_object* v_text_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1393_, v_text_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim(lean_object* v_motive_1396_, lean_object* v_t_1397_, lean_object* v_h_1398_, lean_object* v_text_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1397_, v_text_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim___redArg(lean_object* v_t_1401_, lean_object* v_emph_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1401_, v_emph_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim(lean_object* v_motive_1404_, lean_object* v_t_1405_, lean_object* v_h_1406_, lean_object* v_emph_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1405_, v_emph_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim___redArg(lean_object* v_t_1409_, lean_object* v_bold_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1409_, v_bold_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim(lean_object* v_motive_1412_, lean_object* v_t_1413_, lean_object* v_h_1414_, lean_object* v_bold_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1413_, v_bold_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim___redArg(lean_object* v_t_1417_, lean_object* v_code_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1417_, v_code_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim(lean_object* v_motive_1420_, lean_object* v_t_1421_, lean_object* v_h_1422_, lean_object* v_code_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1421_, v_code_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim___redArg(lean_object* v_t_1425_, lean_object* v_math_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1425_, v_math_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim(lean_object* v_motive_1428_, lean_object* v_t_1429_, lean_object* v_h_1430_, lean_object* v_math_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1429_, v_math_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim___redArg(lean_object* v_t_1433_, lean_object* v_link_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1433_, v_link_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim(lean_object* v_motive_1436_, lean_object* v_t_1437_, lean_object* v_h_1438_, lean_object* v_link_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1437_, v_link_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim___redArg(lean_object* v_t_1441_, lean_object* v_image_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1441_, v_image_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim(lean_object* v_motive_1444_, lean_object* v_t_1445_, lean_object* v_h_1446_, lean_object* v_image_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1445_, v_image_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim___redArg(lean_object* v_t_1449_, lean_object* v_footnote_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1449_, v_footnote_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim(lean_object* v_motive_1452_, lean_object* v_t_1453_, lean_object* v_h_1454_, lean_object* v_footnote_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1453_, v_footnote_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim___redArg(lean_object* v_t_1457_, lean_object* v_linebreak_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1457_, v_linebreak_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim(lean_object* v_motive_1460_, lean_object* v_t_1461_, lean_object* v_h_1462_, lean_object* v_linebreak_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1461_, v_linebreak_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim___redArg(lean_object* v_t_1465_, lean_object* v_role_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1465_, v_role_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim(lean_object* v_motive_1468_, lean_object* v_t_1469_, lean_object* v_h_1470_, lean_object* v_role_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1469_, v_role_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTextViewInlineView___lam__0(lean_object* v_view_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_view_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeEmphViewInlineView___lam__0(lean_object* v_view_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_view_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBoldViewInlineView___lam__0(lean_object* v_view_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_view_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeViewInlineView___lam__0(lean_object* v_view_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_view_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMathViewInlineView___lam__0(lean_object* v_view_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_view_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkViewInlineView___lam__0(lean_object* v_view_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_view_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeImageViewInlineView___lam__0(lean_object* v_view_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_view_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0(lean_object* v_view_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_view_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0(lean_object* v_view_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_view_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeRoleViewInlineView___lam__0(lean_object* v_view_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_view_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx(lean_object* v_x_1517_){
_start:
{
lean_object* v_view_1518_; lean_object* v_stx_1519_; 
v_view_1518_ = lean_ctor_get(v_x_1517_, 0);
v_stx_1519_ = lean_ctor_get(v_view_1518_, 0);
lean_inc(v_stx_1519_);
return v_stx_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx___boxed(lean_object* v_x_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Doc_InlineView_stx(v_x_1520_);
lean_dec_ref(v_x_1520_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_of(lean_object* v_stx_1522_){
_start:
{
lean_object* v___x_1523_; 
lean_inc(v_stx_1522_);
v___x_1523_ = l_Lean_Doc_TextView_of(v_stx_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1524_; 
lean_inc(v_stx_1522_);
v___x_1524_ = l_Lean_Doc_EmphView_of(v_stx_1522_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1525_; 
lean_inc(v_stx_1522_);
v___x_1525_ = l_Lean_Doc_BoldView_of(v_stx_1522_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v___x_1526_; 
lean_inc(v_stx_1522_);
v___x_1526_ = l_Lean_Doc_CodeView_of(v_stx_1522_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v___x_1527_; 
lean_inc(v_stx_1522_);
v___x_1527_ = l_Lean_Doc_MathView_of(v_stx_1522_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1528_; 
lean_inc(v_stx_1522_);
v___x_1528_ = l_Lean_Doc_LinkView_of(v_stx_1522_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v___x_1529_; 
lean_inc(v_stx_1522_);
v___x_1529_ = l_Lean_Doc_ImageView_of(v_stx_1522_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v___x_1530_; 
lean_inc(v_stx_1522_);
v___x_1530_ = l_Lean_Doc_FootnoteView_of(v_stx_1522_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v___x_1531_; 
lean_inc(v_stx_1522_);
v___x_1531_ = l_Lean_Doc_LinebreakView_of(v_stx_1522_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Doc_RoleView_of(v_stx_1522_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_box(0);
return v___x_1533_;
}
else
{
lean_object* v_val_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1542_; 
v_val_1534_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1536_ = v___x_1532_;
v_isShared_1537_ = v_isSharedCheck_1542_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_val_1534_);
lean_dec(v___x_1532_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1542_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1538_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_val_1534_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1538_);
v___x_1540_ = v___x_1536_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_val_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_stx_1522_);
v_val_1543_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1545_ = v___x_1531_;
v_isShared_1546_ = v_isSharedCheck_1551_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_val_1543_);
lean_dec(v___x_1531_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1551_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_val_1543_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1547_);
v___x_1549_ = v___x_1545_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_val_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_stx_1522_);
v_val_1552_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1554_ = v___x_1530_;
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_val_1552_);
lean_dec(v___x_1530_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_val_1552_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1556_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_val_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_stx_1522_);
v_val_1561_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1563_ = v___x_1529_;
v_isShared_1564_ = v_isSharedCheck_1569_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_val_1561_);
lean_dec(v___x_1529_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1569_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1565_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1565_, 0, v_val_1561_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1565_);
v___x_1567_ = v___x_1563_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_object* v_val_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_stx_1522_);
v_val_1570_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1572_ = v___x_1528_;
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_val_1570_);
lean_dec(v___x_1528_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_val_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v_val_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_stx_1522_);
v_val_1579_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1581_ = v___x_1527_;
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_val_1579_);
lean_dec(v___x_1527_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_val_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
lean_object* v_val_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_stx_1522_);
v_val_1588_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1590_ = v___x_1526_;
v_isShared_1591_ = v_isSharedCheck_1596_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_val_1588_);
lean_dec(v___x_1526_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1596_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_val_1588_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1592_);
v___x_1594_ = v___x_1590_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_stx_1522_);
v_val_1597_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1599_ = v___x_1525_;
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_val_1597_);
lean_dec(v___x_1525_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_val_1597_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1601_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_object* v_val_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_stx_1522_);
v_val_1606_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1608_ = v___x_1524_;
v_isShared_1609_ = v_isSharedCheck_1614_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_val_1606_);
lean_dec(v___x_1524_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1614_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_val_1606_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1610_);
v___x_1612_ = v___x_1608_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_object* v_val_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_stx_1522_);
v_val_1615_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1617_ = v___x_1523_;
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_val_1615_);
lean_dec(v___x_1523_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v_val_1615_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1619_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(uint32_t v_a_1624_, lean_object* v_x_1625_){
_start:
{
if (lean_obj_tag(v_x_1625_) == 0)
{
uint8_t v___x_1626_; 
v___x_1626_ = 0;
return v___x_1626_;
}
else
{
lean_object* v_head_1627_; lean_object* v_tail_1628_; uint32_t v___x_1629_; uint8_t v___x_1630_; 
v_head_1627_ = lean_ctor_get(v_x_1625_, 0);
v_tail_1628_ = lean_ctor_get(v_x_1625_, 1);
v___x_1629_ = lean_unbox_uint32(v_head_1627_);
v___x_1630_ = lean_uint32_dec_eq(v_a_1624_, v___x_1629_);
if (v___x_1630_ == 0)
{
v_x_1625_ = v_tail_1628_;
goto _start;
}
else
{
return v___x_1630_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0___boxed(lean_object* v_a_1632_, lean_object* v_x_1633_){
_start:
{
uint32_t v_a_boxed_1634_; uint8_t v_res_1635_; lean_object* v_r_1636_; 
v_a_boxed_1634_ = lean_unbox_uint32(v_a_1632_);
lean_dec(v_a_1632_);
v_res_1635_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v_a_boxed_1634_, v_x_1633_);
lean_dec(v_x_1633_);
v_r_1636_ = lean_box(v_res_1635_);
return v_r_1636_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = 43;
v___x_1652_ = lean_box_uint32(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__5(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_box(0);
v___x_1654_ = l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1;
v___x_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1653_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = 45;
v___x_1657_ = lean_box_uint32(v___x_1656_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__6(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__5, &l_Lean_Doc_UnorderedListItemView_of___closed__5_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__5);
v___x_1659_ = l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1;
v___x_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
lean_ctor_set(v___x_1660_, 1, v___x_1658_);
return v___x_1660_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = 42;
v___x_1662_ = lean_box_uint32(v___x_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__7(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__6, &l_Lean_Doc_UnorderedListItemView_of___closed__6_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__6);
v___x_1664_ = l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1;
v___x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v___x_1663_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of(lean_object* v_stx_1666_){
_start:
{
lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1667_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__2));
lean_inc(v_stx_1666_);
v___x_1668_ = l_Lean_Syntax_isOfKind(v_stx_1666_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
lean_dec(v_stx_1666_);
v___x_1669_ = lean_box(0);
return v___x_1669_;
}
else
{
lean_object* v___x_1670_; lean_object* v_m_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
v_m_1671_ = l_Lean_Syntax_getArg(v_stx_1666_, v___x_1670_);
v___x_1672_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__4));
lean_inc(v_m_1671_);
v___x_1673_ = l_Lean_Syntax_isOfKind(v_m_1671_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
lean_dec(v_m_1671_);
lean_dec(v_stx_1666_);
v___x_1674_ = lean_box(0);
return v___x_1674_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1675_ = l_Lean_TSyntax_getVersoDelimiter(v_m_1671_);
v___x_1676_ = lean_string_utf8_byte_size(v___x_1675_);
v___x_1677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1670_);
lean_ctor_set(v___x_1677_, 2, v___x_1676_);
v___x_1678_ = l_String_Slice_Pos_get_x3f(v___x_1677_, v___x_1670_);
lean_dec_ref_known(v___x_1677_, 3);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v___x_1679_; 
lean_dec(v_m_1671_);
lean_dec(v_stx_1666_);
v___x_1679_ = lean_box(0);
return v___x_1679_;
}
else
{
lean_object* v_val_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1695_; 
v_val_1680_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1682_ = v___x_1678_;
v_isShared_1683_ = v_isSharedCheck_1695_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_val_1680_);
lean_dec(v___x_1678_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1695_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; uint32_t v___x_1685_; uint8_t v___x_1686_; 
v___x_1684_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__7, &l_Lean_Doc_UnorderedListItemView_of___closed__7_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__7);
v___x_1685_ = lean_unbox_uint32(v_val_1680_);
lean_dec(v_val_1680_);
v___x_1686_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v___x_1685_, v___x_1684_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; 
lean_del_object(v___x_1682_);
lean_dec(v_m_1671_);
lean_dec(v_stx_1666_);
v___x_1687_ = lean_box(0);
return v___x_1687_;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_bs_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = l_Lean_Syntax_getArg(v_stx_1666_, v___x_1688_);
v_bs_1690_ = l_Lean_Syntax_getArgs(v___x_1689_);
lean_dec(v___x_1689_);
v___x_1691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1691_, 0, v_stx_1666_);
lean_ctor_set(v___x_1691_, 1, v_m_1671_);
lean_ctor_set(v___x_1691_, 2, v_bs_1690_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1691_);
v___x_1693_ = v___x_1682_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(lean_object* v_s_1696_, lean_object* v_pos_1697_){
_start:
{
lean_object* v_str_1698_; lean_object* v_startInclusive_1699_; lean_object* v_endExclusive_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v_decide_1704_; 
v_str_1698_ = lean_ctor_get(v_s_1696_, 0);
v_startInclusive_1699_ = lean_ctor_get(v_s_1696_, 1);
v_endExclusive_1700_ = lean_ctor_get(v_s_1696_, 2);
v___x_1701_ = lean_nat_add(v_startInclusive_1699_, v_pos_1697_);
v___x_1702_ = lean_unsigned_to_nat(0u);
v___x_1703_ = lean_nat_sub(v_endExclusive_1700_, v___x_1701_);
v_decide_1704_ = lean_nat_dec_eq(v___x_1702_, v___x_1703_);
lean_dec(v___x_1703_);
if (v_decide_1704_ == 0)
{
uint32_t v___x_1705_; uint32_t v___x_1706_; uint8_t v___x_1707_; 
v___x_1705_ = lean_string_utf8_get_fast(v_str_1698_, v___x_1701_);
v___x_1706_ = 48;
v___x_1707_ = lean_uint32_dec_le(v___x_1706_, v___x_1705_);
if (v___x_1707_ == 0)
{
lean_dec(v___x_1701_);
return v_pos_1697_;
}
else
{
uint32_t v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = 57;
v___x_1709_ = lean_uint32_dec_le(v___x_1705_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_dec(v___x_1701_);
return v_pos_1697_;
}
else
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1710_ = lean_string_utf8_next_fast(v_str_1698_, v___x_1701_);
v___x_1711_ = lean_nat_sub(v___x_1710_, v___x_1701_);
lean_dec(v___x_1701_);
v___x_1712_ = lean_nat_add(v_pos_1697_, v___x_1711_);
lean_dec(v___x_1711_);
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_nat_add(v_pos_1697_, v___x_1713_);
v___x_1715_ = lean_nat_dec_le(v___x_1714_, v___x_1712_);
lean_dec(v___x_1714_);
if (v___x_1715_ == 0)
{
lean_dec(v___x_1712_);
return v_pos_1697_;
}
else
{
lean_dec(v_pos_1697_);
v_pos_1697_ = v___x_1712_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_1701_);
return v_pos_1697_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0___boxed(lean_object* v_s_1717_, lean_object* v_pos_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v_s_1717_, v_pos_1718_);
lean_dec_ref(v_s_1717_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_number(lean_object* v_v_1720_){
_start:
{
lean_object* v_marker_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1736_; 
v_marker_1721_ = lean_ctor_get(v_v_1720_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_v_1720_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; lean_object* v_unused_1738_; 
v_unused_1737_ = lean_ctor_get(v_v_1720_, 2);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_v_1720_, 0);
lean_dec(v_unused_1738_);
v___x_1723_ = v_v_1720_;
v_isShared_1724_ = v_isSharedCheck_1736_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_marker_1721_);
lean_dec(v_v_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1736_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1725_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_1721_);
lean_dec(v_marker_1721_);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = lean_string_utf8_byte_size(v___x_1725_);
lean_inc_ref(v___x_1725_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 2, v___x_1727_);
lean_ctor_set(v___x_1723_, 1, v___x_1726_);
lean_ctor_set(v___x_1723_, 0, v___x_1725_);
v___x_1729_ = v___x_1723_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1730_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v___x_1729_, v___x_1726_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = lean_string_utf8_extract_fast(v___x_1725_, v___x_1726_, v___x_1730_);
lean_dec(v___x_1730_);
lean_dec_ref(v___x_1725_);
v___x_1732_ = lean_string_utf8_byte_size(v___x_1731_);
v___x_1733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1726_);
lean_ctor_set(v___x_1733_, 2, v___x_1732_);
v___x_1734_ = l_String_Slice_toNat_x3f(v___x_1733_);
lean_dec_ref_known(v___x_1733_, 3);
return v___x_1734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_of(lean_object* v_stx_1739_){
_start:
{
lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__2));
lean_inc(v_stx_1739_);
v___x_1741_ = l_Lean_Syntax_isOfKind(v_stx_1739_, v___x_1740_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
lean_dec(v_stx_1739_);
v___x_1742_ = lean_box(0);
return v___x_1742_;
}
else
{
lean_object* v___x_1743_; lean_object* v_m_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1743_ = lean_unsigned_to_nat(0u);
v_m_1744_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_1743_);
v___x_1745_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__4));
lean_inc(v_m_1744_);
v___x_1746_ = l_Lean_Syntax_isOfKind(v_m_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
lean_dec(v_m_1744_);
lean_dec(v_stx_1739_);
v___x_1747_ = lean_box(0);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1748_ = l_Lean_TSyntax_getVersoDelimiter(v_m_1744_);
v___x_1749_ = lean_string_utf8_byte_size(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1743_);
lean_ctor_set(v___x_1750_, 2, v___x_1749_);
v___x_1751_ = l_String_Slice_Pos_get_x3f(v___x_1750_, v___x_1743_);
lean_dec_ref_known(v___x_1750_, 3);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v___x_1752_; 
lean_dec(v_m_1744_);
lean_dec(v_stx_1739_);
v___x_1752_ = lean_box(0);
return v___x_1752_;
}
else
{
lean_object* v_val_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1772_; 
v_val_1753_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1755_ = v___x_1751_;
v_isShared_1756_ = v_isSharedCheck_1772_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_val_1753_);
lean_dec(v___x_1751_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1772_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
uint32_t v___x_1757_; uint32_t v___x_1758_; uint8_t v___x_1759_; 
v___x_1757_ = 48;
v___x_1758_ = lean_unbox_uint32(v_val_1753_);
v___x_1759_ = lean_uint32_dec_le(v___x_1757_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_del_object(v___x_1755_);
lean_dec(v_val_1753_);
lean_dec(v_m_1744_);
lean_dec(v_stx_1739_);
v___x_1760_ = lean_box(0);
return v___x_1760_;
}
else
{
uint32_t v___x_1761_; uint32_t v___x_1762_; uint8_t v___x_1763_; 
v___x_1761_ = 57;
v___x_1762_ = lean_unbox_uint32(v_val_1753_);
lean_dec(v_val_1753_);
v___x_1763_ = lean_uint32_dec_le(v___x_1762_, v___x_1761_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_del_object(v___x_1755_);
lean_dec(v_m_1744_);
lean_dec(v_stx_1739_);
v___x_1764_ = lean_box(0);
return v___x_1764_;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_bs_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = l_Lean_Syntax_getArg(v_stx_1739_, v___x_1765_);
v_bs_1767_ = l_Lean_Syntax_getArgs(v___x_1766_);
lean_dec(v___x_1766_);
v___x_1768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1768_, 0, v_stx_1739_);
lean_ctor_set(v___x_1768_, 1, v_m_1744_);
lean_ctor_set(v___x_1768_, 2, v_bs_1767_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1768_);
v___x_1770_ = v___x_1755_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescItemView_of(lean_object* v_stx_1780_){
_start:
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_Doc_DescItemView_of___closed__1));
lean_inc(v_stx_1780_);
v___x_1782_ = l_Lean_Syntax_isOfKind(v_stx_1780_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; 
lean_dec(v_stx_1780_);
v___x_1783_ = lean_box(0);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v_marker_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v_desc_1790_; lean_object* v_term_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1784_ = lean_unsigned_to_nat(0u);
v_marker_1785_ = l_Lean_Syntax_getArg(v_stx_1780_, v___x_1784_);
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = l_Lean_Syntax_getArg(v_stx_1780_, v___x_1786_);
v___x_1788_ = lean_unsigned_to_nat(2u);
v___x_1789_ = l_Lean_Syntax_getArg(v_stx_1780_, v___x_1788_);
v_desc_1790_ = l_Lean_Syntax_getArgs(v___x_1789_);
lean_dec(v___x_1789_);
v_term_1791_ = l_Lean_Syntax_getArgs(v___x_1787_);
lean_dec(v___x_1787_);
v___x_1792_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1792_, 0, v_stx_1780_);
lean_ctor_set(v___x_1792_, 1, v_marker_1785_);
lean_ctor_set(v___x_1792_, 2, v_term_1791_);
lean_ctor_set(v___x_1792_, 3, v_desc_1790_);
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ParaView_of(lean_object* v_stx_1809_){
_start:
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_Doc_ParaView_of___closed__2));
lean_inc(v_stx_1809_);
v___x_1811_ = l_Lean_Syntax_isOfKind(v_stx_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; 
lean_dec(v_stx_1809_);
v___x_1812_ = lean_box(0);
return v___x_1812_;
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_inl_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = l_Lean_Syntax_getArg(v_stx_1809_, v___x_1813_);
v_inl_1815_ = l_Lean_Syntax_getArgs(v___x_1814_);
lean_dec(v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v_stx_1809_);
lean_ctor_set(v___x_1816_, 1, v_inl_1815_);
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(size_t v_sz_1818_, size_t v_i_1819_, lean_object* v_bs_1820_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_usize_dec_lt(v_i_1819_, v_sz_1818_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_bs_1820_);
return v___x_1822_;
}
else
{
lean_object* v_v_1823_; lean_object* v___x_1824_; 
v_v_1823_ = lean_array_uget_borrowed(v_bs_1820_, v_i_1819_);
lean_inc(v_v_1823_);
v___x_1824_ = l_Lean_Doc_UnorderedListItemView_of(v_v_1823_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v___x_1825_; 
lean_dec_ref(v_bs_1820_);
v___x_1825_ = lean_box(0);
return v___x_1825_;
}
else
{
lean_object* v_val_1826_; lean_object* v___x_1827_; lean_object* v_bs_x27_1828_; size_t v___x_1829_; size_t v___x_1830_; lean_object* v___x_1831_; 
v_val_1826_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_val_1826_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1827_ = lean_unsigned_to_nat(0u);
v_bs_x27_1828_ = lean_array_uset(v_bs_1820_, v_i_1819_, v___x_1827_);
v___x_1829_ = ((size_t)1ULL);
v___x_1830_ = lean_usize_add(v_i_1819_, v___x_1829_);
v___x_1831_ = lean_array_uset(v_bs_x27_1828_, v_i_1819_, v_val_1826_);
v_i_1819_ = v___x_1830_;
v_bs_1820_ = v___x_1831_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0___boxed(lean_object* v_sz_1833_, lean_object* v_i_1834_, lean_object* v_bs_1835_){
_start:
{
size_t v_sz_boxed_1836_; size_t v_i_boxed_1837_; lean_object* v_res_1838_; 
v_sz_boxed_1836_ = lean_unbox_usize(v_sz_1833_);
lean_dec(v_sz_1833_);
v_i_boxed_1837_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_res_1838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_boxed_1836_, v_i_boxed_1837_, v_bs_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListView_of(lean_object* v_stx_1846_){
_start:
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Lean_Doc_UnorderedListView_of___closed__1));
lean_inc(v_stx_1846_);
v___x_1848_ = l_Lean_Syntax_isOfKind(v_stx_1846_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; 
lean_dec(v_stx_1846_);
v___x_1849_ = lean_box(0);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v_items_1852_; size_t v_sz_1853_; size_t v___x_1854_; lean_object* v___x_1855_; 
v___x_1850_ = lean_unsigned_to_nat(0u);
v___x_1851_ = l_Lean_Syntax_getArg(v_stx_1846_, v___x_1850_);
v_items_1852_ = l_Lean_Syntax_getArgs(v___x_1851_);
lean_dec(v___x_1851_);
v_sz_1853_ = lean_array_size(v_items_1852_);
v___x_1854_ = ((size_t)0ULL);
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_1853_, v___x_1854_, v_items_1852_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v___x_1856_; 
lean_dec(v_stx_1846_);
v___x_1856_ = lean_box(0);
return v___x_1856_;
}
else
{
lean_object* v_val_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1865_; 
v_val_1857_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1859_ = v___x_1855_;
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_val_1857_);
lean_dec(v___x_1855_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v_stx_1846_);
lean_ctor_set(v___x_1861_, 1, v_val_1857_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(size_t v_sz_1866_, size_t v_i_1867_, lean_object* v_bs_1868_){
_start:
{
uint8_t v___x_1869_; 
v___x_1869_ = lean_usize_dec_lt(v_i_1867_, v_sz_1866_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_bs_1868_);
return v___x_1870_;
}
else
{
lean_object* v_v_1871_; lean_object* v___x_1872_; 
v_v_1871_ = lean_array_uget_borrowed(v_bs_1868_, v_i_1867_);
lean_inc(v_v_1871_);
v___x_1872_ = l_Lean_Doc_OrderedListItemView_of(v_v_1871_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v___x_1873_; 
lean_dec_ref(v_bs_1868_);
v___x_1873_ = lean_box(0);
return v___x_1873_;
}
else
{
lean_object* v_val_1874_; lean_object* v___x_1875_; lean_object* v_bs_x27_1876_; size_t v___x_1877_; size_t v___x_1878_; lean_object* v___x_1879_; 
v_val_1874_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1875_ = lean_unsigned_to_nat(0u);
v_bs_x27_1876_ = lean_array_uset(v_bs_1868_, v_i_1867_, v___x_1875_);
v___x_1877_ = ((size_t)1ULL);
v___x_1878_ = lean_usize_add(v_i_1867_, v___x_1877_);
v___x_1879_ = lean_array_uset(v_bs_x27_1876_, v_i_1867_, v_val_1874_);
v_i_1867_ = v___x_1878_;
v_bs_1868_ = v___x_1879_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0___boxed(lean_object* v_sz_1881_, lean_object* v_i_1882_, lean_object* v_bs_1883_){
_start:
{
size_t v_sz_boxed_1884_; size_t v_i_boxed_1885_; lean_object* v_res_1886_; 
v_sz_boxed_1884_ = lean_unbox_usize(v_sz_1881_);
lean_dec(v_sz_1881_);
v_i_boxed_1885_ = lean_unbox_usize(v_i_1882_);
lean_dec(v_i_1882_);
v_res_1886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_boxed_1884_, v_i_boxed_1885_, v_bs_1883_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListView_of(lean_object* v_stx_1894_){
_start:
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = ((lean_object*)(l_Lean_Doc_OrderedListView_of___closed__1));
lean_inc(v_stx_1894_);
v___x_1896_ = l_Lean_Syntax_isOfKind(v_stx_1894_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; 
lean_dec(v_stx_1894_);
v___x_1897_ = lean_box(0);
return v___x_1897_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v_items_1900_; size_t v_sz_1901_; size_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1898_ = lean_unsigned_to_nat(0u);
v___x_1899_ = l_Lean_Syntax_getArg(v_stx_1894_, v___x_1898_);
v_items_1900_ = l_Lean_Syntax_getArgs(v___x_1899_);
lean_dec(v___x_1899_);
v_sz_1901_ = lean_array_size(v_items_1900_);
v___x_1902_ = ((size_t)0ULL);
v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_1901_, v___x_1902_, v_items_1900_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v___x_1904_; 
lean_dec(v_stx_1894_);
v___x_1904_ = lean_box(0);
return v___x_1904_;
}
else
{
lean_object* v_val_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1922_; 
v_val_1905_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1907_ = v___x_1903_;
v_isShared_1908_ = v_isSharedCheck_1922_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_val_1905_);
lean_dec(v___x_1903_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1922_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___y_1910_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1917_ = lean_array_get_size(v_val_1905_);
v___x_1918_ = lean_nat_dec_lt(v___x_1898_, v___x_1917_);
if (v___x_1918_ == 0)
{
goto v___jp_1915_;
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_array_fget_borrowed(v_val_1905_, v___x_1898_);
lean_inc(v___x_1919_);
v___x_1920_ = l_Lean_Doc_OrderedListItemView_number(v___x_1919_);
if (lean_obj_tag(v___x_1920_) == 0)
{
goto v___jp_1915_;
}
else
{
lean_object* v_val_1921_; 
v_val_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_val_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___y_1910_ = v_val_1921_;
goto v___jp_1909_;
}
}
v___jp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1911_, 0, v_stx_1894_);
lean_ctor_set(v___x_1911_, 1, v___y_1910_);
lean_ctor_set(v___x_1911_, 2, v_val_1905_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1911_);
v___x_1913_ = v___x_1907_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
v___jp_1915_:
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_unsigned_to_nat(1u);
v___y_1910_ = v___x_1916_;
goto v___jp_1909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(size_t v_sz_1923_, size_t v_i_1924_, lean_object* v_bs_1925_){
_start:
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_usize_dec_lt(v_i_1924_, v_sz_1923_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_bs_1925_);
return v___x_1927_;
}
else
{
lean_object* v_v_1928_; lean_object* v___x_1929_; 
v_v_1928_ = lean_array_uget_borrowed(v_bs_1925_, v_i_1924_);
lean_inc(v_v_1928_);
v___x_1929_ = l_Lean_Doc_DescItemView_of(v_v_1928_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1930_; 
lean_dec_ref(v_bs_1925_);
v___x_1930_ = lean_box(0);
return v___x_1930_;
}
else
{
lean_object* v_val_1931_; lean_object* v___x_1932_; lean_object* v_bs_x27_1933_; size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v_val_1931_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_val_1931_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1932_ = lean_unsigned_to_nat(0u);
v_bs_x27_1933_ = lean_array_uset(v_bs_1925_, v_i_1924_, v___x_1932_);
v___x_1934_ = ((size_t)1ULL);
v___x_1935_ = lean_usize_add(v_i_1924_, v___x_1934_);
v___x_1936_ = lean_array_uset(v_bs_x27_1933_, v_i_1924_, v_val_1931_);
v_i_1924_ = v___x_1935_;
v_bs_1925_ = v___x_1936_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0___boxed(lean_object* v_sz_1938_, lean_object* v_i_1939_, lean_object* v_bs_1940_){
_start:
{
size_t v_sz_boxed_1941_; size_t v_i_boxed_1942_; lean_object* v_res_1943_; 
v_sz_boxed_1941_ = lean_unbox_usize(v_sz_1938_);
lean_dec(v_sz_1938_);
v_i_boxed_1942_ = lean_unbox_usize(v_i_1939_);
lean_dec(v_i_1939_);
v_res_1943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_boxed_1941_, v_i_boxed_1942_, v_bs_1940_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescListView_of(lean_object* v_stx_1951_){
_start:
{
lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = ((lean_object*)(l_Lean_Doc_DescListView_of___closed__1));
lean_inc(v_stx_1951_);
v___x_1953_ = l_Lean_Syntax_isOfKind(v_stx_1951_, v___x_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
lean_dec(v_stx_1951_);
v___x_1954_ = lean_box(0);
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v_items_1957_; size_t v_sz_1958_; size_t v___x_1959_; lean_object* v___x_1960_; 
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = l_Lean_Syntax_getArg(v_stx_1951_, v___x_1955_);
v_items_1957_ = l_Lean_Syntax_getArgs(v___x_1956_);
lean_dec(v___x_1956_);
v_sz_1958_ = lean_array_size(v_items_1957_);
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_1958_, v___x_1959_, v_items_1957_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v___x_1961_; 
lean_dec(v_stx_1951_);
v___x_1961_ = lean_box(0);
return v___x_1961_;
}
else
{
lean_object* v_val_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1970_; 
v_val_1962_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1964_ = v___x_1960_;
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_val_1962_);
lean_dec(v___x_1960_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_stx_1951_);
lean_ctor_set(v___x_1966_, 1, v_val_1962_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1966_);
v___x_1968_ = v___x_1964_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockquoteView_of(lean_object* v_stx_1978_){
_start:
{
lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = ((lean_object*)(l_Lean_Doc_BlockquoteView_of___closed__1));
lean_inc(v_stx_1978_);
v___x_1980_ = l_Lean_Syntax_isOfKind(v_stx_1978_, v___x_1979_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; 
lean_dec(v_stx_1978_);
v___x_1981_ = lean_box(0);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; lean_object* v_gt_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v_bs_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1982_ = lean_unsigned_to_nat(0u);
v_gt_1983_ = l_Lean_Syntax_getArg(v_stx_1978_, v___x_1982_);
v___x_1984_ = lean_unsigned_to_nat(1u);
v___x_1985_ = l_Lean_Syntax_getArg(v_stx_1978_, v___x_1984_);
v_bs_1986_ = l_Lean_Syntax_getArgs(v___x_1985_);
lean_dec(v___x_1985_);
v___x_1987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1987_, 0, v_stx_1978_);
lean_ctor_set(v___x_1987_, 1, v_gt_1983_);
lean_ctor_set(v___x_1987_, 2, v_bs_1986_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
return v___x_1988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object* v_v_1989_){
_start:
{
lean_object* v_content_1990_; lean_object* v___x_1991_; 
v_content_1990_ = lean_ctor_get(v_v_1989_, 4);
v___x_1991_ = l_Lean_TSyntax_getVersoCodeBlock(v_content_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock___boxed(lean_object* v_v_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_v_1992_);
lean_dec_ref(v_v_1992_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_of(lean_object* v_stx_2013_){
_start:
{
lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__1));
lean_inc(v_stx_2013_);
v___x_2015_ = l_Lean_Syntax_isOfKind(v_stx_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
lean_dec(v_stx_2013_);
v___x_2016_ = lean_box(0);
return v___x_2016_;
}
else
{
lean_object* v___x_2017_; lean_object* v_openFence_2018_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v_name_2034_; lean_object* v_args_2035_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2017_ = lean_unsigned_to_nat(0u);
v_openFence_2018_ = l_Lean_Syntax_getArg(v_stx_2013_, v___x_2017_);
v___x_2050_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__5));
lean_inc(v_openFence_2018_);
v___x_2051_ = l_Lean_Syntax_isOfKind(v_openFence_2018_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
lean_dec(v_openFence_2018_);
lean_dec(v_stx_2013_);
v___x_2052_ = lean_box(0);
return v___x_2052_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2053_ = lean_unsigned_to_nat(1u);
v___x_2054_ = l_Lean_Syntax_getArg(v_stx_2013_, v___x_2053_);
v___x_2055_ = l_Lean_Syntax_isNone(v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2054_);
v___x_2057_ = l_Lean_Syntax_matchesNull(v___x_2054_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; 
lean_dec(v___x_2054_);
lean_dec(v_openFence_2018_);
lean_dec(v_stx_2013_);
v___x_2058_ = lean_box(0);
return v___x_2058_;
}
else
{
lean_object* v_name_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v_name_2059_ = l_Lean_Syntax_getArg(v___x_2054_, v___x_2017_);
v___x_2060_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2059_);
v___x_2061_ = l_Lean_Syntax_isOfKind(v_name_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
lean_dec(v_name_2059_);
lean_dec(v___x_2054_);
lean_dec(v_openFence_2018_);
lean_dec(v_stx_2013_);
v___x_2062_ = lean_box(0);
return v___x_2062_;
}
else
{
lean_object* v___x_2063_; lean_object* v_args_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2063_ = l_Lean_Syntax_getArg(v___x_2054_, v___x_2053_);
lean_dec(v___x_2054_);
v_args_2064_ = l_Lean_Syntax_getArgs(v___x_2063_);
lean_dec(v___x_2063_);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_name_2059_);
v___x_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2066_, 0, v_args_2064_);
v_name_2034_ = v___x_2065_;
v_args_2035_ = v___x_2066_;
goto v___jp_2033_;
}
}
}
else
{
lean_object* v___x_2067_; 
lean_dec(v___x_2054_);
v___x_2067_ = lean_box(0);
v_name_2034_ = v___x_2067_;
v_args_2035_ = v___x_2067_;
goto v___jp_2033_;
}
}
v___jp_2019_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2024_, 0, v_stx_2013_);
lean_ctor_set(v___x_2024_, 1, v_openFence_2018_);
lean_ctor_set(v___x_2024_, 2, v___y_2021_);
lean_ctor_set(v___x_2024_, 3, v___y_2023_);
lean_ctor_set(v___x_2024_, 4, v___y_2022_);
lean_ctor_set(v___x_2024_, 5, v___y_2020_);
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
v___jp_2026_:
{
if (lean_obj_tag(v___y_2029_) == 0)
{
lean_object* v___x_2031_; 
v___x_2031_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0));
v___y_2020_ = v___y_2027_;
v___y_2021_ = v___y_2028_;
v___y_2022_ = v___y_2030_;
v___y_2023_ = v___x_2031_;
goto v___jp_2019_;
}
else
{
lean_object* v_val_2032_; 
v_val_2032_ = lean_ctor_get(v___y_2029_, 0);
lean_inc(v_val_2032_);
lean_dec_ref_known(v___y_2029_, 1);
v___y_2020_ = v___y_2027_;
v___y_2021_ = v___y_2028_;
v___y_2022_ = v___y_2030_;
v___y_2023_ = v_val_2032_;
goto v___jp_2019_;
}
}
v___jp_2033_:
{
lean_object* v___x_2036_; lean_object* v_s_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2036_ = lean_unsigned_to_nat(2u);
v_s_2037_ = l_Lean_Syntax_getArg(v_stx_2013_, v___x_2036_);
v___x_2038_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__3));
lean_inc(v_s_2037_);
v___x_2039_ = l_Lean_Syntax_isOfKind(v_s_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_dec(v_s_2037_);
lean_dec(v_args_2035_);
lean_dec(v_name_2034_);
lean_dec(v_openFence_2018_);
lean_dec(v_stx_2013_);
v___x_2040_ = lean_box(0);
return v___x_2040_;
}
else
{
lean_object* v___x_2041_; lean_object* v_closeFence_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2041_ = lean_unsigned_to_nat(3u);
v_closeFence_2042_ = l_Lean_Syntax_getArg(v_stx_2013_, v___x_2041_);
v___x_2043_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__5));
lean_inc(v_closeFence_2042_);
v___x_2044_ = l_Lean_Syntax_isOfKind(v_closeFence_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; 
lean_dec(v_closeFence_2042_);
lean_dec(v_s_2037_);
lean_dec(v_args_2035_);
lean_dec(v_name_2034_);
lean_dec(v_openFence_2018_);
lean_dec(v_stx_2013_);
v___x_2045_ = lean_box(0);
return v___x_2045_;
}
else
{
uint8_t v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = 0;
v___x_2047_ = l_Lean_Syntax_getPos_x3f(v_s_2037_, v___x_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v_closeFence_2042_);
v___x_2049_ = l_Lean_Syntax_setInfo(v___x_2048_, v_s_2037_);
v___y_2027_ = v_closeFence_2042_;
v___y_2028_ = v_name_2034_;
v___y_2029_ = v_args_2035_;
v___y_2030_ = v___x_2049_;
goto v___jp_2026_;
}
else
{
lean_dec_ref_known(v___x_2047_, 1);
v___y_2027_ = v_closeFence_2042_;
v___y_2028_ = v_name_2034_;
v___y_2029_ = v_args_2035_;
v___y_2030_ = v_s_2037_;
goto v___jp_2026_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DirectiveView_of(lean_object* v_stx_2081_){
_start:
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = ((lean_object*)(l_Lean_Doc_DirectiveView_of___closed__1));
lean_inc(v_stx_2081_);
v___x_2083_ = l_Lean_Syntax_isOfKind(v_stx_2081_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
lean_dec(v_stx_2081_);
v___x_2084_ = lean_box(0);
return v___x_2084_;
}
else
{
lean_object* v___x_2085_; lean_object* v_opener_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2085_ = lean_unsigned_to_nat(0u);
v_opener_2086_ = l_Lean_Syntax_getArg(v_stx_2081_, v___x_2085_);
v___x_2087_ = ((lean_object*)(l_Lean_Doc_DirectiveView_of___closed__3));
lean_inc(v_opener_2086_);
v___x_2088_ = l_Lean_Syntax_isOfKind(v_opener_2086_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_dec(v_opener_2086_);
lean_dec(v_stx_2081_);
v___x_2089_ = lean_box(0);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; lean_object* v_name_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2090_ = lean_unsigned_to_nat(1u);
v_name_2091_ = l_Lean_Syntax_getArg(v_stx_2081_, v___x_2090_);
v___x_2092_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2091_);
v___x_2093_ = l_Lean_Syntax_isOfKind(v_name_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
lean_dec(v_name_2091_);
lean_dec(v_opener_2086_);
lean_dec(v_stx_2081_);
v___x_2094_ = lean_box(0);
return v___x_2094_;
}
else
{
lean_object* v___x_2095_; lean_object* v_closer_2096_; uint8_t v___x_2097_; 
v___x_2095_ = lean_unsigned_to_nat(4u);
v_closer_2096_ = l_Lean_Syntax_getArg(v_stx_2081_, v___x_2095_);
lean_inc(v_closer_2096_);
v___x_2097_ = l_Lean_Syntax_isOfKind(v_closer_2096_, v___x_2087_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
lean_dec(v_closer_2096_);
lean_dec(v_name_2091_);
lean_dec(v_opener_2086_);
lean_dec(v_stx_2081_);
v___x_2098_ = lean_box(0);
return v___x_2098_;
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v_bs_2103_; lean_object* v_args_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2099_ = lean_unsigned_to_nat(2u);
v___x_2100_ = l_Lean_Syntax_getArg(v_stx_2081_, v___x_2099_);
v___x_2101_ = lean_unsigned_to_nat(3u);
v___x_2102_ = l_Lean_Syntax_getArg(v_stx_2081_, v___x_2101_);
v_bs_2103_ = l_Lean_Syntax_getArgs(v___x_2102_);
lean_dec(v___x_2102_);
v_args_2104_ = l_Lean_Syntax_getArgs(v___x_2100_);
lean_dec(v___x_2100_);
v___x_2105_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2105_, 0, v_stx_2081_);
lean_ctor_set(v___x_2105_, 1, v_opener_2086_);
lean_ctor_set(v___x_2105_, 2, v_name_2091_);
lean_ctor_set(v___x_2105_, 3, v_args_2104_);
lean_ctor_set(v___x_2105_, 4, v_bs_2103_);
lean_ctor_set(v___x_2105_, 5, v_closer_2096_);
v___x_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CommandView_of(lean_object* v_stx_2114_){
_start:
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_Doc_CommandView_of___closed__1));
lean_inc(v_stx_2114_);
v___x_2116_ = l_Lean_Syntax_isOfKind(v_stx_2114_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_dec(v_stx_2114_);
v___x_2117_ = lean_box(0);
return v___x_2117_;
}
else
{
lean_object* v___x_2118_; lean_object* v_name_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2118_ = lean_unsigned_to_nat(1u);
v_name_2119_ = l_Lean_Syntax_getArg(v_stx_2114_, v___x_2118_);
v___x_2120_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2119_);
v___x_2121_ = l_Lean_Syntax_isOfKind(v_name_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; 
lean_dec(v_name_2119_);
lean_dec(v_stx_2114_);
v___x_2122_ = lean_box(0);
return v___x_2122_;
}
else
{
lean_object* v___x_2123_; lean_object* v_braceOpen_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v_braceClose_2128_; lean_object* v_args_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2123_ = lean_unsigned_to_nat(0u);
v_braceOpen_2124_ = l_Lean_Syntax_getArg(v_stx_2114_, v___x_2123_);
v___x_2125_ = lean_unsigned_to_nat(2u);
v___x_2126_ = l_Lean_Syntax_getArg(v_stx_2114_, v___x_2125_);
v___x_2127_ = lean_unsigned_to_nat(3u);
v_braceClose_2128_ = l_Lean_Syntax_getArg(v_stx_2114_, v___x_2127_);
v_args_2129_ = l_Lean_Syntax_getArgs(v___x_2126_);
lean_dec(v___x_2126_);
v___x_2130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2130_, 0, v_stx_2114_);
lean_ctor_set(v___x_2130_, 1, v_braceOpen_2124_);
lean_ctor_set(v___x_2130_, 2, v_name_2119_);
lean_ctor_set(v___x_2130_, 3, v_args_2129_);
lean_ctor_set(v___x_2130_, 4, v_braceClose_2128_);
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_HeaderView_of(lean_object* v_stx_2145_){
_start:
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = ((lean_object*)(l_Lean_Doc_HeaderView_of___closed__1));
lean_inc(v_stx_2145_);
v___x_2147_ = l_Lean_Syntax_isOfKind(v_stx_2145_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; 
lean_dec(v_stx_2145_);
v___x_2148_ = lean_box(0);
return v___x_2148_;
}
else
{
lean_object* v___x_2149_; lean_object* v_marker_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2149_ = lean_unsigned_to_nat(0u);
v_marker_2150_ = l_Lean_Syntax_getArg(v_stx_2145_, v___x_2149_);
v___x_2151_ = ((lean_object*)(l_Lean_Doc_HeaderView_of___closed__3));
lean_inc(v_marker_2150_);
v___x_2152_ = l_Lean_Syntax_isOfKind(v_marker_2150_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
lean_dec(v_marker_2150_);
lean_dec(v_stx_2145_);
v___x_2153_ = lean_box(0);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v_content_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2154_ = lean_unsigned_to_nat(1u);
v___x_2155_ = l_Lean_Syntax_getArg(v_stx_2145_, v___x_2154_);
v_content_2156_ = l_Lean_Syntax_getArgs(v___x_2155_);
lean_dec(v___x_2155_);
v___x_2157_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_2150_);
v___x_2158_ = lean_string_length(v___x_2157_);
lean_dec_ref(v___x_2157_);
v___x_2159_ = lean_nat_sub(v___x_2158_, v___x_2154_);
v___x_2160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2160_, 0, v_stx_2145_);
lean_ctor_set(v___x_2160_, 1, v_marker_2150_);
lean_ctor_set(v___x_2160_, 2, v___x_2159_);
lean_ctor_set(v___x_2160_, 3, v_content_2156_);
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName(lean_object* v_v_2162_){
_start:
{
lean_object* v_name_2163_; lean_object* v___x_2164_; 
v_name_2163_ = lean_ctor_get(v_v_2162_, 2);
v___x_2164_ = l_Lean_TSyntax_getVersoRefName(v_name_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName___boxed(lean_object* v_v_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Doc_LinkRefView_getName(v_v_2165_);
lean_dec_ref(v_v_2165_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object* v_v_2167_){
_start:
{
lean_object* v_url_2168_; lean_object* v___x_2169_; 
v_url_2168_ = lean_ctor_get(v_v_2167_, 4);
v___x_2169_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_url_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl___boxed(lean_object* v_v_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_Doc_LinkRefView_getUrl(v_v_2170_);
lean_dec_ref(v_v_2170_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_of(lean_object* v_stx_2185_){
_start:
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__1));
lean_inc(v_stx_2185_);
v___x_2187_ = l_Lean_Syntax_isOfKind(v_stx_2185_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
lean_dec(v_stx_2185_);
v___x_2188_ = lean_box(0);
return v___x_2188_;
}
else
{
lean_object* v___x_2189_; lean_object* v_name_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2189_ = lean_unsigned_to_nat(1u);
v_name_2190_ = l_Lean_Syntax_getArg(v_stx_2185_, v___x_2189_);
v___x_2191_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_2190_);
v___x_2192_ = l_Lean_Syntax_isOfKind(v_name_2190_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; 
lean_dec(v_name_2190_);
lean_dec(v_stx_2185_);
v___x_2193_ = lean_box(0);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; lean_object* v_url_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2194_ = lean_unsigned_to_nat(3u);
v_url_2195_ = l_Lean_Syntax_getArg(v_stx_2185_, v___x_2194_);
v___x_2196_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__3));
lean_inc(v_url_2195_);
v___x_2197_ = l_Lean_Syntax_isOfKind(v_url_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; 
lean_dec(v_url_2195_);
lean_dec(v_name_2190_);
lean_dec(v_stx_2185_);
v___x_2198_ = lean_box(0);
return v___x_2198_;
}
else
{
lean_object* v___x_2199_; lean_object* v_opener_2200_; lean_object* v___x_2201_; lean_object* v_closer_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2199_ = lean_unsigned_to_nat(0u);
v_opener_2200_ = l_Lean_Syntax_getArg(v_stx_2185_, v___x_2199_);
v___x_2201_ = lean_unsigned_to_nat(2u);
v_closer_2202_ = l_Lean_Syntax_getArg(v_stx_2185_, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2203_, 0, v_stx_2185_);
lean_ctor_set(v___x_2203_, 1, v_opener_2200_);
lean_ctor_set(v___x_2203_, 2, v_name_2190_);
lean_ctor_set(v___x_2203_, 3, v_closer_2202_);
lean_ctor_set(v___x_2203_, 4, v_url_2195_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object* v_v_2205_){
_start:
{
lean_object* v_name_2206_; lean_object* v___x_2207_; 
v_name_2206_ = lean_ctor_get(v_v_2205_, 2);
v___x_2207_ = l_Lean_TSyntax_getVersoRefName(v_name_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName___boxed(lean_object* v_v_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_Doc_FootnoteRefView_getName(v_v_2208_);
lean_dec_ref(v_v_2208_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_of(lean_object* v_stx_2217_){
_start:
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = ((lean_object*)(l_Lean_Doc_FootnoteRefView_of___closed__1));
lean_inc(v_stx_2217_);
v___x_2219_ = l_Lean_Syntax_isOfKind(v_stx_2217_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; 
lean_dec(v_stx_2217_);
v___x_2220_ = lean_box(0);
return v___x_2220_;
}
else
{
lean_object* v___x_2221_; lean_object* v_name_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2221_ = lean_unsigned_to_nat(1u);
v_name_2222_ = l_Lean_Syntax_getArg(v_stx_2217_, v___x_2221_);
v___x_2223_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_2222_);
v___x_2224_ = l_Lean_Syntax_isOfKind(v_name_2222_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; 
lean_dec(v_name_2222_);
lean_dec(v_stx_2217_);
v___x_2225_ = lean_box(0);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; lean_object* v_opener_2227_; lean_object* v___x_2228_; lean_object* v_closer_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_content_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2226_ = lean_unsigned_to_nat(0u);
v_opener_2227_ = l_Lean_Syntax_getArg(v_stx_2217_, v___x_2226_);
v___x_2228_ = lean_unsigned_to_nat(2u);
v_closer_2229_ = l_Lean_Syntax_getArg(v_stx_2217_, v___x_2228_);
v___x_2230_ = lean_unsigned_to_nat(3u);
v___x_2231_ = l_Lean_Syntax_getArg(v_stx_2217_, v___x_2230_);
v_content_2232_ = l_Lean_Syntax_getArgs(v___x_2231_);
lean_dec(v___x_2231_);
v___x_2233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2233_, 0, v_stx_2217_);
lean_ctor_set(v___x_2233_, 1, v_opener_2227_);
lean_ctor_set(v___x_2233_, 2, v_name_2222_);
lean_ctor_set(v___x_2233_, 3, v_closer_2229_);
lean_ctor_set(v___x_2233_, 4, v_content_2232_);
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(size_t v_sz_2235_, size_t v_i_2236_, lean_object* v_bs_2237_){
_start:
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_usize_dec_lt(v_i_2236_, v_sz_2235_);
if (v___x_2238_ == 0)
{
return v_bs_2237_;
}
else
{
lean_object* v_v_2239_; lean_object* v___x_2240_; lean_object* v_bs_x27_2241_; size_t v___x_2242_; size_t v___x_2243_; lean_object* v___x_2244_; 
v_v_2239_ = lean_array_uget(v_bs_2237_, v_i_2236_);
v___x_2240_ = lean_unsigned_to_nat(0u);
v_bs_x27_2241_ = lean_array_uset(v_bs_2237_, v_i_2236_, v___x_2240_);
v___x_2242_ = ((size_t)1ULL);
v___x_2243_ = lean_usize_add(v_i_2236_, v___x_2242_);
v___x_2244_ = lean_array_uset(v_bs_x27_2241_, v_i_2236_, v_v_2239_);
v_i_2236_ = v___x_2243_;
v_bs_2237_ = v___x_2244_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0___boxed(lean_object* v_sz_2246_, lean_object* v_i_2247_, lean_object* v_bs_2248_){
_start:
{
size_t v_sz_boxed_2249_; size_t v_i_boxed_2250_; lean_object* v_res_2251_; 
v_sz_boxed_2249_ = lean_unbox_usize(v_sz_2246_);
lean_dec(v_sz_2246_);
v_i_boxed_2250_ = lean_unbox_usize(v_i_2247_);
lean_dec(v_i_2247_);
v_res_2251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_boxed_2249_, v_i_boxed_2250_, v_bs_2248_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields(lean_object* v_v_2252_){
_start:
{
lean_object* v_contents_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; size_t v_sz_2257_; size_t v___x_2258_; lean_object* v___x_2259_; 
v_contents_2253_ = lean_ctor_get(v_v_2252_, 2);
v___x_2254_ = lean_unsigned_to_nat(0u);
v___x_2255_ = l_Lean_Syntax_getArg(v_contents_2253_, v___x_2254_);
v___x_2256_ = l_Lean_Syntax_getSepArgs(v___x_2255_);
lean_dec(v___x_2255_);
v_sz_2257_ = lean_array_size(v___x_2256_);
v___x_2258_ = ((size_t)0ULL);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_2257_, v___x_2258_, v___x_2256_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields___boxed(lean_object* v_v_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Doc_MetadataView_fields(v_v_2260_);
lean_dec_ref(v_v_2260_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_of(lean_object* v_stx_2276_){
_start:
{
lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = ((lean_object*)(l_Lean_Doc_MetadataView_of___closed__1));
lean_inc(v_stx_2276_);
v___x_2278_ = l_Lean_Syntax_isOfKind(v_stx_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; 
lean_dec(v_stx_2276_);
v___x_2279_ = lean_box(0);
return v___x_2279_;
}
else
{
lean_object* v___x_2280_; lean_object* v_contents_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2280_ = lean_unsigned_to_nat(1u);
v_contents_2281_ = l_Lean_Syntax_getArg(v_stx_2276_, v___x_2280_);
v___x_2282_ = ((lean_object*)(l_Lean_Doc_MetadataView_of___closed__4));
lean_inc(v_contents_2281_);
v___x_2283_ = l_Lean_Syntax_isOfKind(v_contents_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
lean_dec(v_contents_2281_);
lean_dec(v_stx_2276_);
v___x_2284_ = lean_box(0);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; lean_object* v_opener_2286_; lean_object* v___x_2287_; lean_object* v_closer_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2285_ = lean_unsigned_to_nat(0u);
v_opener_2286_ = l_Lean_Syntax_getArg(v_stx_2276_, v___x_2285_);
v___x_2287_ = lean_unsigned_to_nat(2u);
v_closer_2288_ = l_Lean_Syntax_getArg(v_stx_2276_, v___x_2287_);
v___x_2289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2289_, 0, v_stx_2276_);
lean_ctor_set(v___x_2289_, 1, v_opener_2286_);
lean_ctor_set(v___x_2289_, 2, v_contents_2281_);
lean_ctor_set(v___x_2289_, 3, v_closer_2288_);
v___x_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___impl(lean_object* v_x_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_obj_tag_nat(v_x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___impl___boxed(lean_object* v_x_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Doc_BlockView_ctorIdx___impl(v_x_2293_);
lean_dec_ref(v_x_2293_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___redArg(lean_object* v_t_2295_, lean_object* v_k_2296_){
_start:
{
lean_object* v_view_2297_; lean_object* v___x_2298_; 
v_view_2297_ = lean_ctor_get(v_t_2295_, 0);
lean_inc_ref(v_view_2297_);
lean_dec_ref(v_t_2295_);
v___x_2298_ = lean_apply_1(v_k_2296_, v_view_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim(lean_object* v_motive_2299_, lean_object* v_ctorIdx_2300_, lean_object* v_t_2301_, lean_object* v_h_2302_, lean_object* v_k_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2301_, v_k_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___boxed(lean_object* v_motive_2305_, lean_object* v_ctorIdx_2306_, lean_object* v_t_2307_, lean_object* v_h_2308_, lean_object* v_k_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Doc_BlockView_ctorElim(v_motive_2305_, v_ctorIdx_2306_, v_t_2307_, v_h_2308_, v_k_2309_);
lean_dec(v_ctorIdx_2306_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim___redArg(lean_object* v_t_2311_, lean_object* v_para_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2311_, v_para_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim(lean_object* v_motive_2314_, lean_object* v_t_2315_, lean_object* v_h_2316_, lean_object* v_para_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2315_, v_para_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim___redArg(lean_object* v_t_2319_, lean_object* v_ul_2320_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2319_, v_ul_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim(lean_object* v_motive_2322_, lean_object* v_t_2323_, lean_object* v_h_2324_, lean_object* v_ul_2325_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2323_, v_ul_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim___redArg(lean_object* v_t_2327_, lean_object* v_ol_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2327_, v_ol_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim(lean_object* v_motive_2330_, lean_object* v_t_2331_, lean_object* v_h_2332_, lean_object* v_ol_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2331_, v_ol_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim___redArg(lean_object* v_t_2335_, lean_object* v_dl_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2335_, v_dl_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim(lean_object* v_motive_2338_, lean_object* v_t_2339_, lean_object* v_h_2340_, lean_object* v_dl_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2339_, v_dl_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim___redArg(lean_object* v_t_2343_, lean_object* v_blockquote_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2343_, v_blockquote_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim(lean_object* v_motive_2346_, lean_object* v_t_2347_, lean_object* v_h_2348_, lean_object* v_blockquote_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2347_, v_blockquote_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim___redArg(lean_object* v_t_2351_, lean_object* v_codeblock_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2351_, v_codeblock_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim(lean_object* v_motive_2354_, lean_object* v_t_2355_, lean_object* v_h_2356_, lean_object* v_codeblock_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2355_, v_codeblock_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim___redArg(lean_object* v_t_2359_, lean_object* v_directive_2360_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2359_, v_directive_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim(lean_object* v_motive_2362_, lean_object* v_t_2363_, lean_object* v_h_2364_, lean_object* v_directive_2365_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2363_, v_directive_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim___redArg(lean_object* v_t_2367_, lean_object* v_command_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2367_, v_command_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim(lean_object* v_motive_2370_, lean_object* v_t_2371_, lean_object* v_h_2372_, lean_object* v_command_2373_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2371_, v_command_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim___redArg(lean_object* v_t_2375_, lean_object* v_header_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2375_, v_header_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim(lean_object* v_motive_2378_, lean_object* v_t_2379_, lean_object* v_h_2380_, lean_object* v_header_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2379_, v_header_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim___redArg(lean_object* v_t_2383_, lean_object* v_linkRef_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2383_, v_linkRef_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim(lean_object* v_motive_2386_, lean_object* v_t_2387_, lean_object* v_h_2388_, lean_object* v_linkRef_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2387_, v_linkRef_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim___redArg(lean_object* v_t_2391_, lean_object* v_footnoteRef_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2391_, v_footnoteRef_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim(lean_object* v_motive_2394_, lean_object* v_t_2395_, lean_object* v_h_2396_, lean_object* v_footnoteRef_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2395_, v_footnoteRef_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim___redArg(lean_object* v_t_2399_, lean_object* v_metadata_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2399_, v_metadata_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim(lean_object* v_motive_2402_, lean_object* v_t_2403_, lean_object* v_h_2404_, lean_object* v_metadata_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2403_, v_metadata_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeParaViewBlockView___lam__0(lean_object* v_view_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v_view_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0(lean_object* v_view_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_view_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0(lean_object* v_view_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_view_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDescListViewBlockView___lam__0(lean_object* v_view_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2424_, 0, v_view_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0(lean_object* v_view_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2428_, 0, v_view_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0(lean_object* v_view_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2432_, 0, v_view_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0(lean_object* v_view_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2436_, 0, v_view_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCommandViewBlockView___lam__0(lean_object* v_view_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_view_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___lam__0(lean_object* v_view_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2444_, 0, v_view_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0(lean_object* v_view_2447_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2448_, 0, v_view_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0(lean_object* v_view_2451_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2452_, 0, v_view_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___lam__0(lean_object* v_view_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_view_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx(lean_object* v_x_2459_){
_start:
{
lean_object* v_view_2460_; lean_object* v_stx_2461_; 
v_view_2460_ = lean_ctor_get(v_x_2459_, 0);
v_stx_2461_ = lean_ctor_get(v_view_2460_, 0);
lean_inc(v_stx_2461_);
return v_stx_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx___boxed(lean_object* v_x_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Doc_BlockView_stx(v_x_2462_);
lean_dec_ref(v_x_2462_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_of(lean_object* v_stx_2464_){
_start:
{
lean_object* v___x_2465_; 
lean_inc(v_stx_2464_);
v___x_2465_ = l_Lean_Doc_ParaView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v___x_2466_; 
lean_inc(v_stx_2464_);
v___x_2466_ = l_Lean_Doc_UnorderedListView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v___x_2467_; 
lean_inc(v_stx_2464_);
v___x_2467_ = l_Lean_Doc_OrderedListView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v___x_2468_; 
lean_inc(v_stx_2464_);
v___x_2468_ = l_Lean_Doc_DescListView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v___x_2469_; 
lean_inc(v_stx_2464_);
v___x_2469_ = l_Lean_Doc_BlockquoteView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v___x_2470_; 
lean_inc(v_stx_2464_);
v___x_2470_ = l_Lean_Doc_CodeBlockView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v___x_2471_; 
lean_inc(v_stx_2464_);
v___x_2471_ = l_Lean_Doc_DirectiveView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v___x_2472_; 
lean_inc(v_stx_2464_);
v___x_2472_ = l_Lean_Doc_CommandView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v___x_2473_; 
lean_inc(v_stx_2464_);
v___x_2473_ = l_Lean_Doc_HeaderView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v___x_2474_; 
lean_inc(v_stx_2464_);
v___x_2474_ = l_Lean_Doc_LinkRefView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v___x_2475_; 
lean_inc(v_stx_2464_);
v___x_2475_ = l_Lean_Doc_FootnoteRefView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lean_Doc_MetadataView_of(v_stx_2464_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_box(0);
return v___x_2477_;
}
else
{
lean_object* v_val_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2486_; 
v_val_2478_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2480_ = v___x_2476_;
v_isShared_2481_ = v_isSharedCheck_2486_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_val_2478_);
lean_dec(v___x_2476_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2486_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2482_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2482_, 0, v_val_2478_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2482_);
v___x_2484_ = v___x_2480_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v_val_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_stx_2464_);
v_val_2487_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2489_ = v___x_2475_;
v_isShared_2490_ = v_isSharedCheck_2495_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_val_2487_);
lean_dec(v___x_2475_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2495_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2491_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_val_2487_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2491_);
v___x_2493_ = v___x_2489_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_object* v_val_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_stx_2464_);
v_val_2496_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2498_ = v___x_2474_;
v_isShared_2499_ = v_isSharedCheck_2504_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_val_2496_);
lean_dec(v___x_2474_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2504_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2500_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_val_2496_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2500_);
v___x_2502_ = v___x_2498_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_object* v_val_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_stx_2464_);
v_val_2505_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2507_ = v___x_2473_;
v_isShared_2508_ = v_isSharedCheck_2513_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_val_2505_);
lean_dec(v___x_2473_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2513_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_val_2505_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2509_);
v___x_2511_ = v___x_2507_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
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
else
{
lean_object* v_val_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v_stx_2464_);
v_val_2514_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2516_ = v___x_2472_;
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_val_2514_);
lean_dec(v___x_2472_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2518_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2518_, 0, v_val_2514_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
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
else
{
lean_object* v_val_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_stx_2464_);
v_val_2523_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2525_ = v___x_2471_;
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_val_2523_);
lean_dec(v___x_2471_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2527_, 0, v_val_2523_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2527_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v_val_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_stx_2464_);
v_val_2532_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2534_ = v___x_2470_;
v_isShared_2535_ = v_isSharedCheck_2540_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_val_2532_);
lean_dec(v___x_2470_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2540_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
v___x_2536_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_val_2532_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2536_);
v___x_2538_ = v___x_2534_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_object* v_val_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_stx_2464_);
v_val_2541_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2543_ = v___x_2469_;
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_val_2541_);
lean_dec(v___x_2469_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_val_2541_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2545_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
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
else
{
lean_object* v_val_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2558_; 
lean_dec(v_stx_2464_);
v_val_2550_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2552_ = v___x_2468_;
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_val_2550_);
lean_dec(v___x_2468_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_val_2550_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2554_);
v___x_2556_ = v___x_2552_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
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
else
{
lean_object* v_val_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v_stx_2464_);
v_val_2559_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2561_ = v___x_2467_;
v_isShared_2562_ = v_isSharedCheck_2567_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_val_2559_);
lean_dec(v___x_2467_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2567_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2565_; 
v___x_2563_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_val_2559_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2563_);
v___x_2565_ = v___x_2561_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
lean_object* v_val_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v_stx_2464_);
v_val_2568_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2570_ = v___x_2466_;
v_isShared_2571_ = v_isSharedCheck_2576_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_val_2568_);
lean_dec(v___x_2466_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2576_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2572_, 0, v_val_2568_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2572_);
v___x_2574_ = v___x_2570_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_object* v_val_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v_stx_2464_);
v_val_2577_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2579_ = v___x_2465_;
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_val_2577_);
lean_dec(v___x_2465_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v_val_2577_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoInline_view(lean_object* v_stx_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Doc_InlineView_of(v_stx_2586_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2588_; 
v___x_2588_ = ((lean_object*)(l_Lean_Doc_instInhabitedInlineView_default));
return v___x_2588_;
}
else
{
lean_object* v_val_2589_; 
v_val_2589_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_val_2589_);
lean_dec_ref_known(v___x_2587_, 1);
return v_val_2589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoBlock_view(lean_object* v_stx_2590_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_Doc_BlockView_of(v_stx_2590_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2592_; 
v___x_2592_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlockView_default));
return v___x_2592_;
}
else
{
lean_object* v_val_2593_; 
v_val_2593_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_val_2593_);
lean_dec_ref_known(v___x_2591_, 1);
return v_val_2593_;
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
