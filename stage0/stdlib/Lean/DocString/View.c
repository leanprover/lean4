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
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom(lean_object* v_src_408_, lean_object* v_value_409_, uint8_t v_canonical_410_){
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
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom___boxed(lean_object* v_src_415_, lean_object* v_value_416_, lean_object* v_canonical_417_){
_start:
{
uint8_t v_canonical_boxed_418_; lean_object* v_res_419_; 
v_canonical_boxed_418_ = lean_unbox(v_canonical_417_);
v_res_419_ = l_Lean_Doc_mkVersoTextFrom(v_src_415_, v_value_416_, v_canonical_boxed_418_);
lean_dec_ref(v_value_416_);
lean_dec(v_src_415_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom(lean_object* v_src_420_, lean_object* v_value_421_, uint8_t v_canonical_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = l_Lean_Doc_versoRefKind;
v___x_424_ = l_Lean_SourceInfo_fromRef(v_src_420_, v_canonical_422_);
v___x_425_ = l_Lean_Syntax_mkLit(v___x_423_, v_value_421_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom___boxed(lean_object* v_src_426_, lean_object* v_value_427_, lean_object* v_canonical_428_){
_start:
{
uint8_t v_canonical_boxed_429_; lean_object* v_res_430_; 
v_canonical_boxed_429_ = lean_unbox(v_canonical_428_);
v_res_430_ = l_Lean_Doc_mkVersoRefNameFrom(v_src_426_, v_value_427_, v_canonical_boxed_429_);
lean_dec(v_src_426_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom(lean_object* v_src_431_, lean_object* v_value_432_, uint8_t v_canonical_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = l_Lean_Doc_versoLinkUrlKind;
v___x_435_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_432_);
v___x_436_ = l_Lean_SourceInfo_fromRef(v_src_431_, v_canonical_433_);
v___x_437_ = l_Lean_Syntax_mkLit(v___x_434_, v___x_435_, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom___boxed(lean_object* v_src_438_, lean_object* v_value_439_, lean_object* v_canonical_440_){
_start:
{
uint8_t v_canonical_boxed_441_; lean_object* v_res_442_; 
v_canonical_boxed_441_ = lean_unbox(v_canonical_440_);
v_res_442_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_src_438_, v_value_439_, v_canonical_boxed_441_);
lean_dec_ref(v_value_439_);
lean_dec(v_src_438_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom(lean_object* v_src_443_, lean_object* v_value_444_, uint8_t v_canonical_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_446_ = l_Lean_Doc_versoImageAltKind;
v___x_447_ = l_Lean_Doc_escapeVersoImageAlt(v_value_444_);
v___x_448_ = l_Lean_SourceInfo_fromRef(v_src_443_, v_canonical_445_);
v___x_449_ = l_Lean_Syntax_mkLit(v___x_446_, v___x_447_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom___boxed(lean_object* v_src_450_, lean_object* v_value_451_, lean_object* v_canonical_452_){
_start:
{
uint8_t v_canonical_boxed_453_; lean_object* v_res_454_; 
v_canonical_boxed_453_ = lean_unbox(v_canonical_452_);
v_res_454_ = l_Lean_Doc_mkVersoImageAltFrom(v_src_450_, v_value_451_, v_canonical_boxed_453_);
lean_dec_ref(v_value_451_);
lean_dec(v_src_450_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom(lean_object* v_src_455_, lean_object* v_value_456_, uint8_t v_canonical_457_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = l_Lean_Doc_versoLinkRefUrlKind;
v___x_459_ = l_Lean_SourceInfo_fromRef(v_src_455_, v_canonical_457_);
v___x_460_ = l_Lean_Syntax_mkLit(v___x_458_, v_value_456_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom___boxed(lean_object* v_src_461_, lean_object* v_value_462_, lean_object* v_canonical_463_){
_start:
{
uint8_t v_canonical_boxed_464_; lean_object* v_res_465_; 
v_canonical_boxed_464_ = lean_unbox(v_canonical_463_);
v_res_465_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_src_461_, v_value_462_, v_canonical_boxed_464_);
lean_dec(v_src_461_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(lean_object* v_info_466_, lean_object* v___x_467_, lean_object* v_value_468_, lean_object* v_a_469_, lean_object* v_b_470_){
_start:
{
uint8_t v_decide_471_; 
v_decide_471_ = lean_nat_dec_eq(v_a_469_, v___x_467_);
if (v_decide_471_ == 0)
{
lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_494_; 
v_fst_472_ = lean_ctor_get(v_b_470_, 0);
v_snd_473_ = lean_ctor_get(v_b_470_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_b_470_);
if (v_isSharedCheck_494_ == 0)
{
v___x_475_ = v_b_470_;
v_isShared_476_ = v_isSharedCheck_494_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snd_473_);
lean_inc(v_fst_472_);
lean_dec(v_b_470_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_494_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint32_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_477_ = lean_string_utf8_get_fast(v_value_468_, v_a_469_);
v___x_478_ = lean_string_utf8_next_fast(v_value_468_, v_a_469_);
lean_dec(v_a_469_);
v___x_479_ = lean_string_push(v_snd_473_, v___x_477_);
v___x_480_ = 10;
v___x_481_ = lean_uint32_dec_eq(v___x_477_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_483_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v___x_479_);
v___x_483_ = v___x_475_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_fst_472_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_479_);
v___x_483_ = v_reuseFailAlloc_485_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
v_a_469_ = v___x_478_;
v_b_470_ = v___x_483_;
goto _start;
}
}
else
{
lean_object* v_line_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v_line_486_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0));
v___x_487_ = l_Lean_Doc_versoCodeLineKind;
lean_inc(v_info_466_);
v___x_488_ = l_Lean_Syntax_mkLit(v___x_487_, v___x_479_, v_info_466_);
v___x_489_ = lean_array_push(v_fst_472_, v___x_488_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v_line_486_);
lean_ctor_set(v___x_475_, 0, v___x_489_);
v___x_491_ = v___x_475_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_line_486_);
v___x_491_ = v_reuseFailAlloc_493_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
v_a_469_ = v___x_478_;
v_b_470_ = v___x_491_;
goto _start;
}
}
}
}
else
{
lean_dec(v_a_469_);
lean_dec(v_info_466_);
return v_b_470_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg___boxed(lean_object* v_info_495_, lean_object* v___x_496_, lean_object* v_value_497_, lean_object* v_a_498_, lean_object* v_b_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_495_, v___x_496_, v_value_497_, v_a_498_, v_b_499_);
lean_dec_ref(v_value_497_);
lean_dec(v___x_496_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(lean_object* v_info_506_, lean_object* v_value_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_fst_512_; lean_object* v_snd_513_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__1));
v___x_510_ = lean_string_utf8_byte_size(v_value_507_);
lean_inc(v_info_506_);
v___x_511_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_506_, v___x_510_, v_value_507_, v___x_508_, v___x_509_);
v_fst_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_fst_512_);
v_snd_513_ = lean_ctor_get(v___x_511_, 1);
lean_inc(v_snd_513_);
lean_dec_ref(v___x_511_);
v___x_518_ = lean_string_utf8_byte_size(v_snd_513_);
v___x_519_ = lean_nat_dec_eq(v___x_518_, v___x_508_);
if (v___x_519_ == 0)
{
goto v___jp_514_;
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_array_get_size(v_fst_512_);
v___x_521_ = lean_nat_dec_eq(v___x_520_, v___x_508_);
if (v___x_521_ == 0)
{
lean_dec(v_snd_513_);
lean_dec(v_info_506_);
return v_fst_512_;
}
else
{
goto v___jp_514_;
}
}
v___jp_514_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = l_Lean_Doc_versoCodeLineKind;
v___x_516_ = l_Lean_Syntax_mkLit(v___x_515_, v_snd_513_, v_info_506_);
v___x_517_ = lean_array_push(v_fst_512_, v___x_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___boxed(lean_object* v_info_522_, lean_object* v_value_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_522_, v_value_523_);
lean_dec_ref(v_value_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(lean_object* v_info_525_, lean_object* v___x_526_, lean_object* v___x_527_, lean_object* v_value_528_, lean_object* v_inst_529_, lean_object* v_R_530_, lean_object* v_a_531_, lean_object* v_b_532_, lean_object* v_c_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_525_, v___x_527_, v_value_528_, v_a_531_, v_b_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___boxed(lean_object* v_info_535_, lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v_value_538_, lean_object* v_inst_539_, lean_object* v_R_540_, lean_object* v_a_541_, lean_object* v_b_542_, lean_object* v_c_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(v_info_535_, v___x_536_, v___x_537_, v_value_538_, v_inst_539_, v_R_540_, v_a_541_, v_b_542_, v_c_543_);
lean_dec_ref(v_value_538_);
lean_dec(v___x_537_);
lean_dec_ref(v___x_536_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom(lean_object* v_src_548_, lean_object* v_value_549_, uint8_t v_canonical_550_){
_start:
{
lean_object* v_info_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_info_551_ = l_Lean_SourceInfo_fromRef(v_src_548_, v_canonical_550_);
v___x_552_ = l_Lean_Doc_versoCodeKind;
lean_inc(v_info_551_);
v___x_553_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_551_, v_value_549_);
v___x_554_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_555_ = lean_box(2);
v___x_556_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
lean_ctor_set(v___x_556_, 2, v___x_553_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_mk_empty_array_with_capacity(v___x_557_);
v___x_559_ = lean_array_push(v___x_558_, v___x_556_);
v___x_560_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_560_, 0, v_info_551_);
lean_ctor_set(v___x_560_, 1, v___x_552_);
lean_ctor_set(v___x_560_, 2, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom___boxed(lean_object* v_src_561_, lean_object* v_value_562_, lean_object* v_canonical_563_){
_start:
{
uint8_t v_canonical_boxed_564_; lean_object* v_res_565_; 
v_canonical_boxed_564_ = lean_unbox(v_canonical_563_);
v_res_565_ = l_Lean_Doc_mkVersoCodeFrom(v_src_561_, v_value_562_, v_canonical_boxed_564_);
lean_dec_ref(v_value_562_);
lean_dec(v_src_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom(lean_object* v_src_566_, lean_object* v_value_567_, uint8_t v_canonical_568_){
_start:
{
lean_object* v_info_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_info_569_ = l_Lean_SourceInfo_fromRef(v_src_566_, v_canonical_568_);
v___x_570_ = l_Lean_Doc_versoCodeBlockKind;
lean_inc(v_info_569_);
v___x_571_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_569_, v_value_567_);
v___x_572_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_573_ = lean_box(2);
v___x_574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_572_);
lean_ctor_set(v___x_574_, 2, v___x_571_);
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_mk_empty_array_with_capacity(v___x_575_);
v___x_577_ = lean_array_push(v___x_576_, v___x_574_);
v___x_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_578_, 0, v_info_569_);
lean_ctor_set(v___x_578_, 1, v___x_570_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___boxed(lean_object* v_src_579_, lean_object* v_value_580_, lean_object* v_canonical_581_){
_start:
{
uint8_t v_canonical_boxed_582_; lean_object* v_res_583_; 
v_canonical_boxed_582_ = lean_unbox(v_canonical_581_);
v_res_583_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_src_579_, v_value_580_, v_canonical_boxed_582_);
lean_dec_ref(v_value_580_);
lean_dec(v_src_579_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom(lean_object* v_src_593_, uint8_t v_canonical_594_){
_start:
{
lean_object* v_info_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_info_595_ = l_Lean_SourceInfo_fromRef(v_src_593_, v_canonical_594_);
v___x_596_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
v___x_597_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__3));
lean_inc(v_info_595_);
v___x_598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_598_, 0, v_info_595_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_mk_empty_array_with_capacity(v___x_599_);
v___x_601_ = lean_array_push(v___x_600_, v___x_598_);
v___x_602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_602_, 0, v_info_595_);
lean_ctor_set(v___x_602_, 1, v___x_596_);
lean_ctor_set(v___x_602_, 2, v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom___boxed(lean_object* v_src_603_, lean_object* v_canonical_604_){
_start:
{
uint8_t v_canonical_boxed_605_; lean_object* v_res_606_; 
v_canonical_boxed_605_ = lean_unbox(v_canonical_604_);
v_res_606_ = l_Lean_Doc_mkVersoLinebreakFrom(v_src_603_, v_canonical_boxed_605_);
lean_dec(v_src_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(uint8_t v_canonical_607_, lean_object* v_toPure_608_, lean_object* v_____do__lift_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = l_Lean_Doc_mkVersoLinebreakFrom(v_____do__lift_609_, v_canonical_607_);
v___x_611_ = lean_apply_2(v_toPure_608_, lean_box(0), v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed(lean_object* v_canonical_612_, lean_object* v_toPure_613_, lean_object* v_____do__lift_614_){
_start:
{
uint8_t v_canonical_boxed_615_; lean_object* v_res_616_; 
v_canonical_boxed_615_ = lean_unbox(v_canonical_612_);
v_res_616_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(v_canonical_boxed_615_, v_toPure_613_, v_____do__lift_614_);
lean_dec(v_____do__lift_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg(lean_object* v_inst_617_, lean_object* v_inst_618_, uint8_t v_canonical_619_){
_start:
{
lean_object* v_toApplicative_620_; lean_object* v_toBind_621_; lean_object* v_getRef_622_; lean_object* v_toPure_623_; lean_object* v___x_624_; lean_object* v___f_625_; lean_object* v___x_626_; 
v_toApplicative_620_ = lean_ctor_get(v_inst_617_, 0);
lean_inc_ref(v_toApplicative_620_);
v_toBind_621_ = lean_ctor_get(v_inst_617_, 1);
lean_inc(v_toBind_621_);
lean_dec_ref(v_inst_617_);
v_getRef_622_ = lean_ctor_get(v_inst_618_, 0);
lean_inc(v_getRef_622_);
lean_dec_ref(v_inst_618_);
v_toPure_623_ = lean_ctor_get(v_toApplicative_620_, 1);
lean_inc(v_toPure_623_);
lean_dec_ref(v_toApplicative_620_);
v___x_624_ = lean_box(v_canonical_619_);
v___f_625_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_625_, 0, v___x_624_);
lean_closure_set(v___f_625_, 1, v_toPure_623_);
v___x_626_ = lean_apply_4(v_toBind_621_, lean_box(0), lean_box(0), v_getRef_622_, v___f_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___boxed(lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_canonical_629_){
_start:
{
uint8_t v_canonical_boxed_630_; lean_object* v_res_631_; 
v_canonical_boxed_630_ = lean_unbox(v_canonical_629_);
v_res_631_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_627_, v_inst_628_, v_canonical_boxed_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef(lean_object* v_m_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, uint8_t v_canonical_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_633_, v_inst_634_, v_canonical_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___boxed(lean_object* v_m_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_canonical_640_){
_start:
{
uint8_t v_canonical_boxed_641_; lean_object* v_res_642_; 
v_canonical_boxed_641_ = lean_unbox(v_canonical_640_);
v_res_642_ = l_Lean_Doc_mkVersoLinebreakFromRef(v_m_637_, v_inst_638_, v_inst_639_, v_canonical_boxed_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(lean_object* v_value_643_, uint8_t v_canonical_644_, lean_object* v_toPure_645_, lean_object* v_____do__lift_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = l_Lean_Doc_mkVersoTextFrom(v_____do__lift_646_, v_value_643_, v_canonical_644_);
v___x_648_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed(lean_object* v_value_649_, lean_object* v_canonical_650_, lean_object* v_toPure_651_, lean_object* v_____do__lift_652_){
_start:
{
uint8_t v_canonical_boxed_653_; lean_object* v_res_654_; 
v_canonical_boxed_653_ = lean_unbox(v_canonical_650_);
v_res_654_ = l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(v_value_649_, v_canonical_boxed_653_, v_toPure_651_, v_____do__lift_652_);
lean_dec(v_____do__lift_652_);
lean_dec_ref(v_value_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg(lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_value_657_, uint8_t v_canonical_658_){
_start:
{
lean_object* v_toApplicative_659_; lean_object* v_toBind_660_; lean_object* v_getRef_661_; lean_object* v_toPure_662_; lean_object* v___x_663_; lean_object* v___f_664_; lean_object* v___x_665_; 
v_toApplicative_659_ = lean_ctor_get(v_inst_655_, 0);
lean_inc_ref(v_toApplicative_659_);
v_toBind_660_ = lean_ctor_get(v_inst_655_, 1);
lean_inc(v_toBind_660_);
lean_dec_ref(v_inst_655_);
v_getRef_661_ = lean_ctor_get(v_inst_656_, 0);
lean_inc(v_getRef_661_);
lean_dec_ref(v_inst_656_);
v_toPure_662_ = lean_ctor_get(v_toApplicative_659_, 1);
lean_inc(v_toPure_662_);
lean_dec_ref(v_toApplicative_659_);
v___x_663_ = lean_box(v_canonical_658_);
v___f_664_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_664_, 0, v_value_657_);
lean_closure_set(v___f_664_, 1, v___x_663_);
lean_closure_set(v___f_664_, 2, v_toPure_662_);
v___x_665_ = lean_apply_4(v_toBind_660_, lean_box(0), lean_box(0), v_getRef_661_, v___f_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___boxed(lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_value_668_, lean_object* v_canonical_669_){
_start:
{
uint8_t v_canonical_boxed_670_; lean_object* v_res_671_; 
v_canonical_boxed_670_ = lean_unbox(v_canonical_669_);
v_res_671_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_666_, v_inst_667_, v_value_668_, v_canonical_boxed_670_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef(lean_object* v_m_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_value_675_, uint8_t v_canonical_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_673_, v_inst_674_, v_value_675_, v_canonical_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___boxed(lean_object* v_m_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_value_681_, lean_object* v_canonical_682_){
_start:
{
uint8_t v_canonical_boxed_683_; lean_object* v_res_684_; 
v_canonical_boxed_683_ = lean_unbox(v_canonical_682_);
v_res_684_ = l_Lean_Doc_mkVersoTextFromRef(v_m_678_, v_inst_679_, v_inst_680_, v_value_681_, v_canonical_boxed_683_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(lean_object* v_value_685_, uint8_t v_canonical_686_, lean_object* v_toPure_687_, lean_object* v_____do__lift_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = l_Lean_Doc_mkVersoRefNameFrom(v_____do__lift_688_, v_value_685_, v_canonical_686_);
v___x_690_ = lean_apply_2(v_toPure_687_, lean_box(0), v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed(lean_object* v_value_691_, lean_object* v_canonical_692_, lean_object* v_toPure_693_, lean_object* v_____do__lift_694_){
_start:
{
uint8_t v_canonical_boxed_695_; lean_object* v_res_696_; 
v_canonical_boxed_695_ = lean_unbox(v_canonical_692_);
v_res_696_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(v_value_691_, v_canonical_boxed_695_, v_toPure_693_, v_____do__lift_694_);
lean_dec(v_____do__lift_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg(lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_value_699_, uint8_t v_canonical_700_){
_start:
{
lean_object* v_toApplicative_701_; lean_object* v_toBind_702_; lean_object* v_getRef_703_; lean_object* v_toPure_704_; lean_object* v___x_705_; lean_object* v___f_706_; lean_object* v___x_707_; 
v_toApplicative_701_ = lean_ctor_get(v_inst_697_, 0);
lean_inc_ref(v_toApplicative_701_);
v_toBind_702_ = lean_ctor_get(v_inst_697_, 1);
lean_inc(v_toBind_702_);
lean_dec_ref(v_inst_697_);
v_getRef_703_ = lean_ctor_get(v_inst_698_, 0);
lean_inc(v_getRef_703_);
lean_dec_ref(v_inst_698_);
v_toPure_704_ = lean_ctor_get(v_toApplicative_701_, 1);
lean_inc(v_toPure_704_);
lean_dec_ref(v_toApplicative_701_);
v___x_705_ = lean_box(v_canonical_700_);
v___f_706_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_706_, 0, v_value_699_);
lean_closure_set(v___f_706_, 1, v___x_705_);
lean_closure_set(v___f_706_, 2, v_toPure_704_);
v___x_707_ = lean_apply_4(v_toBind_702_, lean_box(0), lean_box(0), v_getRef_703_, v___f_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___boxed(lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_value_710_, lean_object* v_canonical_711_){
_start:
{
uint8_t v_canonical_boxed_712_; lean_object* v_res_713_; 
v_canonical_boxed_712_ = lean_unbox(v_canonical_711_);
v_res_713_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_708_, v_inst_709_, v_value_710_, v_canonical_boxed_712_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef(lean_object* v_m_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_value_717_, uint8_t v_canonical_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_715_, v_inst_716_, v_value_717_, v_canonical_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___boxed(lean_object* v_m_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_value_723_, lean_object* v_canonical_724_){
_start:
{
uint8_t v_canonical_boxed_725_; lean_object* v_res_726_; 
v_canonical_boxed_725_ = lean_unbox(v_canonical_724_);
v_res_726_ = l_Lean_Doc_mkVersoRefNameFromRef(v_m_720_, v_inst_721_, v_inst_722_, v_value_723_, v_canonical_boxed_725_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(lean_object* v_value_727_, uint8_t v_canonical_728_, lean_object* v_toPure_729_, lean_object* v_____do__lift_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_____do__lift_730_, v_value_727_, v_canonical_728_);
v___x_732_ = lean_apply_2(v_toPure_729_, lean_box(0), v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_733_, lean_object* v_canonical_734_, lean_object* v_toPure_735_, lean_object* v_____do__lift_736_){
_start:
{
uint8_t v_canonical_boxed_737_; lean_object* v_res_738_; 
v_canonical_boxed_737_ = lean_unbox(v_canonical_734_);
v_res_738_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(v_value_733_, v_canonical_boxed_737_, v_toPure_735_, v_____do__lift_736_);
lean_dec(v_____do__lift_736_);
lean_dec_ref(v_value_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_value_741_, uint8_t v_canonical_742_){
_start:
{
lean_object* v_toApplicative_743_; lean_object* v_toBind_744_; lean_object* v_getRef_745_; lean_object* v_toPure_746_; lean_object* v___x_747_; lean_object* v___f_748_; lean_object* v___x_749_; 
v_toApplicative_743_ = lean_ctor_get(v_inst_739_, 0);
lean_inc_ref(v_toApplicative_743_);
v_toBind_744_ = lean_ctor_get(v_inst_739_, 1);
lean_inc(v_toBind_744_);
lean_dec_ref(v_inst_739_);
v_getRef_745_ = lean_ctor_get(v_inst_740_, 0);
lean_inc(v_getRef_745_);
lean_dec_ref(v_inst_740_);
v_toPure_746_ = lean_ctor_get(v_toApplicative_743_, 1);
lean_inc(v_toPure_746_);
lean_dec_ref(v_toApplicative_743_);
v___x_747_ = lean_box(v_canonical_742_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_748_, 0, v_value_741_);
lean_closure_set(v___f_748_, 1, v___x_747_);
lean_closure_set(v___f_748_, 2, v_toPure_746_);
v___x_749_ = lean_apply_4(v_toBind_744_, lean_box(0), lean_box(0), v_getRef_745_, v___f_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___boxed(lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_value_752_, lean_object* v_canonical_753_){
_start:
{
uint8_t v_canonical_boxed_754_; lean_object* v_res_755_; 
v_canonical_boxed_754_ = lean_unbox(v_canonical_753_);
v_res_755_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_750_, v_inst_751_, v_value_752_, v_canonical_boxed_754_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef(lean_object* v_m_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_value_759_, uint8_t v_canonical_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_757_, v_inst_758_, v_value_759_, v_canonical_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___boxed(lean_object* v_m_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_value_765_, lean_object* v_canonical_766_){
_start:
{
uint8_t v_canonical_boxed_767_; lean_object* v_res_768_; 
v_canonical_boxed_767_ = lean_unbox(v_canonical_766_);
v_res_768_ = l_Lean_Doc_mkVersoLinkUrlFromRef(v_m_762_, v_inst_763_, v_inst_764_, v_value_765_, v_canonical_boxed_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(lean_object* v_value_769_, uint8_t v_canonical_770_, lean_object* v_toPure_771_, lean_object* v_____do__lift_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = l_Lean_Doc_mkVersoImageAltFrom(v_____do__lift_772_, v_value_769_, v_canonical_770_);
v___x_774_ = lean_apply_2(v_toPure_771_, lean_box(0), v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed(lean_object* v_value_775_, lean_object* v_canonical_776_, lean_object* v_toPure_777_, lean_object* v_____do__lift_778_){
_start:
{
uint8_t v_canonical_boxed_779_; lean_object* v_res_780_; 
v_canonical_boxed_779_ = lean_unbox(v_canonical_776_);
v_res_780_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(v_value_775_, v_canonical_boxed_779_, v_toPure_777_, v_____do__lift_778_);
lean_dec(v_____do__lift_778_);
lean_dec_ref(v_value_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg(lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_value_783_, uint8_t v_canonical_784_){
_start:
{
lean_object* v_toApplicative_785_; lean_object* v_toBind_786_; lean_object* v_getRef_787_; lean_object* v_toPure_788_; lean_object* v___x_789_; lean_object* v___f_790_; lean_object* v___x_791_; 
v_toApplicative_785_ = lean_ctor_get(v_inst_781_, 0);
lean_inc_ref(v_toApplicative_785_);
v_toBind_786_ = lean_ctor_get(v_inst_781_, 1);
lean_inc(v_toBind_786_);
lean_dec_ref(v_inst_781_);
v_getRef_787_ = lean_ctor_get(v_inst_782_, 0);
lean_inc(v_getRef_787_);
lean_dec_ref(v_inst_782_);
v_toPure_788_ = lean_ctor_get(v_toApplicative_785_, 1);
lean_inc(v_toPure_788_);
lean_dec_ref(v_toApplicative_785_);
v___x_789_ = lean_box(v_canonical_784_);
v___f_790_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_790_, 0, v_value_783_);
lean_closure_set(v___f_790_, 1, v___x_789_);
lean_closure_set(v___f_790_, 2, v_toPure_788_);
v___x_791_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v_getRef_787_, v___f_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___boxed(lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_value_794_, lean_object* v_canonical_795_){
_start:
{
uint8_t v_canonical_boxed_796_; lean_object* v_res_797_; 
v_canonical_boxed_796_ = lean_unbox(v_canonical_795_);
v_res_797_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_792_, v_inst_793_, v_value_794_, v_canonical_boxed_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef(lean_object* v_m_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_value_801_, uint8_t v_canonical_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_799_, v_inst_800_, v_value_801_, v_canonical_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___boxed(lean_object* v_m_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_value_807_, lean_object* v_canonical_808_){
_start:
{
uint8_t v_canonical_boxed_809_; lean_object* v_res_810_; 
v_canonical_boxed_809_ = lean_unbox(v_canonical_808_);
v_res_810_ = l_Lean_Doc_mkVersoImageAltFromRef(v_m_804_, v_inst_805_, v_inst_806_, v_value_807_, v_canonical_boxed_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(lean_object* v_value_811_, uint8_t v_canonical_812_, lean_object* v_toPure_813_, lean_object* v_____do__lift_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_____do__lift_814_, v_value_811_, v_canonical_812_);
v___x_816_ = lean_apply_2(v_toPure_813_, lean_box(0), v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_817_, lean_object* v_canonical_818_, lean_object* v_toPure_819_, lean_object* v_____do__lift_820_){
_start:
{
uint8_t v_canonical_boxed_821_; lean_object* v_res_822_; 
v_canonical_boxed_821_ = lean_unbox(v_canonical_818_);
v_res_822_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(v_value_817_, v_canonical_boxed_821_, v_toPure_819_, v_____do__lift_820_);
lean_dec(v_____do__lift_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_value_825_, uint8_t v_canonical_826_){
_start:
{
lean_object* v_toApplicative_827_; lean_object* v_toBind_828_; lean_object* v_getRef_829_; lean_object* v_toPure_830_; lean_object* v___x_831_; lean_object* v___f_832_; lean_object* v___x_833_; 
v_toApplicative_827_ = lean_ctor_get(v_inst_823_, 0);
lean_inc_ref(v_toApplicative_827_);
v_toBind_828_ = lean_ctor_get(v_inst_823_, 1);
lean_inc(v_toBind_828_);
lean_dec_ref(v_inst_823_);
v_getRef_829_ = lean_ctor_get(v_inst_824_, 0);
lean_inc(v_getRef_829_);
lean_dec_ref(v_inst_824_);
v_toPure_830_ = lean_ctor_get(v_toApplicative_827_, 1);
lean_inc(v_toPure_830_);
lean_dec_ref(v_toApplicative_827_);
v___x_831_ = lean_box(v_canonical_826_);
v___f_832_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_832_, 0, v_value_825_);
lean_closure_set(v___f_832_, 1, v___x_831_);
lean_closure_set(v___f_832_, 2, v_toPure_830_);
v___x_833_ = lean_apply_4(v_toBind_828_, lean_box(0), lean_box(0), v_getRef_829_, v___f_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___boxed(lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_value_836_, lean_object* v_canonical_837_){
_start:
{
uint8_t v_canonical_boxed_838_; lean_object* v_res_839_; 
v_canonical_boxed_838_ = lean_unbox(v_canonical_837_);
v_res_839_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_834_, v_inst_835_, v_value_836_, v_canonical_boxed_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef(lean_object* v_m_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_value_843_, uint8_t v_canonical_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_841_, v_inst_842_, v_value_843_, v_canonical_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___boxed(lean_object* v_m_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_value_849_, lean_object* v_canonical_850_){
_start:
{
uint8_t v_canonical_boxed_851_; lean_object* v_res_852_; 
v_canonical_boxed_851_ = lean_unbox(v_canonical_850_);
v_res_852_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef(v_m_846_, v_inst_847_, v_inst_848_, v_value_849_, v_canonical_boxed_851_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(lean_object* v_value_853_, uint8_t v_canonical_854_, lean_object* v_toPure_855_, lean_object* v_____do__lift_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = l_Lean_Doc_mkVersoCodeFrom(v_____do__lift_856_, v_value_853_, v_canonical_854_);
v___x_858_ = lean_apply_2(v_toPure_855_, lean_box(0), v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed(lean_object* v_value_859_, lean_object* v_canonical_860_, lean_object* v_toPure_861_, lean_object* v_____do__lift_862_){
_start:
{
uint8_t v_canonical_boxed_863_; lean_object* v_res_864_; 
v_canonical_boxed_863_ = lean_unbox(v_canonical_860_);
v_res_864_ = l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(v_value_859_, v_canonical_boxed_863_, v_toPure_861_, v_____do__lift_862_);
lean_dec(v_____do__lift_862_);
lean_dec_ref(v_value_859_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg(lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_value_867_, uint8_t v_canonical_868_){
_start:
{
lean_object* v_toApplicative_869_; lean_object* v_toBind_870_; lean_object* v_getRef_871_; lean_object* v_toPure_872_; lean_object* v___x_873_; lean_object* v___f_874_; lean_object* v___x_875_; 
v_toApplicative_869_ = lean_ctor_get(v_inst_865_, 0);
lean_inc_ref(v_toApplicative_869_);
v_toBind_870_ = lean_ctor_get(v_inst_865_, 1);
lean_inc(v_toBind_870_);
lean_dec_ref(v_inst_865_);
v_getRef_871_ = lean_ctor_get(v_inst_866_, 0);
lean_inc(v_getRef_871_);
lean_dec_ref(v_inst_866_);
v_toPure_872_ = lean_ctor_get(v_toApplicative_869_, 1);
lean_inc(v_toPure_872_);
lean_dec_ref(v_toApplicative_869_);
v___x_873_ = lean_box(v_canonical_868_);
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_874_, 0, v_value_867_);
lean_closure_set(v___f_874_, 1, v___x_873_);
lean_closure_set(v___f_874_, 2, v_toPure_872_);
v___x_875_ = lean_apply_4(v_toBind_870_, lean_box(0), lean_box(0), v_getRef_871_, v___f_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___boxed(lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_value_878_, lean_object* v_canonical_879_){
_start:
{
uint8_t v_canonical_boxed_880_; lean_object* v_res_881_; 
v_canonical_boxed_880_ = lean_unbox(v_canonical_879_);
v_res_881_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_876_, v_inst_877_, v_value_878_, v_canonical_boxed_880_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef(lean_object* v_m_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_value_885_, uint8_t v_canonical_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_883_, v_inst_884_, v_value_885_, v_canonical_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___boxed(lean_object* v_m_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_value_891_, lean_object* v_canonical_892_){
_start:
{
uint8_t v_canonical_boxed_893_; lean_object* v_res_894_; 
v_canonical_boxed_893_ = lean_unbox(v_canonical_892_);
v_res_894_ = l_Lean_Doc_mkVersoCodeFromRef(v_m_888_, v_inst_889_, v_inst_890_, v_value_891_, v_canonical_boxed_893_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(lean_object* v_value_895_, uint8_t v_canonical_896_, lean_object* v_toPure_897_, lean_object* v_____do__lift_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_____do__lift_898_, v_value_895_, v_canonical_896_);
v___x_900_ = lean_apply_2(v_toPure_897_, lean_box(0), v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed(lean_object* v_value_901_, lean_object* v_canonical_902_, lean_object* v_toPure_903_, lean_object* v_____do__lift_904_){
_start:
{
uint8_t v_canonical_boxed_905_; lean_object* v_res_906_; 
v_canonical_boxed_905_ = lean_unbox(v_canonical_902_);
v_res_906_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(v_value_901_, v_canonical_boxed_905_, v_toPure_903_, v_____do__lift_904_);
lean_dec(v_____do__lift_904_);
lean_dec_ref(v_value_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_value_909_, uint8_t v_canonical_910_){
_start:
{
lean_object* v_toApplicative_911_; lean_object* v_toBind_912_; lean_object* v_getRef_913_; lean_object* v_toPure_914_; lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___x_917_; 
v_toApplicative_911_ = lean_ctor_get(v_inst_907_, 0);
lean_inc_ref(v_toApplicative_911_);
v_toBind_912_ = lean_ctor_get(v_inst_907_, 1);
lean_inc(v_toBind_912_);
lean_dec_ref(v_inst_907_);
v_getRef_913_ = lean_ctor_get(v_inst_908_, 0);
lean_inc(v_getRef_913_);
lean_dec_ref(v_inst_908_);
v_toPure_914_ = lean_ctor_get(v_toApplicative_911_, 1);
lean_inc(v_toPure_914_);
lean_dec_ref(v_toApplicative_911_);
v___x_915_ = lean_box(v_canonical_910_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_916_, 0, v_value_909_);
lean_closure_set(v___f_916_, 1, v___x_915_);
lean_closure_set(v___f_916_, 2, v_toPure_914_);
v___x_917_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v_getRef_913_, v___f_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___boxed(lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_value_920_, lean_object* v_canonical_921_){
_start:
{
uint8_t v_canonical_boxed_922_; lean_object* v_res_923_; 
v_canonical_boxed_922_ = lean_unbox(v_canonical_921_);
v_res_923_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_918_, v_inst_919_, v_value_920_, v_canonical_boxed_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef(lean_object* v_m_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_value_927_, uint8_t v_canonical_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_925_, v_inst_926_, v_value_927_, v_canonical_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___boxed(lean_object* v_m_930_, lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_value_933_, lean_object* v_canonical_934_){
_start:
{
uint8_t v_canonical_boxed_935_; lean_object* v_res_936_; 
v_canonical_boxed_935_ = lean_unbox(v_canonical_934_);
v_res_936_ = l_Lean_Doc_mkVersoCodeBlockFromRef(v_m_930_, v_inst_931_, v_inst_932_, v_value_933_, v_canonical_boxed_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_of(lean_object* v_stx_964_){
_start:
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__2));
lean_inc(v_stx_964_);
v___x_966_ = l_Lean_Syntax_isOfKind(v_stx_964_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__4));
lean_inc(v_stx_964_);
v___x_968_ = l_Lean_Syntax_isOfKind(v_stx_964_, v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
lean_dec(v_stx_964_);
v___x_969_ = lean_box(0);
return v___x_969_;
}
else
{
lean_object* v___x_970_; lean_object* v_o_971_; lean_object* v___x_972_; lean_object* v_name_973_; 
v___x_970_ = lean_unsigned_to_nat(0u);
v_o_971_ = l_Lean_Syntax_getArg(v_stx_964_, v___x_970_);
v___x_972_ = lean_unsigned_to_nat(1u);
v_name_973_ = l_Lean_Syntax_getArg(v_stx_964_, v___x_972_);
if (v___x_966_ == 0)
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_973_);
v___x_980_ = l_Lean_Syntax_isOfKind(v_name_973_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
lean_dec(v_name_973_);
lean_dec(v_o_971_);
lean_dec(v_stx_964_);
v___x_981_ = lean_box(0);
return v___x_981_;
}
else
{
goto v___jp_974_;
}
}
else
{
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_975_; lean_object* v_c_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_975_ = lean_unsigned_to_nat(2u);
v_c_976_ = l_Lean_Syntax_getArg(v_stx_964_, v___x_975_);
v___x_977_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_977_, 0, v_stx_964_);
lean_ctor_set(v___x_977_, 1, v_o_971_);
lean_ctor_set(v___x_977_, 2, v_name_973_);
lean_ctor_set(v___x_977_, 3, v_c_976_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
}
}
else
{
lean_object* v___x_982_; lean_object* v_url_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_982_ = lean_unsigned_to_nat(1u);
v_url_983_ = l_Lean_Syntax_getArg(v_stx_964_, v___x_982_);
v___x_984_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__8));
lean_inc(v_url_983_);
v___x_985_ = l_Lean_Syntax_isOfKind(v_url_983_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
lean_dec(v_url_983_);
lean_dec(v_stx_964_);
v___x_986_ = lean_box(0);
return v___x_986_;
}
else
{
lean_object* v___x_987_; lean_object* v_o_988_; lean_object* v___x_989_; lean_object* v_c_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v_o_988_ = l_Lean_Syntax_getArg(v_stx_964_, v___x_987_);
v___x_989_ = lean_unsigned_to_nat(2u);
v_c_990_ = l_Lean_Syntax_getArg(v_stx_964_, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_991_, 0, v_stx_964_);
lean_ctor_set(v___x_991_, 1, v_o_988_);
lean_ctor_set(v___x_991_, 2, v_url_983_);
lean_ctor_set(v___x_991_, 3, v_c_990_);
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText(lean_object* v_v_997_){
_start:
{
lean_object* v_content_998_; lean_object* v___x_999_; 
v_content_998_ = lean_ctor_get(v_v_997_, 1);
v___x_999_ = l_Lean_TSyntax_getVersoText(v_content_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText___boxed(lean_object* v_v_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Doc_TextView_getVersoText(v_v_1000_);
lean_dec_ref(v_v_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object* v_v_1002_){
_start:
{
lean_object* v_content_1003_; lean_object* v___x_1004_; 
v_content_1003_ = lean_ctor_get(v_v_1002_, 1);
v___x_1004_ = l_Lean_TSyntax_getVersoTextSource(v_content_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource___boxed(lean_object* v_v_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Doc_TextView_getVersoTextSource(v_v_1005_);
lean_dec_ref(v_v_1005_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_of(lean_object* v_stx_1020_){
_start:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__1));
lean_inc(v_stx_1020_);
v___x_1022_ = l_Lean_Syntax_isOfKind(v_stx_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
lean_dec(v_stx_1020_);
v___x_1023_ = lean_box(0);
return v___x_1023_;
}
else
{
lean_object* v___x_1024_; lean_object* v_s_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1024_ = lean_unsigned_to_nat(0u);
v_s_1025_ = l_Lean_Syntax_getArg(v_stx_1020_, v___x_1024_);
v___x_1026_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__3));
lean_inc(v_s_1025_);
v___x_1027_ = l_Lean_Syntax_isOfKind(v_s_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
lean_dec(v_s_1025_);
lean_dec(v_stx_1020_);
v___x_1028_ = lean_box(0);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_stx_1020_);
lean_ctor_set(v___x_1029_, 1, v_s_1025_);
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_EmphView_of(lean_object* v_stx_1044_){
_start:
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = ((lean_object*)(l_Lean_Doc_EmphView_of___closed__1));
lean_inc(v_stx_1044_);
v___x_1046_ = l_Lean_Syntax_isOfKind(v_stx_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; 
lean_dec(v_stx_1044_);
v___x_1047_ = lean_box(0);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; lean_object* v_o_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1048_ = lean_unsigned_to_nat(0u);
v_o_1049_ = l_Lean_Syntax_getArg(v_stx_1044_, v___x_1048_);
v___x_1050_ = ((lean_object*)(l_Lean_Doc_EmphView_of___closed__3));
lean_inc(v_o_1049_);
v___x_1051_ = l_Lean_Syntax_isOfKind(v_o_1049_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; 
lean_dec(v_o_1049_);
lean_dec(v_stx_1044_);
v___x_1052_ = lean_box(0);
return v___x_1052_;
}
else
{
lean_object* v___x_1053_; lean_object* v_c_1054_; uint8_t v___x_1055_; 
v___x_1053_ = lean_unsigned_to_nat(2u);
v_c_1054_ = l_Lean_Syntax_getArg(v_stx_1044_, v___x_1053_);
lean_inc(v_c_1054_);
v___x_1055_ = l_Lean_Syntax_isOfKind(v_c_1054_, v___x_1050_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
lean_dec(v_c_1054_);
lean_dec(v_o_1049_);
lean_dec(v_stx_1044_);
v___x_1056_ = lean_box(0);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v_inl_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = l_Lean_Syntax_getArg(v_stx_1044_, v___x_1057_);
v_inl_1059_ = l_Lean_Syntax_getArgs(v___x_1058_);
lean_dec(v___x_1058_);
v___x_1060_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1060_, 0, v_stx_1044_);
lean_ctor_set(v___x_1060_, 1, v_o_1049_);
lean_ctor_set(v___x_1060_, 2, v_inl_1059_);
lean_ctor_set(v___x_1060_, 3, v_c_1054_);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BoldView_of(lean_object* v_stx_1075_){
_start:
{
lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_Doc_BoldView_of___closed__1));
lean_inc(v_stx_1075_);
v___x_1077_ = l_Lean_Syntax_isOfKind(v_stx_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
lean_dec(v_stx_1075_);
v___x_1078_ = lean_box(0);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; lean_object* v_o_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1079_ = lean_unsigned_to_nat(0u);
v_o_1080_ = l_Lean_Syntax_getArg(v_stx_1075_, v___x_1079_);
v___x_1081_ = ((lean_object*)(l_Lean_Doc_BoldView_of___closed__3));
lean_inc(v_o_1080_);
v___x_1082_ = l_Lean_Syntax_isOfKind(v_o_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
lean_dec(v_o_1080_);
lean_dec(v_stx_1075_);
v___x_1083_ = lean_box(0);
return v___x_1083_;
}
else
{
lean_object* v___x_1084_; lean_object* v_c_1085_; uint8_t v___x_1086_; 
v___x_1084_ = lean_unsigned_to_nat(2u);
v_c_1085_ = l_Lean_Syntax_getArg(v_stx_1075_, v___x_1084_);
lean_inc(v_c_1085_);
v___x_1086_ = l_Lean_Syntax_isOfKind(v_c_1085_, v___x_1081_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
lean_dec(v_c_1085_);
lean_dec(v_o_1080_);
lean_dec(v_stx_1075_);
v___x_1087_ = lean_box(0);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_inl_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1088_ = lean_unsigned_to_nat(1u);
v___x_1089_ = l_Lean_Syntax_getArg(v_stx_1075_, v___x_1088_);
v_inl_1090_ = l_Lean_Syntax_getArgs(v___x_1089_);
lean_dec(v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1091_, 0, v_stx_1075_);
lean_ctor_set(v___x_1091_, 1, v_o_1080_);
lean_ctor_set(v___x_1091_, 2, v_inl_1090_);
lean_ctor_set(v___x_1091_, 3, v_c_1085_);
v___x_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object* v_v_1093_){
_start:
{
lean_object* v_content_1094_; lean_object* v___x_1095_; 
v_content_1094_ = lean_ctor_get(v_v_1093_, 2);
v___x_1095_ = l_Lean_TSyntax_getVersoCode(v_content_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode___boxed(lean_object* v_v_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Doc_CodeView_getVersoCode(v_v_1096_);
lean_dec_ref(v_v_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_of(lean_object* v_stx_1117_){
_start:
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v_stx_1117_);
v___x_1119_ = l_Lean_Syntax_isOfKind(v_stx_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec(v_stx_1117_);
v___x_1120_ = lean_box(0);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; lean_object* v_o_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1121_ = lean_unsigned_to_nat(0u);
v_o_1122_ = l_Lean_Syntax_getArg(v_stx_1117_, v___x_1121_);
v___x_1123_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__3));
lean_inc(v_o_1122_);
v___x_1124_ = l_Lean_Syntax_isOfKind(v_o_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec(v_o_1122_);
lean_dec(v_stx_1117_);
v___x_1125_ = lean_box(0);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; lean_object* v_s_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1126_ = lean_unsigned_to_nat(1u);
v_s_1127_ = l_Lean_Syntax_getArg(v_stx_1117_, v___x_1126_);
v___x_1128_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__5));
lean_inc(v_s_1127_);
v___x_1129_ = l_Lean_Syntax_isOfKind(v_s_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
lean_dec(v_s_1127_);
lean_dec(v_o_1122_);
lean_dec(v_stx_1117_);
v___x_1130_ = lean_box(0);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; lean_object* v_c_1132_; uint8_t v___x_1133_; 
v___x_1131_ = lean_unsigned_to_nat(2u);
v_c_1132_ = l_Lean_Syntax_getArg(v_stx_1117_, v___x_1131_);
lean_inc(v_c_1132_);
v___x_1133_ = l_Lean_Syntax_isOfKind(v_c_1132_, v___x_1123_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v_c_1132_);
lean_dec(v_s_1127_);
lean_dec(v_o_1122_);
lean_dec(v_stx_1117_);
v___x_1134_ = lean_box(0);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1135_, 0, v_stx_1117_);
lean_ctor_set(v___x_1135_, 1, v_o_1122_);
lean_ctor_set(v___x_1135_, 2, v_s_1127_);
lean_ctor_set(v___x_1135_, 3, v_c_1132_);
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object* v_v_1137_){
_start:
{
lean_object* v_code_1138_; lean_object* v___x_1139_; 
v_code_1138_ = lean_ctor_get(v_v_1137_, 2);
v___x_1139_ = l_Lean_Doc_CodeView_getVersoCode(v_code_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode___boxed(lean_object* v_v_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Doc_MathView_getVersoCode(v_v_1140_);
lean_dec_ref(v_v_1140_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_of(lean_object* v_stx_1168_){
_start:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__1));
lean_inc(v_stx_1168_);
v___x_1170_ = l_Lean_Syntax_isOfKind(v_stx_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__3));
lean_inc(v_stx_1168_);
v___x_1172_ = l_Lean_Syntax_isOfKind(v_stx_1168_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec(v_stx_1168_);
v___x_1173_ = lean_box(0);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___y_1177_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = l_Lean_Syntax_getArg(v_stx_1168_, v___x_1174_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__5));
lean_inc(v___x_1175_);
v___x_1197_ = l_Lean_Syntax_isOfKind(v___x_1175_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec(v___x_1175_);
lean_dec(v_stx_1168_);
v___x_1198_ = lean_box(0);
return v___x_1198_;
}
else
{
goto v___jp_1190_;
}
}
else
{
goto v___jp_1190_;
}
v___jp_1176_:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Doc_CodeView_of(v___y_1177_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v___x_1179_; 
lean_dec(v___x_1175_);
lean_dec(v_stx_1168_);
v___x_1179_ = lean_box(0);
return v___x_1179_;
}
else
{
lean_object* v_val_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1189_; 
v_val_1180_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1182_ = v___x_1178_;
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_val_1180_);
lean_dec(v___x_1178_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1184_ = 1;
v___x_1185_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1185_, 0, v_stx_1168_);
lean_ctor_set(v___x_1185_, 1, v___x_1175_);
lean_ctor_set(v___x_1185_, 2, v_val_1180_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*3, v___x_1184_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1185_);
v___x_1187_ = v___x_1182_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
v___jp_1190_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = l_Lean_Syntax_getArg(v_stx_1168_, v___x_1191_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v___x_1192_);
v___x_1194_ = l_Lean_Syntax_isOfKind(v___x_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_dec(v___x_1192_);
lean_dec(v___x_1175_);
lean_dec(v_stx_1168_);
v___x_1195_ = lean_box(0);
return v___x_1195_;
}
else
{
v___y_1177_ = v___x_1192_;
goto v___jp_1176_;
}
}
else
{
v___y_1177_ = v___x_1192_;
goto v___jp_1176_;
}
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = l_Lean_Syntax_getArg(v_stx_1168_, v___x_1199_);
v___x_1201_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__7));
lean_inc(v___x_1200_);
v___x_1202_ = l_Lean_Syntax_isOfKind(v___x_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; 
lean_dec(v___x_1200_);
lean_dec(v_stx_1168_);
v___x_1203_ = lean_box(0);
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = l_Lean_Syntax_getArg(v_stx_1168_, v___x_1204_);
v___x_1206_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v___x_1205_);
v___x_1207_ = l_Lean_Syntax_isOfKind(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
lean_dec(v___x_1205_);
lean_dec(v___x_1200_);
lean_dec(v_stx_1168_);
v___x_1208_ = lean_box(0);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Doc_CodeView_of(v___x_1205_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1210_; 
lean_dec(v___x_1200_);
lean_dec(v_stx_1168_);
v___x_1210_ = lean_box(0);
return v___x_1210_;
}
else
{
lean_object* v_val_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1220_; 
v_val_1211_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1213_ = v___x_1209_;
v_isShared_1214_ = v_isSharedCheck_1220_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_val_1211_);
lean_dec(v___x_1209_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1220_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
uint8_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1215_ = 0;
v___x_1216_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1216_, 0, v_stx_1168_);
lean_ctor_set(v___x_1216_, 1, v___x_1200_);
lean_ctor_set(v___x_1216_, 2, v_val_1211_);
lean_ctor_set_uint8(v___x_1216_, sizeof(void*)*3, v___x_1215_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1216_);
v___x_1218_ = v___x_1213_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkView_of(lean_object* v_stx_1228_){
_start:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_Doc_LinkView_of___closed__1));
lean_inc(v_stx_1228_);
v___x_1230_ = l_Lean_Syntax_isOfKind(v_stx_1228_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_dec(v_stx_1228_);
v___x_1231_ = lean_box(0);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v_tgt_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_unsigned_to_nat(3u);
v_tgt_1233_ = l_Lean_Syntax_getArg(v_stx_1228_, v___x_1232_);
v___x_1234_ = l_Lean_Doc_LinkTargetView_of(v_tgt_1233_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_stx_1228_);
v___x_1235_ = lean_box(0);
return v___x_1235_;
}
else
{
lean_object* v_val_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1251_; 
v_val_1236_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1238_ = v___x_1234_;
v_isShared_1239_ = v_isSharedCheck_1251_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_val_1236_);
lean_dec(v___x_1234_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1251_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v_o_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_c_1245_; lean_object* v_inl_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1240_ = lean_unsigned_to_nat(0u);
v_o_1241_ = l_Lean_Syntax_getArg(v_stx_1228_, v___x_1240_);
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = l_Lean_Syntax_getArg(v_stx_1228_, v___x_1242_);
v___x_1244_ = lean_unsigned_to_nat(2u);
v_c_1245_ = l_Lean_Syntax_getArg(v_stx_1228_, v___x_1244_);
v_inl_1246_ = l_Lean_Syntax_getArgs(v___x_1243_);
lean_dec(v___x_1243_);
v___x_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1247_, 0, v_stx_1228_);
lean_ctor_set(v___x_1247_, 1, v_o_1241_);
lean_ctor_set(v___x_1247_, 2, v_inl_1246_);
lean_ctor_set(v___x_1247_, 3, v_c_1245_);
lean_ctor_set(v___x_1247_, 4, v_val_1236_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1247_);
v___x_1249_ = v___x_1238_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt(lean_object* v_v_1252_){
_start:
{
lean_object* v_alt_1253_; lean_object* v___x_1254_; 
v_alt_1253_ = lean_ctor_get(v_v_1252_, 2);
v___x_1254_ = l_Lean_TSyntax_getVersoImageAlt(v_alt_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt___boxed(lean_object* v_v_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_Doc_ImageView_getAlt(v_v_1255_);
lean_dec_ref(v_v_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_of(lean_object* v_stx_1270_){
_start:
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__1));
lean_inc(v_stx_1270_);
v___x_1272_ = l_Lean_Syntax_isOfKind(v_stx_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
lean_dec(v_stx_1270_);
v___x_1273_ = lean_box(0);
return v___x_1273_;
}
else
{
lean_object* v___x_1274_; lean_object* v_alt_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1274_ = lean_unsigned_to_nat(1u);
v_alt_1275_ = l_Lean_Syntax_getArg(v_stx_1270_, v___x_1274_);
v___x_1276_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__3));
lean_inc(v_alt_1275_);
v___x_1277_ = l_Lean_Syntax_isOfKind(v_alt_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
lean_dec(v_alt_1275_);
lean_dec(v_stx_1270_);
v___x_1278_ = lean_box(0);
return v___x_1278_;
}
else
{
lean_object* v___x_1279_; lean_object* v_tgt_1280_; lean_object* v___x_1281_; 
v___x_1279_ = lean_unsigned_to_nat(3u);
v_tgt_1280_ = l_Lean_Syntax_getArg(v_stx_1270_, v___x_1279_);
v___x_1281_ = l_Lean_Doc_LinkTargetView_of(v_tgt_1280_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_alt_1275_);
lean_dec(v_stx_1270_);
v___x_1282_ = lean_box(0);
return v___x_1282_;
}
else
{
lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1295_; 
v_val_1283_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1295_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1295_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v_o_1288_; lean_object* v___x_1289_; lean_object* v_c_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1287_ = lean_unsigned_to_nat(0u);
v_o_1288_ = l_Lean_Syntax_getArg(v_stx_1270_, v___x_1287_);
v___x_1289_ = lean_unsigned_to_nat(2u);
v_c_1290_ = l_Lean_Syntax_getArg(v_stx_1270_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1291_, 0, v_stx_1270_);
lean_ctor_set(v___x_1291_, 1, v_o_1288_);
lean_ctor_set(v___x_1291_, 2, v_alt_1275_);
lean_ctor_set(v___x_1291_, 3, v_c_1290_);
lean_ctor_set(v___x_1291_, 4, v_val_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1291_);
v___x_1293_ = v___x_1285_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName(lean_object* v_v_1296_){
_start:
{
lean_object* v_name_1297_; lean_object* v___x_1298_; 
v_name_1297_ = lean_ctor_get(v_v_1296_, 2);
v___x_1298_ = l_Lean_TSyntax_getVersoRefName(v_name_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName___boxed(lean_object* v_v_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_Doc_FootnoteView_getName(v_v_1299_);
lean_dec_ref(v_v_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_of(lean_object* v_stx_1308_){
_start:
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = ((lean_object*)(l_Lean_Doc_FootnoteView_of___closed__1));
lean_inc(v_stx_1308_);
v___x_1310_ = l_Lean_Syntax_isOfKind(v_stx_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
lean_dec(v_stx_1308_);
v___x_1311_ = lean_box(0);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; lean_object* v_name_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1312_ = lean_unsigned_to_nat(1u);
v_name_1313_ = l_Lean_Syntax_getArg(v_stx_1308_, v___x_1312_);
v___x_1314_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_1313_);
v___x_1315_ = l_Lean_Syntax_isOfKind(v_name_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_dec(v_name_1313_);
lean_dec(v_stx_1308_);
v___x_1316_ = lean_box(0);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; lean_object* v_o_1318_; lean_object* v___x_1319_; lean_object* v_c_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v_o_1318_ = l_Lean_Syntax_getArg(v_stx_1308_, v___x_1317_);
v___x_1319_ = lean_unsigned_to_nat(2u);
v_c_1320_ = l_Lean_Syntax_getArg(v_stx_1308_, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1321_, 0, v_stx_1308_);
lean_ctor_set(v___x_1321_, 1, v_o_1318_);
lean_ctor_set(v___x_1321_, 2, v_name_1313_);
lean_ctor_set(v___x_1321_, 3, v_c_1320_);
v___x_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinebreakView_of(lean_object* v_stx_1323_){
_start:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
lean_inc(v_stx_1323_);
v___x_1325_ = l_Lean_Syntax_isOfKind(v_stx_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
lean_dec(v_stx_1323_);
v___x_1326_ = lean_box(0);
return v___x_1326_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = l_Lean_Syntax_getArg(v_stx_1323_, v___x_1327_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_stx_1323_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_RoleView_of(lean_object* v_stx_1338_){
_start:
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_Lean_Doc_RoleView_of___closed__1));
lean_inc(v_stx_1338_);
v___x_1340_ = l_Lean_Syntax_isOfKind(v_stx_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
lean_dec(v_stx_1338_);
v___x_1341_ = lean_box(0);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; lean_object* v_name_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1342_ = lean_unsigned_to_nat(1u);
v_name_1343_ = l_Lean_Syntax_getArg(v_stx_1338_, v___x_1342_);
v___x_1344_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_1343_);
v___x_1345_ = l_Lean_Syntax_isOfKind(v_name_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec(v_name_1343_);
lean_dec(v_stx_1338_);
v___x_1346_ = lean_box(0);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; lean_object* v_bo_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v_bc_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1347_ = lean_unsigned_to_nat(0u);
v_bo_1348_ = l_Lean_Syntax_getArg(v_stx_1338_, v___x_1347_);
v___x_1349_ = lean_unsigned_to_nat(2u);
v___x_1350_ = l_Lean_Syntax_getArg(v_stx_1338_, v___x_1349_);
v___x_1351_ = lean_unsigned_to_nat(3u);
v_bc_1352_ = l_Lean_Syntax_getArg(v_stx_1338_, v___x_1351_);
v___x_1353_ = lean_unsigned_to_nat(4u);
v___x_1354_ = l_Lean_Syntax_getArg(v_stx_1338_, v___x_1353_);
lean_inc(v___x_1354_);
v___x_1355_ = l_Lean_Syntax_matchesNull(v___x_1354_, v___x_1342_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; 
v___x_1356_ = l_Lean_Syntax_matchesNull(v___x_1354_, v___x_1347_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; 
lean_dec(v_bc_1352_);
lean_dec(v___x_1350_);
lean_dec(v_bo_1348_);
lean_dec(v_name_1343_);
lean_dec(v_stx_1338_);
v___x_1357_ = lean_box(0);
return v___x_1357_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1358_ = lean_unsigned_to_nat(6u);
v___x_1359_ = l_Lean_Syntax_getArg(v_stx_1338_, v___x_1358_);
v___x_1360_ = l_Lean_Syntax_matchesNull(v___x_1359_, v___x_1347_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
lean_dec(v_bc_1352_);
lean_dec(v___x_1350_);
lean_dec(v_bo_1348_);
lean_dec(v_name_1343_);
lean_dec(v_stx_1338_);
v___x_1361_ = lean_box(0);
return v___x_1361_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_inl_1364_; lean_object* v_args_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1362_ = lean_unsigned_to_nat(5u);
v___x_1363_ = l_Lean_Syntax_getArg(v_stx_1338_, v___x_1362_);
v_inl_1364_ = l_Lean_Syntax_getArgs(v___x_1363_);
lean_dec(v___x_1363_);
v_args_1365_ = l_Lean_Syntax_getArgs(v___x_1350_);
lean_dec(v___x_1350_);
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1367_, 0, v_stx_1338_);
lean_ctor_set(v___x_1367_, 1, v_bo_1348_);
lean_ctor_set(v___x_1367_, 2, v_name_1343_);
lean_ctor_set(v___x_1367_, 3, v_args_1365_);
lean_ctor_set(v___x_1367_, 4, v_bc_1352_);
lean_ctor_set(v___x_1367_, 5, v___x_1366_);
lean_ctor_set(v___x_1367_, 6, v_inl_1364_);
v___x_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1369_ = lean_unsigned_to_nat(6u);
v___x_1370_ = l_Lean_Syntax_getArg(v_stx_1338_, v___x_1369_);
lean_inc(v___x_1370_);
v___x_1371_ = l_Lean_Syntax_matchesNull(v___x_1370_, v___x_1342_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec(v___x_1370_);
lean_dec(v___x_1354_);
lean_dec(v_bc_1352_);
lean_dec(v___x_1350_);
lean_dec(v_bo_1348_);
lean_dec(v_name_1343_);
lean_dec(v_stx_1338_);
v___x_1372_ = lean_box(0);
return v___x_1372_;
}
else
{
lean_object* v_so_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_sc_1376_; lean_object* v_inl_1377_; lean_object* v_args_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_so_1373_ = l_Lean_Syntax_getArg(v___x_1354_, v___x_1347_);
lean_dec(v___x_1354_);
v___x_1374_ = lean_unsigned_to_nat(5u);
v___x_1375_ = l_Lean_Syntax_getArg(v_stx_1338_, v___x_1374_);
v_sc_1376_ = l_Lean_Syntax_getArg(v___x_1370_, v___x_1347_);
lean_dec(v___x_1370_);
v_inl_1377_ = l_Lean_Syntax_getArgs(v___x_1375_);
lean_dec(v___x_1375_);
v_args_1378_ = l_Lean_Syntax_getArgs(v___x_1350_);
lean_dec(v___x_1350_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_so_1373_);
lean_ctor_set(v___x_1379_, 1, v_sc_1376_);
v___x_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
v___x_1381_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1381_, 0, v_stx_1338_);
lean_ctor_set(v___x_1381_, 1, v_bo_1348_);
lean_ctor_set(v___x_1381_, 2, v_name_1343_);
lean_ctor_set(v___x_1381_, 3, v_args_1378_);
lean_ctor_set(v___x_1381_, 4, v_bc_1352_);
lean_ctor_set(v___x_1381_, 5, v___x_1380_);
lean_ctor_set(v___x_1381_, 6, v_inl_1377_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
return v___x_1382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___impl(lean_object* v_x_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = lean_obj_tag_nat(v_x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___impl___boxed(lean_object* v_x_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Doc_InlineView_ctorIdx___impl(v_x_1385_);
lean_dec_ref(v_x_1385_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___redArg(lean_object* v_t_1387_, lean_object* v_k_1388_){
_start:
{
lean_object* v_view_1389_; lean_object* v___x_1390_; 
v_view_1389_ = lean_ctor_get(v_t_1387_, 0);
lean_inc_ref(v_view_1389_);
lean_dec_ref(v_t_1387_);
v___x_1390_ = lean_apply_1(v_k_1388_, v_view_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim(lean_object* v_motive_1391_, lean_object* v_ctorIdx_1392_, lean_object* v_t_1393_, lean_object* v_h_1394_, lean_object* v_k_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1393_, v_k_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___boxed(lean_object* v_motive_1397_, lean_object* v_ctorIdx_1398_, lean_object* v_t_1399_, lean_object* v_h_1400_, lean_object* v_k_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Doc_InlineView_ctorElim(v_motive_1397_, v_ctorIdx_1398_, v_t_1399_, v_h_1400_, v_k_1401_);
lean_dec(v_ctorIdx_1398_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim___redArg(lean_object* v_t_1403_, lean_object* v_text_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1403_, v_text_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim(lean_object* v_motive_1406_, lean_object* v_t_1407_, lean_object* v_h_1408_, lean_object* v_text_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1407_, v_text_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim___redArg(lean_object* v_t_1411_, lean_object* v_emph_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1411_, v_emph_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim(lean_object* v_motive_1414_, lean_object* v_t_1415_, lean_object* v_h_1416_, lean_object* v_emph_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1415_, v_emph_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim___redArg(lean_object* v_t_1419_, lean_object* v_bold_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1419_, v_bold_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim(lean_object* v_motive_1422_, lean_object* v_t_1423_, lean_object* v_h_1424_, lean_object* v_bold_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1423_, v_bold_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim___redArg(lean_object* v_t_1427_, lean_object* v_code_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1427_, v_code_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim(lean_object* v_motive_1430_, lean_object* v_t_1431_, lean_object* v_h_1432_, lean_object* v_code_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1431_, v_code_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim___redArg(lean_object* v_t_1435_, lean_object* v_math_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1435_, v_math_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim(lean_object* v_motive_1438_, lean_object* v_t_1439_, lean_object* v_h_1440_, lean_object* v_math_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1439_, v_math_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim___redArg(lean_object* v_t_1443_, lean_object* v_link_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1443_, v_link_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim(lean_object* v_motive_1446_, lean_object* v_t_1447_, lean_object* v_h_1448_, lean_object* v_link_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1447_, v_link_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim___redArg(lean_object* v_t_1451_, lean_object* v_image_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1451_, v_image_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim(lean_object* v_motive_1454_, lean_object* v_t_1455_, lean_object* v_h_1456_, lean_object* v_image_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1455_, v_image_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim___redArg(lean_object* v_t_1459_, lean_object* v_footnote_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1459_, v_footnote_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim(lean_object* v_motive_1462_, lean_object* v_t_1463_, lean_object* v_h_1464_, lean_object* v_footnote_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1463_, v_footnote_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim___redArg(lean_object* v_t_1467_, lean_object* v_linebreak_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1467_, v_linebreak_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim(lean_object* v_motive_1470_, lean_object* v_t_1471_, lean_object* v_h_1472_, lean_object* v_linebreak_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1471_, v_linebreak_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim___redArg(lean_object* v_t_1475_, lean_object* v_role_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1475_, v_role_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim(lean_object* v_motive_1478_, lean_object* v_t_1479_, lean_object* v_h_1480_, lean_object* v_role_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1479_, v_role_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTextViewInlineView___lam__0(lean_object* v_view_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v_view_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeEmphViewInlineView___lam__0(lean_object* v_view_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_view_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBoldViewInlineView___lam__0(lean_object* v_view_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_view_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeViewInlineView___lam__0(lean_object* v_view_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_view_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMathViewInlineView___lam__0(lean_object* v_view_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_view_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkViewInlineView___lam__0(lean_object* v_view_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_view_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeImageViewInlineView___lam__0(lean_object* v_view_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_view_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0(lean_object* v_view_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_view_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0(lean_object* v_view_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_view_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeRoleViewInlineView___lam__0(lean_object* v_view_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_view_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx(lean_object* v_x_1527_){
_start:
{
lean_object* v_view_1528_; lean_object* v_stx_1529_; 
v_view_1528_ = lean_ctor_get(v_x_1527_, 0);
v_stx_1529_ = lean_ctor_get(v_view_1528_, 0);
lean_inc(v_stx_1529_);
return v_stx_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx___boxed(lean_object* v_x_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Doc_InlineView_stx(v_x_1530_);
lean_dec_ref(v_x_1530_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_of(lean_object* v_stx_1532_){
_start:
{
lean_object* v___x_1533_; 
lean_inc(v_stx_1532_);
v___x_1533_ = l_Lean_Doc_TextView_of(v_stx_1532_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1534_; 
lean_inc(v_stx_1532_);
v___x_1534_ = l_Lean_Doc_EmphView_of(v_stx_1532_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_stx_1532_);
v___x_1535_ = l_Lean_Doc_BoldView_of(v_stx_1532_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v___x_1536_; 
lean_inc(v_stx_1532_);
v___x_1536_ = l_Lean_Doc_CodeView_of(v_stx_1532_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v___x_1537_; 
lean_inc(v_stx_1532_);
v___x_1537_ = l_Lean_Doc_MathView_of(v_stx_1532_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v___x_1538_; 
lean_inc(v_stx_1532_);
v___x_1538_ = l_Lean_Doc_LinkView_of(v_stx_1532_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1539_; 
lean_inc(v_stx_1532_);
v___x_1539_ = l_Lean_Doc_ImageView_of(v_stx_1532_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v___x_1540_; 
lean_inc(v_stx_1532_);
v___x_1540_ = l_Lean_Doc_FootnoteView_of(v_stx_1532_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1541_; 
lean_inc(v_stx_1532_);
v___x_1541_ = l_Lean_Doc_LinebreakView_of(v_stx_1532_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Doc_RoleView_of(v_stx_1532_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_box(0);
return v___x_1543_;
}
else
{
lean_object* v_val_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1552_; 
v_val_1544_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1546_ = v___x_1542_;
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_val_1544_);
lean_dec(v___x_1542_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_val_1544_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1548_);
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
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
lean_object* v_val_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v_stx_1532_);
v_val_1553_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v___x_1541_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_val_1553_);
lean_dec(v___x_1541_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1557_, 0, v_val_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
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
lean_object* v_val_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_stx_1532_);
v_val_1562_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1564_ = v___x_1540_;
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_val_1562_);
lean_dec(v___x_1540_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1566_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_val_1562_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1566_);
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
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
lean_object* v_val_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_stx_1532_);
v_val_1571_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1573_ = v___x_1539_;
v_isShared_1574_ = v_isSharedCheck_1579_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_val_1571_);
lean_dec(v___x_1539_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1579_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_val_1571_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1575_);
v___x_1577_ = v___x_1573_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
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
lean_object* v_val_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_stx_1532_);
v_val_1580_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1582_ = v___x_1538_;
v_isShared_1583_ = v_isSharedCheck_1588_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_val_1580_);
lean_dec(v___x_1538_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1588_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1584_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_val_1580_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1584_);
v___x_1586_ = v___x_1582_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
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
lean_object* v_val_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v_stx_1532_);
v_val_1589_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1591_ = v___x_1537_;
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_val_1589_);
lean_dec(v___x_1537_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1593_, 0, v_val_1589_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1593_);
v___x_1595_ = v___x_1591_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
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
lean_object* v_val_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_stx_1532_);
v_val_1598_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1600_ = v___x_1536_;
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_val_1598_);
lean_dec(v___x_1536_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_val_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1602_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
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
lean_object* v_val_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_stx_1532_);
v_val_1607_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1609_ = v___x_1535_;
v_isShared_1610_ = v_isSharedCheck_1615_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_val_1607_);
lean_dec(v___x_1535_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1615_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_val_1607_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1611_);
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
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
lean_object* v_val_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v_stx_1532_);
v_val_1616_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1618_ = v___x_1534_;
v_isShared_1619_ = v_isSharedCheck_1624_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_val_1616_);
lean_dec(v___x_1534_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1624_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_val_1616_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1620_);
v___x_1622_ = v___x_1618_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
lean_object* v_val_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v_stx_1532_);
v_val_1625_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1627_ = v___x_1533_;
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_val_1625_);
lean_dec(v___x_1533_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_val_1625_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(uint32_t v_a_1634_, lean_object* v_x_1635_){
_start:
{
if (lean_obj_tag(v_x_1635_) == 0)
{
uint8_t v___x_1636_; 
v___x_1636_ = 0;
return v___x_1636_;
}
else
{
lean_object* v_head_1637_; lean_object* v_tail_1638_; uint32_t v___x_1639_; uint8_t v___x_1640_; 
v_head_1637_ = lean_ctor_get(v_x_1635_, 0);
v_tail_1638_ = lean_ctor_get(v_x_1635_, 1);
v___x_1639_ = lean_unbox_uint32(v_head_1637_);
v___x_1640_ = lean_uint32_dec_eq(v_a_1634_, v___x_1639_);
if (v___x_1640_ == 0)
{
v_x_1635_ = v_tail_1638_;
goto _start;
}
else
{
return v___x_1640_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0___boxed(lean_object* v_a_1642_, lean_object* v_x_1643_){
_start:
{
uint32_t v_a_boxed_1644_; uint8_t v_res_1645_; lean_object* v_r_1646_; 
v_a_boxed_1644_ = lean_unbox_uint32(v_a_1642_);
lean_dec(v_a_1642_);
v_res_1645_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v_a_boxed_1644_, v_x_1643_);
lean_dec(v_x_1643_);
v_r_1646_ = lean_box(v_res_1645_);
return v_r_1646_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = 43;
v___x_1662_ = lean_box_uint32(v___x_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__5(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_box(0);
v___x_1664_ = l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1;
v___x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v___x_1663_);
return v___x_1665_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = 45;
v___x_1667_ = lean_box_uint32(v___x_1666_);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__6(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__5, &l_Lean_Doc_UnorderedListItemView_of___closed__5_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__5);
v___x_1669_ = l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1;
v___x_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v___x_1668_);
return v___x_1670_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = 42;
v___x_1672_ = lean_box_uint32(v___x_1671_);
return v___x_1672_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__7(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__6, &l_Lean_Doc_UnorderedListItemView_of___closed__6_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__6);
v___x_1674_ = l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1;
v___x_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v___x_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of(lean_object* v_stx_1676_){
_start:
{
lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__2));
lean_inc(v_stx_1676_);
v___x_1678_ = l_Lean_Syntax_isOfKind(v_stx_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_dec(v_stx_1676_);
v___x_1679_ = lean_box(0);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; lean_object* v_m_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1680_ = lean_unsigned_to_nat(0u);
v_m_1681_ = l_Lean_Syntax_getArg(v_stx_1676_, v___x_1680_);
v___x_1682_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__4));
lean_inc(v_m_1681_);
v___x_1683_ = l_Lean_Syntax_isOfKind(v_m_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; 
lean_dec(v_m_1681_);
lean_dec(v_stx_1676_);
v___x_1684_ = lean_box(0);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1685_ = l_Lean_TSyntax_getVersoDelimiter(v_m_1681_);
v___x_1686_ = lean_string_utf8_byte_size(v___x_1685_);
v___x_1687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1680_);
lean_ctor_set(v___x_1687_, 2, v___x_1686_);
v___x_1688_ = l_String_Slice_Pos_get_x3f(v___x_1687_, v___x_1680_);
lean_dec_ref_known(v___x_1687_, 3);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v___x_1689_; 
lean_dec(v_m_1681_);
lean_dec(v_stx_1676_);
v___x_1689_ = lean_box(0);
return v___x_1689_;
}
else
{
lean_object* v_val_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1705_; 
v_val_1690_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1692_ = v___x_1688_;
v_isShared_1693_ = v_isSharedCheck_1705_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_val_1690_);
lean_dec(v___x_1688_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1705_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; uint32_t v___x_1695_; uint8_t v___x_1696_; 
v___x_1694_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__7, &l_Lean_Doc_UnorderedListItemView_of___closed__7_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__7);
v___x_1695_ = lean_unbox_uint32(v_val_1690_);
lean_dec(v_val_1690_);
v___x_1696_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v___x_1695_, v___x_1694_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; 
lean_del_object(v___x_1692_);
lean_dec(v_m_1681_);
lean_dec(v_stx_1676_);
v___x_1697_ = lean_box(0);
return v___x_1697_;
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_bs_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1698_ = lean_unsigned_to_nat(1u);
v___x_1699_ = l_Lean_Syntax_getArg(v_stx_1676_, v___x_1698_);
v_bs_1700_ = l_Lean_Syntax_getArgs(v___x_1699_);
lean_dec(v___x_1699_);
v___x_1701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1701_, 0, v_stx_1676_);
lean_ctor_set(v___x_1701_, 1, v_m_1681_);
lean_ctor_set(v___x_1701_, 2, v_bs_1700_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1701_);
v___x_1703_ = v___x_1692_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(lean_object* v_s_1706_, lean_object* v_pos_1707_){
_start:
{
lean_object* v_str_1708_; lean_object* v_startInclusive_1709_; lean_object* v_endExclusive_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v_decide_1714_; 
v_str_1708_ = lean_ctor_get(v_s_1706_, 0);
v_startInclusive_1709_ = lean_ctor_get(v_s_1706_, 1);
v_endExclusive_1710_ = lean_ctor_get(v_s_1706_, 2);
v___x_1711_ = lean_nat_add(v_startInclusive_1709_, v_pos_1707_);
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = lean_nat_sub(v_endExclusive_1710_, v___x_1711_);
v_decide_1714_ = lean_nat_dec_eq(v___x_1712_, v___x_1713_);
lean_dec(v___x_1713_);
if (v_decide_1714_ == 0)
{
uint32_t v___x_1715_; uint32_t v___x_1716_; uint8_t v___x_1717_; 
v___x_1715_ = lean_string_utf8_get_fast(v_str_1708_, v___x_1711_);
v___x_1716_ = 48;
v___x_1717_ = lean_uint32_dec_le(v___x_1716_, v___x_1715_);
if (v___x_1717_ == 0)
{
lean_dec(v___x_1711_);
return v_pos_1707_;
}
else
{
uint32_t v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = 57;
v___x_1719_ = lean_uint32_dec_le(v___x_1715_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_dec(v___x_1711_);
return v_pos_1707_;
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1720_ = lean_string_utf8_next_fast(v_str_1708_, v___x_1711_);
v___x_1721_ = lean_nat_sub(v___x_1720_, v___x_1711_);
lean_dec(v___x_1711_);
v___x_1722_ = lean_nat_add(v_pos_1707_, v___x_1721_);
lean_dec(v___x_1721_);
v___x_1723_ = lean_unsigned_to_nat(1u);
v___x_1724_ = lean_nat_add(v_pos_1707_, v___x_1723_);
v___x_1725_ = lean_nat_dec_le(v___x_1724_, v___x_1722_);
lean_dec(v___x_1724_);
if (v___x_1725_ == 0)
{
lean_dec(v___x_1722_);
return v_pos_1707_;
}
else
{
lean_dec(v_pos_1707_);
v_pos_1707_ = v___x_1722_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_1711_);
return v_pos_1707_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0___boxed(lean_object* v_s_1727_, lean_object* v_pos_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v_s_1727_, v_pos_1728_);
lean_dec_ref(v_s_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_number(lean_object* v_v_1730_){
_start:
{
lean_object* v_marker_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1746_; 
v_marker_1731_ = lean_ctor_get(v_v_1730_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_v_1730_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; lean_object* v_unused_1748_; 
v_unused_1747_ = lean_ctor_get(v_v_1730_, 2);
lean_dec(v_unused_1747_);
v_unused_1748_ = lean_ctor_get(v_v_1730_, 0);
lean_dec(v_unused_1748_);
v___x_1733_ = v_v_1730_;
v_isShared_1734_ = v_isSharedCheck_1746_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_marker_1731_);
lean_dec(v_v_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1746_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1735_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_1731_);
lean_dec(v_marker_1731_);
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_string_utf8_byte_size(v___x_1735_);
lean_inc_ref(v___x_1735_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 2, v___x_1737_);
lean_ctor_set(v___x_1733_, 1, v___x_1736_);
lean_ctor_set(v___x_1733_, 0, v___x_1735_);
v___x_1739_ = v___x_1733_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1740_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v___x_1739_, v___x_1736_);
lean_dec_ref(v___x_1739_);
v___x_1741_ = lean_string_utf8_extract_fast(v___x_1735_, v___x_1736_, v___x_1740_);
lean_dec(v___x_1740_);
lean_dec_ref(v___x_1735_);
v___x_1742_ = lean_string_utf8_byte_size(v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1741_);
lean_ctor_set(v___x_1743_, 1, v___x_1736_);
lean_ctor_set(v___x_1743_, 2, v___x_1742_);
v___x_1744_ = l_String_Slice_toNat_x3f(v___x_1743_);
lean_dec_ref_known(v___x_1743_, 3);
return v___x_1744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_of(lean_object* v_stx_1749_){
_start:
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__2));
lean_inc(v_stx_1749_);
v___x_1751_ = l_Lean_Syntax_isOfKind(v_stx_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
lean_dec(v_stx_1749_);
v___x_1752_ = lean_box(0);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v_m_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1753_ = lean_unsigned_to_nat(0u);
v_m_1754_ = l_Lean_Syntax_getArg(v_stx_1749_, v___x_1753_);
v___x_1755_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__4));
lean_inc(v_m_1754_);
v___x_1756_ = l_Lean_Syntax_isOfKind(v_m_1754_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_dec(v_m_1754_);
lean_dec(v_stx_1749_);
v___x_1757_ = lean_box(0);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1758_ = l_Lean_TSyntax_getVersoDelimiter(v_m_1754_);
v___x_1759_ = lean_string_utf8_byte_size(v___x_1758_);
v___x_1760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1753_);
lean_ctor_set(v___x_1760_, 2, v___x_1759_);
v___x_1761_ = l_String_Slice_Pos_get_x3f(v___x_1760_, v___x_1753_);
lean_dec_ref_known(v___x_1760_, 3);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v___x_1762_; 
lean_dec(v_m_1754_);
lean_dec(v_stx_1749_);
v___x_1762_ = lean_box(0);
return v___x_1762_;
}
else
{
lean_object* v_val_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1782_; 
v_val_1763_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1765_ = v___x_1761_;
v_isShared_1766_ = v_isSharedCheck_1782_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_val_1763_);
lean_dec(v___x_1761_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1782_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
uint32_t v___x_1767_; uint32_t v___x_1768_; uint8_t v___x_1769_; 
v___x_1767_ = 48;
v___x_1768_ = lean_unbox_uint32(v_val_1763_);
v___x_1769_ = lean_uint32_dec_le(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; 
lean_del_object(v___x_1765_);
lean_dec(v_val_1763_);
lean_dec(v_m_1754_);
lean_dec(v_stx_1749_);
v___x_1770_ = lean_box(0);
return v___x_1770_;
}
else
{
uint32_t v___x_1771_; uint32_t v___x_1772_; uint8_t v___x_1773_; 
v___x_1771_ = 57;
v___x_1772_ = lean_unbox_uint32(v_val_1763_);
lean_dec(v_val_1763_);
v___x_1773_ = lean_uint32_dec_le(v___x_1772_, v___x_1771_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_del_object(v___x_1765_);
lean_dec(v_m_1754_);
lean_dec(v_stx_1749_);
v___x_1774_ = lean_box(0);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v_bs_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = l_Lean_Syntax_getArg(v_stx_1749_, v___x_1775_);
v_bs_1777_ = l_Lean_Syntax_getArgs(v___x_1776_);
lean_dec(v___x_1776_);
v___x_1778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1778_, 0, v_stx_1749_);
lean_ctor_set(v___x_1778_, 1, v_m_1754_);
lean_ctor_set(v___x_1778_, 2, v_bs_1777_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1778_);
v___x_1780_ = v___x_1765_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescItemView_of(lean_object* v_stx_1790_){
_start:
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_Lean_Doc_DescItemView_of___closed__1));
lean_inc(v_stx_1790_);
v___x_1792_ = l_Lean_Syntax_isOfKind(v_stx_1790_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; 
lean_dec(v_stx_1790_);
v___x_1793_ = lean_box(0);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v_marker_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_desc_1800_; lean_object* v_term_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1794_ = lean_unsigned_to_nat(0u);
v_marker_1795_ = l_Lean_Syntax_getArg(v_stx_1790_, v___x_1794_);
v___x_1796_ = lean_unsigned_to_nat(1u);
v___x_1797_ = l_Lean_Syntax_getArg(v_stx_1790_, v___x_1796_);
v___x_1798_ = lean_unsigned_to_nat(2u);
v___x_1799_ = l_Lean_Syntax_getArg(v_stx_1790_, v___x_1798_);
v_desc_1800_ = l_Lean_Syntax_getArgs(v___x_1799_);
lean_dec(v___x_1799_);
v_term_1801_ = l_Lean_Syntax_getArgs(v___x_1797_);
lean_dec(v___x_1797_);
v___x_1802_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1802_, 0, v_stx_1790_);
lean_ctor_set(v___x_1802_, 1, v_marker_1795_);
lean_ctor_set(v___x_1802_, 2, v_term_1801_);
lean_ctor_set(v___x_1802_, 3, v_desc_1800_);
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ParaView_of(lean_object* v_stx_1819_){
_start:
{
lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_Lean_Doc_ParaView_of___closed__2));
lean_inc(v_stx_1819_);
v___x_1821_ = l_Lean_Syntax_isOfKind(v_stx_1819_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
lean_dec(v_stx_1819_);
v___x_1822_ = lean_box(0);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v_inl_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = l_Lean_Syntax_getArg(v_stx_1819_, v___x_1823_);
v_inl_1825_ = l_Lean_Syntax_getArgs(v___x_1824_);
lean_dec(v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_stx_1819_);
lean_ctor_set(v___x_1826_, 1, v_inl_1825_);
v___x_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(size_t v_sz_1828_, size_t v_i_1829_, lean_object* v_bs_1830_){
_start:
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_usize_dec_lt(v_i_1829_, v_sz_1828_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_bs_1830_);
return v___x_1832_;
}
else
{
lean_object* v_v_1833_; lean_object* v___x_1834_; 
v_v_1833_ = lean_array_uget_borrowed(v_bs_1830_, v_i_1829_);
lean_inc(v_v_1833_);
v___x_1834_ = l_Lean_Doc_UnorderedListItemView_of(v_v_1833_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v___x_1835_; 
lean_dec_ref(v_bs_1830_);
v___x_1835_ = lean_box(0);
return v___x_1835_;
}
else
{
lean_object* v_val_1836_; lean_object* v___x_1837_; lean_object* v_bs_x27_1838_; size_t v___x_1839_; size_t v___x_1840_; lean_object* v___x_1841_; 
v_val_1836_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_val_1836_);
lean_dec_ref_known(v___x_1834_, 1);
v___x_1837_ = lean_unsigned_to_nat(0u);
v_bs_x27_1838_ = lean_array_uset(v_bs_1830_, v_i_1829_, v___x_1837_);
v___x_1839_ = ((size_t)1ULL);
v___x_1840_ = lean_usize_add(v_i_1829_, v___x_1839_);
v___x_1841_ = lean_array_uset(v_bs_x27_1838_, v_i_1829_, v_val_1836_);
v_i_1829_ = v___x_1840_;
v_bs_1830_ = v___x_1841_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0___boxed(lean_object* v_sz_1843_, lean_object* v_i_1844_, lean_object* v_bs_1845_){
_start:
{
size_t v_sz_boxed_1846_; size_t v_i_boxed_1847_; lean_object* v_res_1848_; 
v_sz_boxed_1846_ = lean_unbox_usize(v_sz_1843_);
lean_dec(v_sz_1843_);
v_i_boxed_1847_ = lean_unbox_usize(v_i_1844_);
lean_dec(v_i_1844_);
v_res_1848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_boxed_1846_, v_i_boxed_1847_, v_bs_1845_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListView_of(lean_object* v_stx_1856_){
_start:
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_Doc_UnorderedListView_of___closed__1));
lean_inc(v_stx_1856_);
v___x_1858_ = l_Lean_Syntax_isOfKind(v_stx_1856_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
lean_dec(v_stx_1856_);
v___x_1859_ = lean_box(0);
return v___x_1859_;
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v_items_1862_; size_t v_sz_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = l_Lean_Syntax_getArg(v_stx_1856_, v___x_1860_);
v_items_1862_ = l_Lean_Syntax_getArgs(v___x_1861_);
lean_dec(v___x_1861_);
v_sz_1863_ = lean_array_size(v_items_1862_);
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_1863_, v___x_1864_, v_items_1862_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v___x_1866_; 
lean_dec(v_stx_1856_);
v___x_1866_ = lean_box(0);
return v___x_1866_;
}
else
{
lean_object* v_val_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1875_; 
v_val_1867_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1869_ = v___x_1865_;
v_isShared_1870_ = v_isSharedCheck_1875_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_val_1867_);
lean_dec(v___x_1865_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1875_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v_stx_1856_);
lean_ctor_set(v___x_1871_, 1, v_val_1867_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1871_);
v___x_1873_ = v___x_1869_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(size_t v_sz_1876_, size_t v_i_1877_, lean_object* v_bs_1878_){
_start:
{
uint8_t v___x_1879_; 
v___x_1879_ = lean_usize_dec_lt(v_i_1877_, v_sz_1876_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_bs_1878_);
return v___x_1880_;
}
else
{
lean_object* v_v_1881_; lean_object* v___x_1882_; 
v_v_1881_ = lean_array_uget_borrowed(v_bs_1878_, v_i_1877_);
lean_inc(v_v_1881_);
v___x_1882_ = l_Lean_Doc_OrderedListItemView_of(v_v_1881_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v___x_1883_; 
lean_dec_ref(v_bs_1878_);
v___x_1883_ = lean_box(0);
return v___x_1883_;
}
else
{
lean_object* v_val_1884_; lean_object* v___x_1885_; lean_object* v_bs_x27_1886_; size_t v___x_1887_; size_t v___x_1888_; lean_object* v___x_1889_; 
v_val_1884_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_val_1884_);
lean_dec_ref_known(v___x_1882_, 1);
v___x_1885_ = lean_unsigned_to_nat(0u);
v_bs_x27_1886_ = lean_array_uset(v_bs_1878_, v_i_1877_, v___x_1885_);
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_add(v_i_1877_, v___x_1887_);
v___x_1889_ = lean_array_uset(v_bs_x27_1886_, v_i_1877_, v_val_1884_);
v_i_1877_ = v___x_1888_;
v_bs_1878_ = v___x_1889_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0___boxed(lean_object* v_sz_1891_, lean_object* v_i_1892_, lean_object* v_bs_1893_){
_start:
{
size_t v_sz_boxed_1894_; size_t v_i_boxed_1895_; lean_object* v_res_1896_; 
v_sz_boxed_1894_ = lean_unbox_usize(v_sz_1891_);
lean_dec(v_sz_1891_);
v_i_boxed_1895_ = lean_unbox_usize(v_i_1892_);
lean_dec(v_i_1892_);
v_res_1896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_boxed_1894_, v_i_boxed_1895_, v_bs_1893_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListView_of(lean_object* v_stx_1904_){
_start:
{
lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = ((lean_object*)(l_Lean_Doc_OrderedListView_of___closed__1));
lean_inc(v_stx_1904_);
v___x_1906_ = l_Lean_Syntax_isOfKind(v_stx_1904_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
lean_dec(v_stx_1904_);
v___x_1907_ = lean_box(0);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v_items_1910_; size_t v_sz_1911_; size_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = l_Lean_Syntax_getArg(v_stx_1904_, v___x_1908_);
v_items_1910_ = l_Lean_Syntax_getArgs(v___x_1909_);
lean_dec(v___x_1909_);
v_sz_1911_ = lean_array_size(v_items_1910_);
v___x_1912_ = ((size_t)0ULL);
v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_1911_, v___x_1912_, v_items_1910_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v___x_1914_; 
lean_dec(v_stx_1904_);
v___x_1914_ = lean_box(0);
return v___x_1914_;
}
else
{
lean_object* v_val_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1932_; 
v_val_1915_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1917_ = v___x_1913_;
v_isShared_1918_ = v_isSharedCheck_1932_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_val_1915_);
lean_dec(v___x_1913_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1932_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___y_1920_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = lean_array_get_size(v_val_1915_);
v___x_1928_ = lean_nat_dec_lt(v___x_1908_, v___x_1927_);
if (v___x_1928_ == 0)
{
goto v___jp_1925_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = lean_array_fget_borrowed(v_val_1915_, v___x_1908_);
lean_inc(v___x_1929_);
v___x_1930_ = l_Lean_Doc_OrderedListItemView_number(v___x_1929_);
if (lean_obj_tag(v___x_1930_) == 0)
{
goto v___jp_1925_;
}
else
{
lean_object* v_val_1931_; 
v_val_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_val_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___y_1920_ = v_val_1931_;
goto v___jp_1919_;
}
}
v___jp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1921_, 0, v_stx_1904_);
lean_ctor_set(v___x_1921_, 1, v___y_1920_);
lean_ctor_set(v___x_1921_, 2, v_val_1915_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1921_);
v___x_1923_ = v___x_1917_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
v___jp_1925_:
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_unsigned_to_nat(1u);
v___y_1920_ = v___x_1926_;
goto v___jp_1919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(size_t v_sz_1933_, size_t v_i_1934_, lean_object* v_bs_1935_){
_start:
{
uint8_t v___x_1936_; 
v___x_1936_ = lean_usize_dec_lt(v_i_1934_, v_sz_1933_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_bs_1935_);
return v___x_1937_;
}
else
{
lean_object* v_v_1938_; lean_object* v___x_1939_; 
v_v_1938_ = lean_array_uget_borrowed(v_bs_1935_, v_i_1934_);
lean_inc(v_v_1938_);
v___x_1939_ = l_Lean_Doc_DescItemView_of(v_v_1938_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v___x_1940_; 
lean_dec_ref(v_bs_1935_);
v___x_1940_ = lean_box(0);
return v___x_1940_;
}
else
{
lean_object* v_val_1941_; lean_object* v___x_1942_; lean_object* v_bs_x27_1943_; size_t v___x_1944_; size_t v___x_1945_; lean_object* v___x_1946_; 
v_val_1941_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1942_ = lean_unsigned_to_nat(0u);
v_bs_x27_1943_ = lean_array_uset(v_bs_1935_, v_i_1934_, v___x_1942_);
v___x_1944_ = ((size_t)1ULL);
v___x_1945_ = lean_usize_add(v_i_1934_, v___x_1944_);
v___x_1946_ = lean_array_uset(v_bs_x27_1943_, v_i_1934_, v_val_1941_);
v_i_1934_ = v___x_1945_;
v_bs_1935_ = v___x_1946_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0___boxed(lean_object* v_sz_1948_, lean_object* v_i_1949_, lean_object* v_bs_1950_){
_start:
{
size_t v_sz_boxed_1951_; size_t v_i_boxed_1952_; lean_object* v_res_1953_; 
v_sz_boxed_1951_ = lean_unbox_usize(v_sz_1948_);
lean_dec(v_sz_1948_);
v_i_boxed_1952_ = lean_unbox_usize(v_i_1949_);
lean_dec(v_i_1949_);
v_res_1953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_boxed_1951_, v_i_boxed_1952_, v_bs_1950_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescListView_of(lean_object* v_stx_1961_){
_start:
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = ((lean_object*)(l_Lean_Doc_DescListView_of___closed__1));
lean_inc(v_stx_1961_);
v___x_1963_ = l_Lean_Syntax_isOfKind(v_stx_1961_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
lean_dec(v_stx_1961_);
v___x_1964_ = lean_box(0);
return v___x_1964_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v_items_1967_; size_t v_sz_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = l_Lean_Syntax_getArg(v_stx_1961_, v___x_1965_);
v_items_1967_ = l_Lean_Syntax_getArgs(v___x_1966_);
lean_dec(v___x_1966_);
v_sz_1968_ = lean_array_size(v_items_1967_);
v___x_1969_ = ((size_t)0ULL);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_1968_, v___x_1969_, v_items_1967_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; 
lean_dec(v_stx_1961_);
v___x_1971_ = lean_box(0);
return v___x_1971_;
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1980_; 
v_val_1972_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1974_ = v___x_1970_;
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v___x_1970_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_stx_1961_);
lean_ctor_set(v___x_1976_, 1, v_val_1972_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1976_);
v___x_1978_ = v___x_1974_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockquoteView_of(lean_object* v_stx_1988_){
_start:
{
lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = ((lean_object*)(l_Lean_Doc_BlockquoteView_of___closed__1));
lean_inc(v_stx_1988_);
v___x_1990_ = l_Lean_Syntax_isOfKind(v_stx_1988_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; 
lean_dec(v_stx_1988_);
v___x_1991_ = lean_box(0);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v_gt_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v_bs_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1992_ = lean_unsigned_to_nat(0u);
v_gt_1993_ = l_Lean_Syntax_getArg(v_stx_1988_, v___x_1992_);
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = l_Lean_Syntax_getArg(v_stx_1988_, v___x_1994_);
v_bs_1996_ = l_Lean_Syntax_getArgs(v___x_1995_);
lean_dec(v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1997_, 0, v_stx_1988_);
lean_ctor_set(v___x_1997_, 1, v_gt_1993_);
lean_ctor_set(v___x_1997_, 2, v_bs_1996_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
return v___x_1998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object* v_v_1999_){
_start:
{
lean_object* v_content_2000_; lean_object* v___x_2001_; 
v_content_2000_ = lean_ctor_get(v_v_1999_, 4);
v___x_2001_ = l_Lean_TSyntax_getVersoCodeBlock(v_content_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock___boxed(lean_object* v_v_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_v_2002_);
lean_dec_ref(v_v_2002_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_of(lean_object* v_stx_2023_){
_start:
{
lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__1));
lean_inc(v_stx_2023_);
v___x_2025_ = l_Lean_Syntax_isOfKind(v_stx_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
lean_dec(v_stx_2023_);
v___x_2026_ = lean_box(0);
return v___x_2026_;
}
else
{
lean_object* v___x_2027_; lean_object* v_openFence_2028_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v_name_2051_; lean_object* v_args_2052_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2027_ = lean_unsigned_to_nat(0u);
v_openFence_2028_ = l_Lean_Syntax_getArg(v_stx_2023_, v___x_2027_);
v___x_2065_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__5));
lean_inc(v_openFence_2028_);
v___x_2066_ = l_Lean_Syntax_isOfKind(v_openFence_2028_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
lean_dec(v_openFence_2028_);
lean_dec(v_stx_2023_);
v___x_2067_ = lean_box(0);
return v___x_2067_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = l_Lean_Syntax_getArg(v_stx_2023_, v___x_2068_);
v___x_2070_ = l_Lean_Syntax_isNone(v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2069_);
v___x_2072_ = l_Lean_Syntax_matchesNull(v___x_2069_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec(v___x_2069_);
lean_dec(v_openFence_2028_);
lean_dec(v_stx_2023_);
v___x_2073_ = lean_box(0);
return v___x_2073_;
}
else
{
lean_object* v_name_2074_; 
v_name_2074_ = l_Lean_Syntax_getArg(v___x_2069_, v___x_2027_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2074_);
v___x_2081_ = l_Lean_Syntax_isOfKind(v_name_2074_, v___x_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; 
lean_dec(v_name_2074_);
lean_dec(v___x_2069_);
lean_dec(v_openFence_2028_);
lean_dec(v_stx_2023_);
v___x_2082_ = lean_box(0);
return v___x_2082_;
}
else
{
goto v___jp_2075_;
}
}
else
{
goto v___jp_2075_;
}
v___jp_2075_:
{
lean_object* v___x_2076_; lean_object* v_args_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2076_ = l_Lean_Syntax_getArg(v___x_2069_, v___x_2068_);
lean_dec(v___x_2069_);
v_args_2077_ = l_Lean_Syntax_getArgs(v___x_2076_);
lean_dec(v___x_2076_);
v___x_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2078_, 0, v_name_2074_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_args_2077_);
v_name_2051_ = v___x_2078_;
v_args_2052_ = v___x_2079_;
goto v___jp_2050_;
}
}
}
else
{
lean_object* v___x_2083_; 
lean_dec(v___x_2069_);
v___x_2083_ = lean_box(0);
v_name_2051_ = v___x_2083_;
v_args_2052_ = v___x_2083_;
goto v___jp_2050_;
}
}
v___jp_2029_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2034_, 0, v_stx_2023_);
lean_ctor_set(v___x_2034_, 1, v_openFence_2028_);
lean_ctor_set(v___x_2034_, 2, v___y_2031_);
lean_ctor_set(v___x_2034_, 3, v___y_2033_);
lean_ctor_set(v___x_2034_, 4, v___y_2030_);
lean_ctor_set(v___x_2034_, 5, v___y_2032_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
return v___x_2035_;
}
v___jp_2036_:
{
if (lean_obj_tag(v___y_2037_) == 0)
{
lean_object* v___x_2041_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0));
v___y_2030_ = v___y_2040_;
v___y_2031_ = v___y_2038_;
v___y_2032_ = v___y_2039_;
v___y_2033_ = v___x_2041_;
goto v___jp_2029_;
}
else
{
lean_object* v_val_2042_; 
v_val_2042_ = lean_ctor_get(v___y_2037_, 0);
lean_inc(v_val_2042_);
lean_dec_ref_known(v___y_2037_, 1);
v___y_2030_ = v___y_2040_;
v___y_2031_ = v___y_2038_;
v___y_2032_ = v___y_2039_;
v___y_2033_ = v_val_2042_;
goto v___jp_2029_;
}
}
v___jp_2043_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v___y_2047_);
v___x_2049_ = l_Lean_Syntax_setInfo(v___x_2048_, v___y_2046_);
v___y_2037_ = v___y_2044_;
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___y_2047_;
v___y_2040_ = v___x_2049_;
goto v___jp_2036_;
}
v___jp_2050_:
{
lean_object* v___x_2053_; lean_object* v_s_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2053_ = lean_unsigned_to_nat(2u);
v_s_2054_ = l_Lean_Syntax_getArg(v_stx_2023_, v___x_2053_);
v___x_2055_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__3));
lean_inc(v_s_2054_);
v___x_2056_ = l_Lean_Syntax_isOfKind(v_s_2054_, v___x_2055_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; 
lean_dec(v_s_2054_);
lean_dec(v_args_2052_);
lean_dec(v_name_2051_);
lean_dec(v_openFence_2028_);
lean_dec(v_stx_2023_);
v___x_2057_ = lean_box(0);
return v___x_2057_;
}
else
{
lean_object* v___x_2058_; lean_object* v_closeFence_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2058_ = lean_unsigned_to_nat(3u);
v_closeFence_2059_ = l_Lean_Syntax_getArg(v_stx_2023_, v___x_2058_);
v___x_2060_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__5));
lean_inc(v_closeFence_2059_);
v___x_2061_ = l_Lean_Syntax_isOfKind(v_closeFence_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
lean_dec(v_closeFence_2059_);
lean_dec(v_s_2054_);
lean_dec(v_args_2052_);
lean_dec(v_name_2051_);
lean_dec(v_openFence_2028_);
lean_dec(v_stx_2023_);
v___x_2062_ = lean_box(0);
return v___x_2062_;
}
else
{
uint8_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = 0;
v___x_2064_ = l_Lean_Syntax_getPos_x3f(v_s_2054_, v___x_2063_);
if (lean_obj_tag(v___x_2064_) == 0)
{
v___y_2044_ = v_args_2052_;
v___y_2045_ = v_name_2051_;
v___y_2046_ = v_s_2054_;
v___y_2047_ = v_closeFence_2059_;
goto v___jp_2043_;
}
else
{
lean_dec_ref_known(v___x_2064_, 1);
if (v___x_2025_ == 0)
{
v___y_2044_ = v_args_2052_;
v___y_2045_ = v_name_2051_;
v___y_2046_ = v_s_2054_;
v___y_2047_ = v_closeFence_2059_;
goto v___jp_2043_;
}
else
{
v___y_2037_ = v_args_2052_;
v___y_2038_ = v_name_2051_;
v___y_2039_ = v_closeFence_2059_;
v___y_2040_ = v_s_2054_;
goto v___jp_2036_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DirectiveView_of(lean_object* v_stx_2097_){
_start:
{
lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2098_ = ((lean_object*)(l_Lean_Doc_DirectiveView_of___closed__1));
lean_inc(v_stx_2097_);
v___x_2099_ = l_Lean_Syntax_isOfKind(v_stx_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; 
lean_dec(v_stx_2097_);
v___x_2100_ = lean_box(0);
return v___x_2100_;
}
else
{
lean_object* v___x_2101_; lean_object* v_opener_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2101_ = lean_unsigned_to_nat(0u);
v_opener_2102_ = l_Lean_Syntax_getArg(v_stx_2097_, v___x_2101_);
v___x_2103_ = ((lean_object*)(l_Lean_Doc_DirectiveView_of___closed__3));
lean_inc(v_opener_2102_);
v___x_2104_ = l_Lean_Syntax_isOfKind(v_opener_2102_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
lean_dec(v_opener_2102_);
lean_dec(v_stx_2097_);
v___x_2105_ = lean_box(0);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; lean_object* v_name_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2106_ = lean_unsigned_to_nat(1u);
v_name_2107_ = l_Lean_Syntax_getArg(v_stx_2097_, v___x_2106_);
v___x_2108_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2107_);
v___x_2109_ = l_Lean_Syntax_isOfKind(v_name_2107_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec(v_name_2107_);
lean_dec(v_opener_2102_);
lean_dec(v_stx_2097_);
v___x_2110_ = lean_box(0);
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; lean_object* v_closer_2112_; uint8_t v___x_2113_; 
v___x_2111_ = lean_unsigned_to_nat(4u);
v_closer_2112_ = l_Lean_Syntax_getArg(v_stx_2097_, v___x_2111_);
lean_inc(v_closer_2112_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v_closer_2112_, v___x_2103_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec(v_closer_2112_);
lean_dec(v_name_2107_);
lean_dec(v_opener_2102_);
lean_dec(v_stx_2097_);
v___x_2114_ = lean_box(0);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_bs_2119_; lean_object* v_args_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2115_ = lean_unsigned_to_nat(2u);
v___x_2116_ = l_Lean_Syntax_getArg(v_stx_2097_, v___x_2115_);
v___x_2117_ = lean_unsigned_to_nat(3u);
v___x_2118_ = l_Lean_Syntax_getArg(v_stx_2097_, v___x_2117_);
v_bs_2119_ = l_Lean_Syntax_getArgs(v___x_2118_);
lean_dec(v___x_2118_);
v_args_2120_ = l_Lean_Syntax_getArgs(v___x_2116_);
lean_dec(v___x_2116_);
v___x_2121_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2121_, 0, v_stx_2097_);
lean_ctor_set(v___x_2121_, 1, v_opener_2102_);
lean_ctor_set(v___x_2121_, 2, v_name_2107_);
lean_ctor_set(v___x_2121_, 3, v_args_2120_);
lean_ctor_set(v___x_2121_, 4, v_bs_2119_);
lean_ctor_set(v___x_2121_, 5, v_closer_2112_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CommandView_of(lean_object* v_stx_2130_){
_start:
{
lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2131_ = ((lean_object*)(l_Lean_Doc_CommandView_of___closed__1));
lean_inc(v_stx_2130_);
v___x_2132_ = l_Lean_Syntax_isOfKind(v_stx_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; 
lean_dec(v_stx_2130_);
v___x_2133_ = lean_box(0);
return v___x_2133_;
}
else
{
lean_object* v___x_2134_; lean_object* v_name_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2134_ = lean_unsigned_to_nat(1u);
v_name_2135_ = l_Lean_Syntax_getArg(v_stx_2130_, v___x_2134_);
v___x_2136_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2135_);
v___x_2137_ = l_Lean_Syntax_isOfKind(v_name_2135_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; 
lean_dec(v_name_2135_);
lean_dec(v_stx_2130_);
v___x_2138_ = lean_box(0);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; lean_object* v_braceOpen_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v_braceClose_2144_; lean_object* v_args_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2139_ = lean_unsigned_to_nat(0u);
v_braceOpen_2140_ = l_Lean_Syntax_getArg(v_stx_2130_, v___x_2139_);
v___x_2141_ = lean_unsigned_to_nat(2u);
v___x_2142_ = l_Lean_Syntax_getArg(v_stx_2130_, v___x_2141_);
v___x_2143_ = lean_unsigned_to_nat(3u);
v_braceClose_2144_ = l_Lean_Syntax_getArg(v_stx_2130_, v___x_2143_);
v_args_2145_ = l_Lean_Syntax_getArgs(v___x_2142_);
lean_dec(v___x_2142_);
v___x_2146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2146_, 0, v_stx_2130_);
lean_ctor_set(v___x_2146_, 1, v_braceOpen_2140_);
lean_ctor_set(v___x_2146_, 2, v_name_2135_);
lean_ctor_set(v___x_2146_, 3, v_args_2145_);
lean_ctor_set(v___x_2146_, 4, v_braceClose_2144_);
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_HeaderView_of(lean_object* v_stx_2161_){
_start:
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_Doc_HeaderView_of___closed__1));
lean_inc(v_stx_2161_);
v___x_2163_ = l_Lean_Syntax_isOfKind(v_stx_2161_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; 
lean_dec(v_stx_2161_);
v___x_2164_ = lean_box(0);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; lean_object* v_marker_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2165_ = lean_unsigned_to_nat(0u);
v_marker_2166_ = l_Lean_Syntax_getArg(v_stx_2161_, v___x_2165_);
v___x_2167_ = ((lean_object*)(l_Lean_Doc_HeaderView_of___closed__3));
lean_inc(v_marker_2166_);
v___x_2168_ = l_Lean_Syntax_isOfKind(v_marker_2166_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; 
lean_dec(v_marker_2166_);
lean_dec(v_stx_2161_);
v___x_2169_ = lean_box(0);
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v_content_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = l_Lean_Syntax_getArg(v_stx_2161_, v___x_2170_);
v_content_2172_ = l_Lean_Syntax_getArgs(v___x_2171_);
lean_dec(v___x_2171_);
v___x_2173_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_2166_);
v___x_2174_ = lean_string_length(v___x_2173_);
lean_dec_ref(v___x_2173_);
v___x_2175_ = lean_nat_sub(v___x_2174_, v___x_2170_);
v___x_2176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2176_, 0, v_stx_2161_);
lean_ctor_set(v___x_2176_, 1, v_marker_2166_);
lean_ctor_set(v___x_2176_, 2, v___x_2175_);
lean_ctor_set(v___x_2176_, 3, v_content_2172_);
v___x_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
return v___x_2177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName(lean_object* v_v_2178_){
_start:
{
lean_object* v_name_2179_; lean_object* v___x_2180_; 
v_name_2179_ = lean_ctor_get(v_v_2178_, 2);
v___x_2180_ = l_Lean_TSyntax_getVersoRefName(v_name_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName___boxed(lean_object* v_v_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_Doc_LinkRefView_getName(v_v_2181_);
lean_dec_ref(v_v_2181_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object* v_v_2183_){
_start:
{
lean_object* v_url_2184_; lean_object* v___x_2185_; 
v_url_2184_ = lean_ctor_get(v_v_2183_, 4);
v___x_2185_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_url_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl___boxed(lean_object* v_v_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Doc_LinkRefView_getUrl(v_v_2186_);
lean_dec_ref(v_v_2186_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_of(lean_object* v_stx_2201_){
_start:
{
lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__1));
lean_inc(v_stx_2201_);
v___x_2203_ = l_Lean_Syntax_isOfKind(v_stx_2201_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; 
lean_dec(v_stx_2201_);
v___x_2204_ = lean_box(0);
return v___x_2204_;
}
else
{
lean_object* v___x_2205_; lean_object* v_name_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2205_ = lean_unsigned_to_nat(1u);
v_name_2206_ = l_Lean_Syntax_getArg(v_stx_2201_, v___x_2205_);
v___x_2207_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_2206_);
v___x_2208_ = l_Lean_Syntax_isOfKind(v_name_2206_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; 
lean_dec(v_name_2206_);
lean_dec(v_stx_2201_);
v___x_2209_ = lean_box(0);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v_url_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2210_ = lean_unsigned_to_nat(3u);
v_url_2211_ = l_Lean_Syntax_getArg(v_stx_2201_, v___x_2210_);
v___x_2212_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__3));
lean_inc(v_url_2211_);
v___x_2213_ = l_Lean_Syntax_isOfKind(v_url_2211_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_dec(v_url_2211_);
lean_dec(v_name_2206_);
lean_dec(v_stx_2201_);
v___x_2214_ = lean_box(0);
return v___x_2214_;
}
else
{
lean_object* v___x_2215_; lean_object* v_opener_2216_; lean_object* v___x_2217_; lean_object* v_closer_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2215_ = lean_unsigned_to_nat(0u);
v_opener_2216_ = l_Lean_Syntax_getArg(v_stx_2201_, v___x_2215_);
v___x_2217_ = lean_unsigned_to_nat(2u);
v_closer_2218_ = l_Lean_Syntax_getArg(v_stx_2201_, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2219_, 0, v_stx_2201_);
lean_ctor_set(v___x_2219_, 1, v_opener_2216_);
lean_ctor_set(v___x_2219_, 2, v_name_2206_);
lean_ctor_set(v___x_2219_, 3, v_closer_2218_);
lean_ctor_set(v___x_2219_, 4, v_url_2211_);
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object* v_v_2221_){
_start:
{
lean_object* v_name_2222_; lean_object* v___x_2223_; 
v_name_2222_ = lean_ctor_get(v_v_2221_, 2);
v___x_2223_ = l_Lean_TSyntax_getVersoRefName(v_name_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName___boxed(lean_object* v_v_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_Doc_FootnoteRefView_getName(v_v_2224_);
lean_dec_ref(v_v_2224_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_of(lean_object* v_stx_2233_){
_start:
{
lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_Lean_Doc_FootnoteRefView_of___closed__1));
lean_inc(v_stx_2233_);
v___x_2235_ = l_Lean_Syntax_isOfKind(v_stx_2233_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; 
lean_dec(v_stx_2233_);
v___x_2236_ = lean_box(0);
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; lean_object* v_name_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2237_ = lean_unsigned_to_nat(1u);
v_name_2238_ = l_Lean_Syntax_getArg(v_stx_2233_, v___x_2237_);
v___x_2239_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_2238_);
v___x_2240_ = l_Lean_Syntax_isOfKind(v_name_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
lean_dec(v_name_2238_);
lean_dec(v_stx_2233_);
v___x_2241_ = lean_box(0);
return v___x_2241_;
}
else
{
lean_object* v___x_2242_; lean_object* v_opener_2243_; lean_object* v___x_2244_; lean_object* v_closer_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v_content_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2242_ = lean_unsigned_to_nat(0u);
v_opener_2243_ = l_Lean_Syntax_getArg(v_stx_2233_, v___x_2242_);
v___x_2244_ = lean_unsigned_to_nat(2u);
v_closer_2245_ = l_Lean_Syntax_getArg(v_stx_2233_, v___x_2244_);
v___x_2246_ = lean_unsigned_to_nat(3u);
v___x_2247_ = l_Lean_Syntax_getArg(v_stx_2233_, v___x_2246_);
v_content_2248_ = l_Lean_Syntax_getArgs(v___x_2247_);
lean_dec(v___x_2247_);
v___x_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2249_, 0, v_stx_2233_);
lean_ctor_set(v___x_2249_, 1, v_opener_2243_);
lean_ctor_set(v___x_2249_, 2, v_name_2238_);
lean_ctor_set(v___x_2249_, 3, v_closer_2245_);
lean_ctor_set(v___x_2249_, 4, v_content_2248_);
v___x_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(size_t v_sz_2251_, size_t v_i_2252_, lean_object* v_bs_2253_){
_start:
{
uint8_t v___x_2254_; 
v___x_2254_ = lean_usize_dec_lt(v_i_2252_, v_sz_2251_);
if (v___x_2254_ == 0)
{
return v_bs_2253_;
}
else
{
lean_object* v_v_2255_; lean_object* v___x_2256_; lean_object* v_bs_x27_2257_; size_t v___x_2258_; size_t v___x_2259_; lean_object* v___x_2260_; 
v_v_2255_ = lean_array_uget(v_bs_2253_, v_i_2252_);
v___x_2256_ = lean_unsigned_to_nat(0u);
v_bs_x27_2257_ = lean_array_uset(v_bs_2253_, v_i_2252_, v___x_2256_);
v___x_2258_ = ((size_t)1ULL);
v___x_2259_ = lean_usize_add(v_i_2252_, v___x_2258_);
v___x_2260_ = lean_array_uset(v_bs_x27_2257_, v_i_2252_, v_v_2255_);
v_i_2252_ = v___x_2259_;
v_bs_2253_ = v___x_2260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0___boxed(lean_object* v_sz_2262_, lean_object* v_i_2263_, lean_object* v_bs_2264_){
_start:
{
size_t v_sz_boxed_2265_; size_t v_i_boxed_2266_; lean_object* v_res_2267_; 
v_sz_boxed_2265_ = lean_unbox_usize(v_sz_2262_);
lean_dec(v_sz_2262_);
v_i_boxed_2266_ = lean_unbox_usize(v_i_2263_);
lean_dec(v_i_2263_);
v_res_2267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_boxed_2265_, v_i_boxed_2266_, v_bs_2264_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields(lean_object* v_v_2268_){
_start:
{
lean_object* v_contents_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; size_t v_sz_2273_; size_t v___x_2274_; lean_object* v___x_2275_; 
v_contents_2269_ = lean_ctor_get(v_v_2268_, 2);
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = l_Lean_Syntax_getArg(v_contents_2269_, v___x_2270_);
v___x_2272_ = l_Lean_Syntax_getSepArgs(v___x_2271_);
lean_dec(v___x_2271_);
v_sz_2273_ = lean_array_size(v___x_2272_);
v___x_2274_ = ((size_t)0ULL);
v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_2273_, v___x_2274_, v___x_2272_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields___boxed(lean_object* v_v_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_Doc_MetadataView_fields(v_v_2276_);
lean_dec_ref(v_v_2276_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_of(lean_object* v_stx_2292_){
_start:
{
lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = ((lean_object*)(l_Lean_Doc_MetadataView_of___closed__1));
lean_inc(v_stx_2292_);
v___x_2294_ = l_Lean_Syntax_isOfKind(v_stx_2292_, v___x_2293_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; 
lean_dec(v_stx_2292_);
v___x_2295_ = lean_box(0);
return v___x_2295_;
}
else
{
lean_object* v___x_2296_; lean_object* v_contents_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2296_ = lean_unsigned_to_nat(1u);
v_contents_2297_ = l_Lean_Syntax_getArg(v_stx_2292_, v___x_2296_);
v___x_2298_ = ((lean_object*)(l_Lean_Doc_MetadataView_of___closed__4));
lean_inc(v_contents_2297_);
v___x_2299_ = l_Lean_Syntax_isOfKind(v_contents_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; 
lean_dec(v_contents_2297_);
lean_dec(v_stx_2292_);
v___x_2300_ = lean_box(0);
return v___x_2300_;
}
else
{
lean_object* v___x_2301_; lean_object* v_opener_2302_; lean_object* v___x_2303_; lean_object* v_closer_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2301_ = lean_unsigned_to_nat(0u);
v_opener_2302_ = l_Lean_Syntax_getArg(v_stx_2292_, v___x_2301_);
v___x_2303_ = lean_unsigned_to_nat(2u);
v_closer_2304_ = l_Lean_Syntax_getArg(v_stx_2292_, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2305_, 0, v_stx_2292_);
lean_ctor_set(v___x_2305_, 1, v_opener_2302_);
lean_ctor_set(v___x_2305_, 2, v_contents_2297_);
lean_ctor_set(v___x_2305_, 3, v_closer_2304_);
v___x_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___impl(lean_object* v_x_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_obj_tag_nat(v_x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___impl___boxed(lean_object* v_x_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Doc_BlockView_ctorIdx___impl(v_x_2309_);
lean_dec_ref(v_x_2309_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___redArg(lean_object* v_t_2311_, lean_object* v_k_2312_){
_start:
{
lean_object* v_view_2313_; lean_object* v___x_2314_; 
v_view_2313_ = lean_ctor_get(v_t_2311_, 0);
lean_inc_ref(v_view_2313_);
lean_dec_ref(v_t_2311_);
v___x_2314_ = lean_apply_1(v_k_2312_, v_view_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim(lean_object* v_motive_2315_, lean_object* v_ctorIdx_2316_, lean_object* v_t_2317_, lean_object* v_h_2318_, lean_object* v_k_2319_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2317_, v_k_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___boxed(lean_object* v_motive_2321_, lean_object* v_ctorIdx_2322_, lean_object* v_t_2323_, lean_object* v_h_2324_, lean_object* v_k_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Doc_BlockView_ctorElim(v_motive_2321_, v_ctorIdx_2322_, v_t_2323_, v_h_2324_, v_k_2325_);
lean_dec(v_ctorIdx_2322_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim___redArg(lean_object* v_t_2327_, lean_object* v_para_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2327_, v_para_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim(lean_object* v_motive_2330_, lean_object* v_t_2331_, lean_object* v_h_2332_, lean_object* v_para_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2331_, v_para_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim___redArg(lean_object* v_t_2335_, lean_object* v_ul_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2335_, v_ul_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim(lean_object* v_motive_2338_, lean_object* v_t_2339_, lean_object* v_h_2340_, lean_object* v_ul_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2339_, v_ul_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim___redArg(lean_object* v_t_2343_, lean_object* v_ol_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2343_, v_ol_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim(lean_object* v_motive_2346_, lean_object* v_t_2347_, lean_object* v_h_2348_, lean_object* v_ol_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2347_, v_ol_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim___redArg(lean_object* v_t_2351_, lean_object* v_dl_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2351_, v_dl_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim(lean_object* v_motive_2354_, lean_object* v_t_2355_, lean_object* v_h_2356_, lean_object* v_dl_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2355_, v_dl_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim___redArg(lean_object* v_t_2359_, lean_object* v_blockquote_2360_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2359_, v_blockquote_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim(lean_object* v_motive_2362_, lean_object* v_t_2363_, lean_object* v_h_2364_, lean_object* v_blockquote_2365_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2363_, v_blockquote_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim___redArg(lean_object* v_t_2367_, lean_object* v_codeblock_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2367_, v_codeblock_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim(lean_object* v_motive_2370_, lean_object* v_t_2371_, lean_object* v_h_2372_, lean_object* v_codeblock_2373_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2371_, v_codeblock_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim___redArg(lean_object* v_t_2375_, lean_object* v_directive_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2375_, v_directive_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim(lean_object* v_motive_2378_, lean_object* v_t_2379_, lean_object* v_h_2380_, lean_object* v_directive_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2379_, v_directive_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim___redArg(lean_object* v_t_2383_, lean_object* v_command_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2383_, v_command_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim(lean_object* v_motive_2386_, lean_object* v_t_2387_, lean_object* v_h_2388_, lean_object* v_command_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2387_, v_command_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim___redArg(lean_object* v_t_2391_, lean_object* v_header_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2391_, v_header_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim(lean_object* v_motive_2394_, lean_object* v_t_2395_, lean_object* v_h_2396_, lean_object* v_header_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2395_, v_header_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim___redArg(lean_object* v_t_2399_, lean_object* v_linkRef_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2399_, v_linkRef_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim(lean_object* v_motive_2402_, lean_object* v_t_2403_, lean_object* v_h_2404_, lean_object* v_linkRef_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2403_, v_linkRef_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim___redArg(lean_object* v_t_2407_, lean_object* v_footnoteRef_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2407_, v_footnoteRef_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim(lean_object* v_motive_2410_, lean_object* v_t_2411_, lean_object* v_h_2412_, lean_object* v_footnoteRef_2413_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2411_, v_footnoteRef_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim___redArg(lean_object* v_t_2415_, lean_object* v_metadata_2416_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2415_, v_metadata_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim(lean_object* v_motive_2418_, lean_object* v_t_2419_, lean_object* v_h_2420_, lean_object* v_metadata_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2419_, v_metadata_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeParaViewBlockView___lam__0(lean_object* v_view_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v_view_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0(lean_object* v_view_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2432_, 0, v_view_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0(lean_object* v_view_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2436_, 0, v_view_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDescListViewBlockView___lam__0(lean_object* v_view_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_view_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0(lean_object* v_view_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2444_, 0, v_view_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0(lean_object* v_view_2447_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2448_, 0, v_view_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0(lean_object* v_view_2451_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2452_, 0, v_view_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCommandViewBlockView___lam__0(lean_object* v_view_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_view_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___lam__0(lean_object* v_view_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2460_, 0, v_view_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0(lean_object* v_view_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2464_, 0, v_view_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0(lean_object* v_view_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2468_, 0, v_view_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___lam__0(lean_object* v_view_2471_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_view_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx(lean_object* v_x_2475_){
_start:
{
lean_object* v_view_2476_; lean_object* v_stx_2477_; 
v_view_2476_ = lean_ctor_get(v_x_2475_, 0);
v_stx_2477_ = lean_ctor_get(v_view_2476_, 0);
lean_inc(v_stx_2477_);
return v_stx_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx___boxed(lean_object* v_x_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Doc_BlockView_stx(v_x_2478_);
lean_dec_ref(v_x_2478_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_of(lean_object* v_stx_2480_){
_start:
{
lean_object* v___x_2481_; 
lean_inc(v_stx_2480_);
v___x_2481_ = l_Lean_Doc_ParaView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2482_; 
lean_inc(v_stx_2480_);
v___x_2482_ = l_Lean_Doc_UnorderedListView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v___x_2483_; 
lean_inc(v_stx_2480_);
v___x_2483_ = l_Lean_Doc_OrderedListView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v___x_2484_; 
lean_inc(v_stx_2480_);
v___x_2484_ = l_Lean_Doc_DescListView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v___x_2485_; 
lean_inc(v_stx_2480_);
v___x_2485_ = l_Lean_Doc_BlockquoteView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v___x_2486_; 
lean_inc(v_stx_2480_);
v___x_2486_ = l_Lean_Doc_CodeBlockView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v___x_2487_; 
lean_inc(v_stx_2480_);
v___x_2487_ = l_Lean_Doc_DirectiveView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v___x_2488_; 
lean_inc(v_stx_2480_);
v___x_2488_ = l_Lean_Doc_CommandView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v___x_2489_; 
lean_inc(v_stx_2480_);
v___x_2489_ = l_Lean_Doc_HeaderView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v___x_2490_; 
lean_inc(v_stx_2480_);
v___x_2490_ = l_Lean_Doc_LinkRefView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2491_; 
lean_inc(v_stx_2480_);
v___x_2491_ = l_Lean_Doc_FootnoteRefView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_Doc_MetadataView_of(v_stx_2480_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_box(0);
return v___x_2493_;
}
else
{
lean_object* v_val_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2502_; 
v_val_2494_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2496_ = v___x_2492_;
v_isShared_2497_ = v_isSharedCheck_2502_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_val_2494_);
lean_dec(v___x_2492_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2502_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2498_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_val_2494_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v___x_2498_);
v___x_2500_ = v___x_2496_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v_val_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v_stx_2480_);
v_val_2503_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2505_ = v___x_2491_;
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_val_2503_);
lean_dec(v___x_2491_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_val_2503_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v___x_2507_);
v___x_2509_ = v___x_2505_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
else
{
lean_object* v_val_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_stx_2480_);
v_val_2512_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2514_ = v___x_2490_;
v_isShared_2515_ = v_isSharedCheck_2520_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_val_2512_);
lean_dec(v___x_2490_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2520_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_val_2512_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_object* v_val_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_stx_2480_);
v_val_2521_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2523_ = v___x_2489_;
v_isShared_2524_ = v_isSharedCheck_2529_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_val_2521_);
lean_dec(v___x_2489_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2529_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2525_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_val_2521_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2525_);
v___x_2527_ = v___x_2523_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v_val_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_stx_2480_);
v_val_2530_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2532_ = v___x_2488_;
v_isShared_2533_ = v_isSharedCheck_2538_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_val_2530_);
lean_dec(v___x_2488_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2538_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2534_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_val_2530_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2534_);
v___x_2536_ = v___x_2532_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2534_);
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
else
{
lean_object* v_val_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v_stx_2480_);
v_val_2539_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2541_ = v___x_2487_;
v_isShared_2542_ = v_isSharedCheck_2547_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_val_2539_);
lean_dec(v___x_2487_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2547_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2543_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_val_2539_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2543_);
v___x_2545_ = v___x_2541_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
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
else
{
lean_object* v_val_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_stx_2480_);
v_val_2548_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2550_ = v___x_2486_;
v_isShared_2551_ = v_isSharedCheck_2556_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_val_2548_);
lean_dec(v___x_2486_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2556_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2552_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_val_2548_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2552_);
v___x_2554_ = v___x_2550_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v_val_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v_stx_2480_);
v_val_2557_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2559_ = v___x_2485_;
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_val_2557_);
lean_dec(v___x_2485_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2561_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_val_2557_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2561_);
v___x_2563_ = v___x_2559_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v_val_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v_stx_2480_);
v_val_2566_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2568_ = v___x_2484_;
v_isShared_2569_ = v_isSharedCheck_2574_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_val_2566_);
lean_dec(v___x_2484_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2574_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_val_2566_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2570_);
v___x_2572_ = v___x_2568_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v_val_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v_stx_2480_);
v_val_2575_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2577_ = v___x_2483_;
v_isShared_2578_ = v_isSharedCheck_2583_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_val_2575_);
lean_dec(v___x_2483_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2583_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2579_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_val_2575_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2579_);
v___x_2581_ = v___x_2577_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v_val_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v_stx_2480_);
v_val_2584_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2586_ = v___x_2482_;
v_isShared_2587_ = v_isSharedCheck_2592_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_val_2584_);
lean_dec(v___x_2482_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2592_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2588_, 0, v_val_2584_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2588_);
v___x_2590_ = v___x_2586_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v_val_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_stx_2480_);
v_val_2593_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2595_ = v___x_2481_;
v_isShared_2596_ = v_isSharedCheck_2601_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_val_2593_);
lean_dec(v___x_2481_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2601_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v_val_2593_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoInline_view(lean_object* v_stx_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Doc_InlineView_of(v_stx_2602_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = ((lean_object*)(l_Lean_Doc_instInhabitedInlineView_default));
return v___x_2604_;
}
else
{
lean_object* v_val_2605_; 
v_val_2605_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_val_2605_);
lean_dec_ref_known(v___x_2603_, 1);
return v_val_2605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoBlock_view(lean_object* v_stx_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_Doc_BlockView_of(v_stx_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v___x_2608_; 
v___x_2608_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlockView_default));
return v___x_2608_;
}
else
{
lean_object* v_val_2609_; 
v_val_2609_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_val_2609_);
lean_dec_ref_known(v___x_2607_, 1);
return v_val_2609_;
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
