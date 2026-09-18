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
lean_object* l_Lean_TSyntax_getString(lean_object*);
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
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_strLitOfContent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_strLitOfContent___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_migrateInlines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_migrateInlines___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_migrateBlocks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_migrateBlocks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(lean_object* v_tok_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Syntax_getHeadInfo(v_tok_323_);
switch(lean_obj_tag(v___x_324_))
{
case 0:
{
lean_object* v_leading_325_; lean_object* v_trailing_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_360_; 
v_leading_325_ = lean_ctor_get(v___x_324_, 0);
v_trailing_326_ = lean_ctor_get(v___x_324_, 2);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; lean_object* v_unused_362_; 
v_unused_361_ = lean_ctor_get(v___x_324_, 3);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v___x_324_, 1);
lean_dec(v_unused_362_);
v___x_328_ = v___x_324_;
v_isShared_329_ = v_isSharedCheck_360_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_trailing_326_);
lean_inc(v_leading_325_);
lean_dec(v___x_324_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_360_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint8_t v___x_330_; lean_object* v___x_331_; 
v___x_330_ = 0;
v___x_331_ = l_Lean_Syntax_getPos_x3f(v_tok_323_, v___x_330_);
if (lean_obj_tag(v___x_331_) == 1)
{
lean_object* v_val_332_; lean_object* v___x_333_; 
v_val_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = l_Lean_Syntax_getTailPos_x3f(v_tok_323_, v___x_330_);
if (lean_obj_tag(v___x_333_) == 1)
{
lean_object* v_val_334_; lean_object* v_str_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_355_; 
v_val_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v___x_333_, 1);
v_str_335_ = lean_ctor_get(v_leading_325_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_leading_325_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; lean_object* v_unused_357_; 
v_unused_356_ = lean_ctor_get(v_leading_325_, 2);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_leading_325_, 1);
lean_dec(v_unused_357_);
v___x_337_ = v_leading_325_;
v_isShared_338_ = v_isSharedCheck_355_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_str_335_);
lean_dec(v_leading_325_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_355_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
lean_inc_n(v_val_332_, 2);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 2, v_val_332_);
lean_ctor_set(v___x_337_, 1, v_val_332_);
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_str_335_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_val_332_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_val_332_);
v___x_340_ = v_reuseFailAlloc_354_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v_str_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_351_; 
v_str_341_ = lean_ctor_get(v_trailing_326_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_trailing_326_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; lean_object* v_unused_353_; 
v_unused_352_ = lean_ctor_get(v_trailing_326_, 2);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_trailing_326_, 1);
lean_dec(v_unused_353_);
v___x_343_ = v_trailing_326_;
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_str_341_);
lean_dec(v_trailing_326_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
lean_inc_n(v_val_334_, 2);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 2, v_val_334_);
lean_ctor_set(v___x_343_, 1, v_val_334_);
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_str_341_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_val_334_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_val_334_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 3, v_val_334_);
lean_ctor_set(v___x_328_, 2, v___x_346_);
lean_ctor_set(v___x_328_, 1, v_val_332_);
lean_ctor_set(v___x_328_, 0, v___x_340_);
v___x_348_ = v___x_328_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_val_332_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v_val_334_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
else
{
lean_object* v___x_358_; 
lean_dec(v___x_333_);
lean_dec(v_val_332_);
lean_del_object(v___x_328_);
lean_dec_ref(v_trailing_326_);
lean_dec_ref(v_leading_325_);
v___x_358_ = lean_box(2);
return v___x_358_;
}
}
else
{
lean_object* v___x_359_; 
lean_dec(v___x_331_);
lean_del_object(v___x_328_);
lean_dec_ref(v_trailing_326_);
lean_dec_ref(v_leading_325_);
v___x_359_ = lean_box(2);
return v___x_359_;
}
}
}
case 1:
{
uint8_t v_canonical_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_377_; 
v_canonical_363_ = lean_ctor_get_uint8(v___x_324_, sizeof(void*)*2);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; 
v_unused_378_ = lean_ctor_get(v___x_324_, 1);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v___x_324_, 0);
lean_dec(v_unused_379_);
v___x_365_ = v___x_324_;
v_isShared_366_ = v_isSharedCheck_377_;
goto v_resetjp_364_;
}
else
{
lean_dec(v___x_324_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_377_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
uint8_t v___x_367_; lean_object* v___x_368_; 
v___x_367_ = 0;
v___x_368_ = l_Lean_Syntax_getPos_x3f(v_tok_323_, v___x_367_);
if (lean_obj_tag(v___x_368_) == 1)
{
lean_object* v_val_369_; lean_object* v___x_370_; 
v_val_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = l_Lean_Syntax_getTailPos_x3f(v_tok_323_, v___x_367_);
if (lean_obj_tag(v___x_370_) == 1)
{
lean_object* v_val_371_; lean_object* v___x_373_; 
v_val_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v___x_370_, 1);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v_val_371_);
lean_ctor_set(v___x_365_, 0, v_val_369_);
v___x_373_ = v___x_365_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_val_369_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_val_371_);
lean_ctor_set_uint8(v_reuseFailAlloc_374_, sizeof(void*)*2, v_canonical_363_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
else
{
lean_object* v___x_375_; 
lean_dec(v___x_370_);
lean_dec(v_val_369_);
lean_del_object(v___x_365_);
v___x_375_ = lean_box(2);
return v___x_375_;
}
}
else
{
lean_object* v___x_376_; 
lean_dec(v___x_368_);
lean_del_object(v___x_365_);
v___x_376_ = lean_box(2);
return v___x_376_;
}
}
}
default: 
{
lean_object* v___x_380_; 
lean_dec(v___x_324_);
v___x_380_ = lean_box(2);
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo___boxed(lean_object* v_tok_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(v_tok_381_);
lean_dec(v_tok_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_strLitOfContent(lean_object* v_value_383_, lean_object* v_tok_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(v_tok_384_);
v___x_386_ = l_Lean_Syntax_mkStrLit(v_value_383_, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_strLitOfContent___boxed(lean_object* v_value_387_, lean_object* v_tok_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Doc_strLitOfContent(v_value_387_, v_tok_388_);
lean_dec(v_tok_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(lean_object* v_tok_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Syntax_getHeadInfo(v_tok_390_);
switch(lean_obj_tag(v___x_391_))
{
case 0:
{
lean_object* v_leading_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_413_; 
v_leading_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; lean_object* v_unused_415_; lean_object* v_unused_416_; 
v_unused_414_ = lean_ctor_get(v___x_391_, 3);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v___x_391_, 2);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v___x_391_, 1);
lean_dec(v_unused_416_);
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_413_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_leading_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_413_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
uint8_t v___x_396_; lean_object* v___x_397_; 
v___x_396_ = 0;
v___x_397_ = l_Lean_Syntax_getPos_x3f(v_tok_390_, v___x_396_);
if (lean_obj_tag(v___x_397_) == 1)
{
lean_object* v_val_398_; lean_object* v_str_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_409_; 
v_val_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_val_398_);
lean_dec_ref_known(v___x_397_, 1);
v_str_399_ = lean_ctor_get(v_leading_392_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_leading_392_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_410_ = lean_ctor_get(v_leading_392_, 2);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_leading_392_, 1);
lean_dec(v_unused_411_);
v___x_401_ = v_leading_392_;
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_str_399_);
lean_dec(v_leading_392_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
lean_inc_n(v_val_398_, 2);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 2, v_val_398_);
lean_ctor_set(v___x_401_, 1, v_val_398_);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_str_399_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_val_398_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_val_398_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
lean_inc(v_val_398_);
lean_inc_ref(v___x_404_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 3, v_val_398_);
lean_ctor_set(v___x_394_, 2, v___x_404_);
lean_ctor_set(v___x_394_, 1, v_val_398_);
lean_ctor_set(v___x_394_, 0, v___x_404_);
v___x_406_ = v___x_394_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_val_398_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_val_398_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_object* v___x_412_; 
lean_dec(v___x_397_);
lean_del_object(v___x_394_);
lean_dec_ref(v_leading_392_);
v___x_412_ = lean_box(2);
return v___x_412_;
}
}
}
case 1:
{
uint8_t v_canonical_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_428_; 
v_canonical_417_ = lean_ctor_get_uint8(v___x_391_, sizeof(void*)*2);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; lean_object* v_unused_430_; 
v_unused_429_ = lean_ctor_get(v___x_391_, 1);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_430_);
v___x_419_ = v___x_391_;
v_isShared_420_ = v_isSharedCheck_428_;
goto v_resetjp_418_;
}
else
{
lean_dec(v___x_391_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_428_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
uint8_t v___x_421_; lean_object* v___x_422_; 
v___x_421_ = 0;
v___x_422_ = l_Lean_Syntax_getPos_x3f(v_tok_390_, v___x_421_);
if (lean_obj_tag(v___x_422_) == 1)
{
lean_object* v_val_423_; lean_object* v___x_425_; 
v_val_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_n(v_val_423_, 2);
lean_dec_ref_known(v___x_422_, 1);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v_val_423_);
lean_ctor_set(v___x_419_, 0, v_val_423_);
v___x_425_ = v___x_419_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_val_423_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_val_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*2, v_canonical_417_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
else
{
lean_object* v___x_427_; 
lean_dec(v___x_422_);
lean_del_object(v___x_419_);
v___x_427_ = lean_box(2);
return v___x_427_;
}
}
}
default: 
{
lean_object* v___x_431_; 
lean_dec(v___x_391_);
v___x_431_ = lean_box(2);
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo___boxed(lean_object* v_tok_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v_tok_432_);
lean_dec(v_tok_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(lean_object* v___x_435_, lean_object* v_value_436_, lean_object* v_a_437_, lean_object* v_b_438_){
_start:
{
uint8_t v_decide_439_; 
v_decide_439_ = lean_nat_dec_eq(v_a_437_, v___x_435_);
if (v_decide_439_ == 0)
{
uint32_t v___x_440_; lean_object* v___x_441_; uint32_t v___x_442_; uint8_t v___x_443_; 
v___x_440_ = lean_string_utf8_get_fast(v_value_436_, v_a_437_);
v___x_441_ = lean_string_utf8_next_fast(v_value_436_, v_a_437_);
lean_dec(v_a_437_);
v___x_442_ = 92;
v___x_443_ = lean_uint32_dec_eq(v___x_440_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
v___x_444_ = lean_string_push(v_b_438_, v___x_440_);
v_a_437_ = v___x_441_;
v_b_438_ = v___x_444_;
goto _start;
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0));
v___x_447_ = lean_string_append(v_b_438_, v___x_446_);
v_a_437_ = v___x_441_;
v_b_438_ = v___x_447_;
goto _start;
}
}
else
{
lean_dec(v_a_437_);
return v_b_438_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___boxed(lean_object* v___x_449_, lean_object* v_value_450_, lean_object* v_a_451_, lean_object* v_b_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_449_, v_value_450_, v_a_451_, v_b_452_);
lean_dec_ref(v_value_450_);
lean_dec(v___x_449_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(lean_object* v_value_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_456_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0));
v___x_457_ = lean_string_utf8_byte_size(v_value_455_);
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_457_, v_value_455_, v___x_458_, v___x_456_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___boxed(lean_object* v_value_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_460_);
lean_dec_ref(v_value_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(lean_object* v___x_462_, lean_object* v___x_463_, lean_object* v_value_464_, lean_object* v_inst_465_, lean_object* v_R_466_, lean_object* v_a_467_, lean_object* v_b_468_, lean_object* v_c_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_463_, v_value_464_, v_a_467_, v_b_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___boxed(lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v_value_473_, lean_object* v_inst_474_, lean_object* v_R_475_, lean_object* v_a_476_, lean_object* v_b_477_, lean_object* v_c_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(v___x_471_, v___x_472_, v_value_473_, v_inst_474_, v_R_475_, v_a_476_, v_b_477_, v_c_478_);
lean_dec_ref(v_value_473_);
lean_dec(v___x_472_);
lean_dec_ref(v___x_471_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom(lean_object* v_src_480_, lean_object* v_value_481_, uint8_t v_canonical_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_483_ = l_Lean_Doc_versoTextKind;
v___x_484_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_481_);
v___x_485_ = l_Lean_SourceInfo_fromRef(v_src_480_, v_canonical_482_);
v___x_486_ = l_Lean_Syntax_mkLit(v___x_483_, v___x_484_, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom___boxed(lean_object* v_src_487_, lean_object* v_value_488_, lean_object* v_canonical_489_){
_start:
{
uint8_t v_canonical_boxed_490_; lean_object* v_res_491_; 
v_canonical_boxed_490_ = lean_unbox(v_canonical_489_);
v_res_491_ = l_Lean_Doc_mkVersoTextFrom(v_src_487_, v_value_488_, v_canonical_boxed_490_);
lean_dec_ref(v_value_488_);
lean_dec(v_src_487_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom(lean_object* v_src_492_, lean_object* v_value_493_, uint8_t v_canonical_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = l_Lean_Doc_versoRefKind;
v___x_496_ = l_Lean_SourceInfo_fromRef(v_src_492_, v_canonical_494_);
v___x_497_ = l_Lean_Syntax_mkLit(v___x_495_, v_value_493_, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom___boxed(lean_object* v_src_498_, lean_object* v_value_499_, lean_object* v_canonical_500_){
_start:
{
uint8_t v_canonical_boxed_501_; lean_object* v_res_502_; 
v_canonical_boxed_501_ = lean_unbox(v_canonical_500_);
v_res_502_ = l_Lean_Doc_mkVersoRefNameFrom(v_src_498_, v_value_499_, v_canonical_boxed_501_);
lean_dec(v_src_498_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom(lean_object* v_src_503_, lean_object* v_value_504_, uint8_t v_canonical_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = l_Lean_Doc_versoLinkUrlKind;
v___x_507_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_504_);
v___x_508_ = l_Lean_SourceInfo_fromRef(v_src_503_, v_canonical_505_);
v___x_509_ = l_Lean_Syntax_mkLit(v___x_506_, v___x_507_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom___boxed(lean_object* v_src_510_, lean_object* v_value_511_, lean_object* v_canonical_512_){
_start:
{
uint8_t v_canonical_boxed_513_; lean_object* v_res_514_; 
v_canonical_boxed_513_ = lean_unbox(v_canonical_512_);
v_res_514_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_src_510_, v_value_511_, v_canonical_boxed_513_);
lean_dec_ref(v_value_511_);
lean_dec(v_src_510_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom(lean_object* v_src_515_, lean_object* v_value_516_, uint8_t v_canonical_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = l_Lean_Doc_versoImageAltKind;
v___x_519_ = l_Lean_Doc_escapeVersoImageAlt(v_value_516_);
v___x_520_ = l_Lean_SourceInfo_fromRef(v_src_515_, v_canonical_517_);
v___x_521_ = l_Lean_Syntax_mkLit(v___x_518_, v___x_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom___boxed(lean_object* v_src_522_, lean_object* v_value_523_, lean_object* v_canonical_524_){
_start:
{
uint8_t v_canonical_boxed_525_; lean_object* v_res_526_; 
v_canonical_boxed_525_ = lean_unbox(v_canonical_524_);
v_res_526_ = l_Lean_Doc_mkVersoImageAltFrom(v_src_522_, v_value_523_, v_canonical_boxed_525_);
lean_dec_ref(v_value_523_);
lean_dec(v_src_522_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom(lean_object* v_src_527_, lean_object* v_value_528_, uint8_t v_canonical_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = l_Lean_Doc_versoLinkRefUrlKind;
v___x_531_ = l_Lean_SourceInfo_fromRef(v_src_527_, v_canonical_529_);
v___x_532_ = l_Lean_Syntax_mkLit(v___x_530_, v_value_528_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom___boxed(lean_object* v_src_533_, lean_object* v_value_534_, lean_object* v_canonical_535_){
_start:
{
uint8_t v_canonical_boxed_536_; lean_object* v_res_537_; 
v_canonical_boxed_536_ = lean_unbox(v_canonical_535_);
v_res_537_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_src_533_, v_value_534_, v_canonical_boxed_536_);
lean_dec(v_src_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(lean_object* v_info_538_, lean_object* v___x_539_, lean_object* v_value_540_, lean_object* v_a_541_, lean_object* v_b_542_){
_start:
{
uint8_t v_decide_543_; 
v_decide_543_ = lean_nat_dec_eq(v_a_541_, v___x_539_);
if (v_decide_543_ == 0)
{
lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_566_; 
v_fst_544_ = lean_ctor_get(v_b_542_, 0);
v_snd_545_ = lean_ctor_get(v_b_542_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_b_542_);
if (v_isSharedCheck_566_ == 0)
{
v___x_547_ = v_b_542_;
v_isShared_548_ = v_isSharedCheck_566_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_snd_545_);
lean_inc(v_fst_544_);
lean_dec(v_b_542_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_566_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
uint32_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint32_t v___x_552_; uint8_t v___x_553_; 
v___x_549_ = lean_string_utf8_get_fast(v_value_540_, v_a_541_);
v___x_550_ = lean_string_utf8_next_fast(v_value_540_, v_a_541_);
lean_dec(v_a_541_);
v___x_551_ = lean_string_push(v_snd_545_, v___x_549_);
v___x_552_ = 10;
v___x_553_ = lean_uint32_dec_eq(v___x_549_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_555_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 1, v___x_551_);
v___x_555_ = v___x_547_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_fst_544_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_551_);
v___x_555_ = v_reuseFailAlloc_557_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v_a_541_ = v___x_550_;
v_b_542_ = v___x_555_;
goto _start;
}
}
else
{
lean_object* v_line_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v_line_558_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___closed__0));
v___x_559_ = l_Lean_Doc_versoCodeLineKind;
lean_inc(v_info_538_);
v___x_560_ = l_Lean_Syntax_mkLit(v___x_559_, v___x_551_, v_info_538_);
v___x_561_ = lean_array_push(v_fst_544_, v___x_560_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 1, v_line_558_);
lean_ctor_set(v___x_547_, 0, v___x_561_);
v___x_563_ = v___x_547_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_line_558_);
v___x_563_ = v_reuseFailAlloc_565_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
v_a_541_ = v___x_550_;
v_b_542_ = v___x_563_;
goto _start;
}
}
}
}
else
{
lean_dec(v_a_541_);
lean_dec(v_info_538_);
return v_b_542_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg___boxed(lean_object* v_info_567_, lean_object* v___x_568_, lean_object* v_value_569_, lean_object* v_a_570_, lean_object* v_b_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_567_, v___x_568_, v_value_569_, v_a_570_, v_b_571_);
lean_dec_ref(v_value_569_);
lean_dec(v___x_568_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(lean_object* v_info_578_, lean_object* v_value_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_fst_584_; lean_object* v_snd_585_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__1));
v___x_582_ = lean_string_utf8_byte_size(v_value_579_);
lean_inc(v_info_578_);
v___x_583_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_578_, v___x_582_, v_value_579_, v___x_580_, v___x_581_);
v_fst_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_fst_584_);
v_snd_585_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_snd_585_);
lean_dec_ref(v___x_583_);
v___x_590_ = lean_string_utf8_byte_size(v_snd_585_);
v___x_591_ = lean_nat_dec_eq(v___x_590_, v___x_580_);
if (v___x_591_ == 0)
{
goto v___jp_586_;
}
else
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_array_get_size(v_fst_584_);
v___x_593_ = lean_nat_dec_eq(v___x_592_, v___x_580_);
if (v___x_593_ == 0)
{
lean_dec(v_snd_585_);
lean_dec(v_info_578_);
return v_fst_584_;
}
else
{
goto v___jp_586_;
}
}
v___jp_586_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = l_Lean_Doc_versoCodeLineKind;
v___x_588_ = l_Lean_Syntax_mkLit(v___x_587_, v_snd_585_, v_info_578_);
v___x_589_ = lean_array_push(v_fst_584_, v___x_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___boxed(lean_object* v_info_594_, lean_object* v_value_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_594_, v_value_595_);
lean_dec_ref(v_value_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(lean_object* v_info_597_, lean_object* v___x_598_, lean_object* v___x_599_, lean_object* v_value_600_, lean_object* v_inst_601_, lean_object* v_R_602_, lean_object* v_a_603_, lean_object* v_b_604_, lean_object* v_c_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_597_, v___x_599_, v_value_600_, v_a_603_, v_b_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___boxed(lean_object* v_info_607_, lean_object* v___x_608_, lean_object* v___x_609_, lean_object* v_value_610_, lean_object* v_inst_611_, lean_object* v_R_612_, lean_object* v_a_613_, lean_object* v_b_614_, lean_object* v_c_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(v_info_607_, v___x_608_, v___x_609_, v_value_610_, v_inst_611_, v_R_612_, v_a_613_, v_b_614_, v_c_615_);
lean_dec_ref(v_value_610_);
lean_dec(v___x_609_);
lean_dec_ref(v___x_608_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom(lean_object* v_src_620_, lean_object* v_value_621_, uint8_t v_canonical_622_){
_start:
{
lean_object* v_info_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_info_623_ = l_Lean_SourceInfo_fromRef(v_src_620_, v_canonical_622_);
v___x_624_ = l_Lean_Doc_versoCodeKind;
lean_inc(v_info_623_);
v___x_625_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_623_, v_value_621_);
v___x_626_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_627_ = lean_box(2);
v___x_628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
lean_ctor_set(v___x_628_, 2, v___x_625_);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_mk_empty_array_with_capacity(v___x_629_);
v___x_631_ = lean_array_push(v___x_630_, v___x_628_);
v___x_632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_632_, 0, v_info_623_);
lean_ctor_set(v___x_632_, 1, v___x_624_);
lean_ctor_set(v___x_632_, 2, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom___boxed(lean_object* v_src_633_, lean_object* v_value_634_, lean_object* v_canonical_635_){
_start:
{
uint8_t v_canonical_boxed_636_; lean_object* v_res_637_; 
v_canonical_boxed_636_ = lean_unbox(v_canonical_635_);
v_res_637_ = l_Lean_Doc_mkVersoCodeFrom(v_src_633_, v_value_634_, v_canonical_boxed_636_);
lean_dec_ref(v_value_634_);
lean_dec(v_src_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom(lean_object* v_src_638_, lean_object* v_value_639_, uint8_t v_canonical_640_){
_start:
{
lean_object* v_info_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_info_641_ = l_Lean_SourceInfo_fromRef(v_src_638_, v_canonical_640_);
v___x_642_ = l_Lean_Doc_versoCodeBlockKind;
lean_inc(v_info_641_);
v___x_643_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_641_, v_value_639_);
v___x_644_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_645_ = lean_box(2);
v___x_646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
lean_ctor_set(v___x_646_, 2, v___x_643_);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___x_649_ = lean_array_push(v___x_648_, v___x_646_);
v___x_650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_650_, 0, v_info_641_);
lean_ctor_set(v___x_650_, 1, v___x_642_);
lean_ctor_set(v___x_650_, 2, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___boxed(lean_object* v_src_651_, lean_object* v_value_652_, lean_object* v_canonical_653_){
_start:
{
uint8_t v_canonical_boxed_654_; lean_object* v_res_655_; 
v_canonical_boxed_654_ = lean_unbox(v_canonical_653_);
v_res_655_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_src_651_, v_value_652_, v_canonical_boxed_654_);
lean_dec_ref(v_value_652_);
lean_dec(v_src_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom(lean_object* v_src_665_, uint8_t v_canonical_666_){
_start:
{
lean_object* v_info_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_info_667_ = l_Lean_SourceInfo_fromRef(v_src_665_, v_canonical_666_);
v___x_668_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
v___x_669_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__3));
lean_inc(v_info_667_);
v___x_670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_670_, 0, v_info_667_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_mk_empty_array_with_capacity(v___x_671_);
v___x_673_ = lean_array_push(v___x_672_, v___x_670_);
v___x_674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_674_, 0, v_info_667_);
lean_ctor_set(v___x_674_, 1, v___x_668_);
lean_ctor_set(v___x_674_, 2, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom___boxed(lean_object* v_src_675_, lean_object* v_canonical_676_){
_start:
{
uint8_t v_canonical_boxed_677_; lean_object* v_res_678_; 
v_canonical_boxed_677_ = lean_unbox(v_canonical_676_);
v_res_678_ = l_Lean_Doc_mkVersoLinebreakFrom(v_src_675_, v_canonical_boxed_677_);
lean_dec(v_src_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(uint8_t v_canonical_679_, lean_object* v_toPure_680_, lean_object* v_____do__lift_681_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = l_Lean_Doc_mkVersoLinebreakFrom(v_____do__lift_681_, v_canonical_679_);
v___x_683_ = lean_apply_2(v_toPure_680_, lean_box(0), v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed(lean_object* v_canonical_684_, lean_object* v_toPure_685_, lean_object* v_____do__lift_686_){
_start:
{
uint8_t v_canonical_boxed_687_; lean_object* v_res_688_; 
v_canonical_boxed_687_ = lean_unbox(v_canonical_684_);
v_res_688_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(v_canonical_boxed_687_, v_toPure_685_, v_____do__lift_686_);
lean_dec(v_____do__lift_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg(lean_object* v_inst_689_, lean_object* v_inst_690_, uint8_t v_canonical_691_){
_start:
{
lean_object* v_toApplicative_692_; lean_object* v_toBind_693_; lean_object* v_getRef_694_; lean_object* v_toPure_695_; lean_object* v___x_696_; lean_object* v___f_697_; lean_object* v___x_698_; 
v_toApplicative_692_ = lean_ctor_get(v_inst_689_, 0);
lean_inc_ref(v_toApplicative_692_);
v_toBind_693_ = lean_ctor_get(v_inst_689_, 1);
lean_inc(v_toBind_693_);
lean_dec_ref(v_inst_689_);
v_getRef_694_ = lean_ctor_get(v_inst_690_, 0);
lean_inc(v_getRef_694_);
lean_dec_ref(v_inst_690_);
v_toPure_695_ = lean_ctor_get(v_toApplicative_692_, 1);
lean_inc(v_toPure_695_);
lean_dec_ref(v_toApplicative_692_);
v___x_696_ = lean_box(v_canonical_691_);
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_697_, 0, v___x_696_);
lean_closure_set(v___f_697_, 1, v_toPure_695_);
v___x_698_ = lean_apply_4(v_toBind_693_, lean_box(0), lean_box(0), v_getRef_694_, v___f_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___boxed(lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_canonical_701_){
_start:
{
uint8_t v_canonical_boxed_702_; lean_object* v_res_703_; 
v_canonical_boxed_702_ = lean_unbox(v_canonical_701_);
v_res_703_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_699_, v_inst_700_, v_canonical_boxed_702_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef(lean_object* v_m_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, uint8_t v_canonical_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_705_, v_inst_706_, v_canonical_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___boxed(lean_object* v_m_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_canonical_712_){
_start:
{
uint8_t v_canonical_boxed_713_; lean_object* v_res_714_; 
v_canonical_boxed_713_ = lean_unbox(v_canonical_712_);
v_res_714_ = l_Lean_Doc_mkVersoLinebreakFromRef(v_m_709_, v_inst_710_, v_inst_711_, v_canonical_boxed_713_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(lean_object* v_value_715_, uint8_t v_canonical_716_, lean_object* v_toPure_717_, lean_object* v_____do__lift_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = l_Lean_Doc_mkVersoTextFrom(v_____do__lift_718_, v_value_715_, v_canonical_716_);
v___x_720_ = lean_apply_2(v_toPure_717_, lean_box(0), v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed(lean_object* v_value_721_, lean_object* v_canonical_722_, lean_object* v_toPure_723_, lean_object* v_____do__lift_724_){
_start:
{
uint8_t v_canonical_boxed_725_; lean_object* v_res_726_; 
v_canonical_boxed_725_ = lean_unbox(v_canonical_722_);
v_res_726_ = l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(v_value_721_, v_canonical_boxed_725_, v_toPure_723_, v_____do__lift_724_);
lean_dec(v_____do__lift_724_);
lean_dec_ref(v_value_721_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg(lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_value_729_, uint8_t v_canonical_730_){
_start:
{
lean_object* v_toApplicative_731_; lean_object* v_toBind_732_; lean_object* v_getRef_733_; lean_object* v_toPure_734_; lean_object* v___x_735_; lean_object* v___f_736_; lean_object* v___x_737_; 
v_toApplicative_731_ = lean_ctor_get(v_inst_727_, 0);
lean_inc_ref(v_toApplicative_731_);
v_toBind_732_ = lean_ctor_get(v_inst_727_, 1);
lean_inc(v_toBind_732_);
lean_dec_ref(v_inst_727_);
v_getRef_733_ = lean_ctor_get(v_inst_728_, 0);
lean_inc(v_getRef_733_);
lean_dec_ref(v_inst_728_);
v_toPure_734_ = lean_ctor_get(v_toApplicative_731_, 1);
lean_inc(v_toPure_734_);
lean_dec_ref(v_toApplicative_731_);
v___x_735_ = lean_box(v_canonical_730_);
v___f_736_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_736_, 0, v_value_729_);
lean_closure_set(v___f_736_, 1, v___x_735_);
lean_closure_set(v___f_736_, 2, v_toPure_734_);
v___x_737_ = lean_apply_4(v_toBind_732_, lean_box(0), lean_box(0), v_getRef_733_, v___f_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___boxed(lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_value_740_, lean_object* v_canonical_741_){
_start:
{
uint8_t v_canonical_boxed_742_; lean_object* v_res_743_; 
v_canonical_boxed_742_ = lean_unbox(v_canonical_741_);
v_res_743_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_738_, v_inst_739_, v_value_740_, v_canonical_boxed_742_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef(lean_object* v_m_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_value_747_, uint8_t v_canonical_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_745_, v_inst_746_, v_value_747_, v_canonical_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___boxed(lean_object* v_m_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_value_753_, lean_object* v_canonical_754_){
_start:
{
uint8_t v_canonical_boxed_755_; lean_object* v_res_756_; 
v_canonical_boxed_755_ = lean_unbox(v_canonical_754_);
v_res_756_ = l_Lean_Doc_mkVersoTextFromRef(v_m_750_, v_inst_751_, v_inst_752_, v_value_753_, v_canonical_boxed_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(lean_object* v_value_757_, uint8_t v_canonical_758_, lean_object* v_toPure_759_, lean_object* v_____do__lift_760_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = l_Lean_Doc_mkVersoRefNameFrom(v_____do__lift_760_, v_value_757_, v_canonical_758_);
v___x_762_ = lean_apply_2(v_toPure_759_, lean_box(0), v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed(lean_object* v_value_763_, lean_object* v_canonical_764_, lean_object* v_toPure_765_, lean_object* v_____do__lift_766_){
_start:
{
uint8_t v_canonical_boxed_767_; lean_object* v_res_768_; 
v_canonical_boxed_767_ = lean_unbox(v_canonical_764_);
v_res_768_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(v_value_763_, v_canonical_boxed_767_, v_toPure_765_, v_____do__lift_766_);
lean_dec(v_____do__lift_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg(lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_value_771_, uint8_t v_canonical_772_){
_start:
{
lean_object* v_toApplicative_773_; lean_object* v_toBind_774_; lean_object* v_getRef_775_; lean_object* v_toPure_776_; lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v___x_779_; 
v_toApplicative_773_ = lean_ctor_get(v_inst_769_, 0);
lean_inc_ref(v_toApplicative_773_);
v_toBind_774_ = lean_ctor_get(v_inst_769_, 1);
lean_inc(v_toBind_774_);
lean_dec_ref(v_inst_769_);
v_getRef_775_ = lean_ctor_get(v_inst_770_, 0);
lean_inc(v_getRef_775_);
lean_dec_ref(v_inst_770_);
v_toPure_776_ = lean_ctor_get(v_toApplicative_773_, 1);
lean_inc(v_toPure_776_);
lean_dec_ref(v_toApplicative_773_);
v___x_777_ = lean_box(v_canonical_772_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_778_, 0, v_value_771_);
lean_closure_set(v___f_778_, 1, v___x_777_);
lean_closure_set(v___f_778_, 2, v_toPure_776_);
v___x_779_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v_getRef_775_, v___f_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___boxed(lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_value_782_, lean_object* v_canonical_783_){
_start:
{
uint8_t v_canonical_boxed_784_; lean_object* v_res_785_; 
v_canonical_boxed_784_ = lean_unbox(v_canonical_783_);
v_res_785_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_780_, v_inst_781_, v_value_782_, v_canonical_boxed_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef(lean_object* v_m_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_value_789_, uint8_t v_canonical_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_787_, v_inst_788_, v_value_789_, v_canonical_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___boxed(lean_object* v_m_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_value_795_, lean_object* v_canonical_796_){
_start:
{
uint8_t v_canonical_boxed_797_; lean_object* v_res_798_; 
v_canonical_boxed_797_ = lean_unbox(v_canonical_796_);
v_res_798_ = l_Lean_Doc_mkVersoRefNameFromRef(v_m_792_, v_inst_793_, v_inst_794_, v_value_795_, v_canonical_boxed_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(lean_object* v_value_799_, uint8_t v_canonical_800_, lean_object* v_toPure_801_, lean_object* v_____do__lift_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_____do__lift_802_, v_value_799_, v_canonical_800_);
v___x_804_ = lean_apply_2(v_toPure_801_, lean_box(0), v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_805_, lean_object* v_canonical_806_, lean_object* v_toPure_807_, lean_object* v_____do__lift_808_){
_start:
{
uint8_t v_canonical_boxed_809_; lean_object* v_res_810_; 
v_canonical_boxed_809_ = lean_unbox(v_canonical_806_);
v_res_810_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(v_value_805_, v_canonical_boxed_809_, v_toPure_807_, v_____do__lift_808_);
lean_dec(v_____do__lift_808_);
lean_dec_ref(v_value_805_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_value_813_, uint8_t v_canonical_814_){
_start:
{
lean_object* v_toApplicative_815_; lean_object* v_toBind_816_; lean_object* v_getRef_817_; lean_object* v_toPure_818_; lean_object* v___x_819_; lean_object* v___f_820_; lean_object* v___x_821_; 
v_toApplicative_815_ = lean_ctor_get(v_inst_811_, 0);
lean_inc_ref(v_toApplicative_815_);
v_toBind_816_ = lean_ctor_get(v_inst_811_, 1);
lean_inc(v_toBind_816_);
lean_dec_ref(v_inst_811_);
v_getRef_817_ = lean_ctor_get(v_inst_812_, 0);
lean_inc(v_getRef_817_);
lean_dec_ref(v_inst_812_);
v_toPure_818_ = lean_ctor_get(v_toApplicative_815_, 1);
lean_inc(v_toPure_818_);
lean_dec_ref(v_toApplicative_815_);
v___x_819_ = lean_box(v_canonical_814_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_820_, 0, v_value_813_);
lean_closure_set(v___f_820_, 1, v___x_819_);
lean_closure_set(v___f_820_, 2, v_toPure_818_);
v___x_821_ = lean_apply_4(v_toBind_816_, lean_box(0), lean_box(0), v_getRef_817_, v___f_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___boxed(lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_value_824_, lean_object* v_canonical_825_){
_start:
{
uint8_t v_canonical_boxed_826_; lean_object* v_res_827_; 
v_canonical_boxed_826_ = lean_unbox(v_canonical_825_);
v_res_827_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_822_, v_inst_823_, v_value_824_, v_canonical_boxed_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef(lean_object* v_m_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_value_831_, uint8_t v_canonical_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_829_, v_inst_830_, v_value_831_, v_canonical_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___boxed(lean_object* v_m_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_value_837_, lean_object* v_canonical_838_){
_start:
{
uint8_t v_canonical_boxed_839_; lean_object* v_res_840_; 
v_canonical_boxed_839_ = lean_unbox(v_canonical_838_);
v_res_840_ = l_Lean_Doc_mkVersoLinkUrlFromRef(v_m_834_, v_inst_835_, v_inst_836_, v_value_837_, v_canonical_boxed_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(lean_object* v_value_841_, uint8_t v_canonical_842_, lean_object* v_toPure_843_, lean_object* v_____do__lift_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = l_Lean_Doc_mkVersoImageAltFrom(v_____do__lift_844_, v_value_841_, v_canonical_842_);
v___x_846_ = lean_apply_2(v_toPure_843_, lean_box(0), v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed(lean_object* v_value_847_, lean_object* v_canonical_848_, lean_object* v_toPure_849_, lean_object* v_____do__lift_850_){
_start:
{
uint8_t v_canonical_boxed_851_; lean_object* v_res_852_; 
v_canonical_boxed_851_ = lean_unbox(v_canonical_848_);
v_res_852_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(v_value_847_, v_canonical_boxed_851_, v_toPure_849_, v_____do__lift_850_);
lean_dec(v_____do__lift_850_);
lean_dec_ref(v_value_847_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg(lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_value_855_, uint8_t v_canonical_856_){
_start:
{
lean_object* v_toApplicative_857_; lean_object* v_toBind_858_; lean_object* v_getRef_859_; lean_object* v_toPure_860_; lean_object* v___x_861_; lean_object* v___f_862_; lean_object* v___x_863_; 
v_toApplicative_857_ = lean_ctor_get(v_inst_853_, 0);
lean_inc_ref(v_toApplicative_857_);
v_toBind_858_ = lean_ctor_get(v_inst_853_, 1);
lean_inc(v_toBind_858_);
lean_dec_ref(v_inst_853_);
v_getRef_859_ = lean_ctor_get(v_inst_854_, 0);
lean_inc(v_getRef_859_);
lean_dec_ref(v_inst_854_);
v_toPure_860_ = lean_ctor_get(v_toApplicative_857_, 1);
lean_inc(v_toPure_860_);
lean_dec_ref(v_toApplicative_857_);
v___x_861_ = lean_box(v_canonical_856_);
v___f_862_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_862_, 0, v_value_855_);
lean_closure_set(v___f_862_, 1, v___x_861_);
lean_closure_set(v___f_862_, 2, v_toPure_860_);
v___x_863_ = lean_apply_4(v_toBind_858_, lean_box(0), lean_box(0), v_getRef_859_, v___f_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___boxed(lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_value_866_, lean_object* v_canonical_867_){
_start:
{
uint8_t v_canonical_boxed_868_; lean_object* v_res_869_; 
v_canonical_boxed_868_ = lean_unbox(v_canonical_867_);
v_res_869_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_864_, v_inst_865_, v_value_866_, v_canonical_boxed_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef(lean_object* v_m_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_value_873_, uint8_t v_canonical_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_871_, v_inst_872_, v_value_873_, v_canonical_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___boxed(lean_object* v_m_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_value_879_, lean_object* v_canonical_880_){
_start:
{
uint8_t v_canonical_boxed_881_; lean_object* v_res_882_; 
v_canonical_boxed_881_ = lean_unbox(v_canonical_880_);
v_res_882_ = l_Lean_Doc_mkVersoImageAltFromRef(v_m_876_, v_inst_877_, v_inst_878_, v_value_879_, v_canonical_boxed_881_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(lean_object* v_value_883_, uint8_t v_canonical_884_, lean_object* v_toPure_885_, lean_object* v_____do__lift_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_____do__lift_886_, v_value_883_, v_canonical_884_);
v___x_888_ = lean_apply_2(v_toPure_885_, lean_box(0), v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_889_, lean_object* v_canonical_890_, lean_object* v_toPure_891_, lean_object* v_____do__lift_892_){
_start:
{
uint8_t v_canonical_boxed_893_; lean_object* v_res_894_; 
v_canonical_boxed_893_ = lean_unbox(v_canonical_890_);
v_res_894_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(v_value_889_, v_canonical_boxed_893_, v_toPure_891_, v_____do__lift_892_);
lean_dec(v_____do__lift_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_value_897_, uint8_t v_canonical_898_){
_start:
{
lean_object* v_toApplicative_899_; lean_object* v_toBind_900_; lean_object* v_getRef_901_; lean_object* v_toPure_902_; lean_object* v___x_903_; lean_object* v___f_904_; lean_object* v___x_905_; 
v_toApplicative_899_ = lean_ctor_get(v_inst_895_, 0);
lean_inc_ref(v_toApplicative_899_);
v_toBind_900_ = lean_ctor_get(v_inst_895_, 1);
lean_inc(v_toBind_900_);
lean_dec_ref(v_inst_895_);
v_getRef_901_ = lean_ctor_get(v_inst_896_, 0);
lean_inc(v_getRef_901_);
lean_dec_ref(v_inst_896_);
v_toPure_902_ = lean_ctor_get(v_toApplicative_899_, 1);
lean_inc(v_toPure_902_);
lean_dec_ref(v_toApplicative_899_);
v___x_903_ = lean_box(v_canonical_898_);
v___f_904_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_904_, 0, v_value_897_);
lean_closure_set(v___f_904_, 1, v___x_903_);
lean_closure_set(v___f_904_, 2, v_toPure_902_);
v___x_905_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v_getRef_901_, v___f_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___boxed(lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_value_908_, lean_object* v_canonical_909_){
_start:
{
uint8_t v_canonical_boxed_910_; lean_object* v_res_911_; 
v_canonical_boxed_910_ = lean_unbox(v_canonical_909_);
v_res_911_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_906_, v_inst_907_, v_value_908_, v_canonical_boxed_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef(lean_object* v_m_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_value_915_, uint8_t v_canonical_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_913_, v_inst_914_, v_value_915_, v_canonical_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___boxed(lean_object* v_m_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_value_921_, lean_object* v_canonical_922_){
_start:
{
uint8_t v_canonical_boxed_923_; lean_object* v_res_924_; 
v_canonical_boxed_923_ = lean_unbox(v_canonical_922_);
v_res_924_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef(v_m_918_, v_inst_919_, v_inst_920_, v_value_921_, v_canonical_boxed_923_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(lean_object* v_value_925_, uint8_t v_canonical_926_, lean_object* v_toPure_927_, lean_object* v_____do__lift_928_){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = l_Lean_Doc_mkVersoCodeFrom(v_____do__lift_928_, v_value_925_, v_canonical_926_);
v___x_930_ = lean_apply_2(v_toPure_927_, lean_box(0), v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed(lean_object* v_value_931_, lean_object* v_canonical_932_, lean_object* v_toPure_933_, lean_object* v_____do__lift_934_){
_start:
{
uint8_t v_canonical_boxed_935_; lean_object* v_res_936_; 
v_canonical_boxed_935_ = lean_unbox(v_canonical_932_);
v_res_936_ = l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(v_value_931_, v_canonical_boxed_935_, v_toPure_933_, v_____do__lift_934_);
lean_dec(v_____do__lift_934_);
lean_dec_ref(v_value_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg(lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_value_939_, uint8_t v_canonical_940_){
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
v___f_946_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_946_, 0, v_value_939_);
lean_closure_set(v___f_946_, 1, v___x_945_);
lean_closure_set(v___f_946_, 2, v_toPure_944_);
v___x_947_ = lean_apply_4(v_toBind_942_, lean_box(0), lean_box(0), v_getRef_943_, v___f_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___boxed(lean_object* v_inst_948_, lean_object* v_inst_949_, lean_object* v_value_950_, lean_object* v_canonical_951_){
_start:
{
uint8_t v_canonical_boxed_952_; lean_object* v_res_953_; 
v_canonical_boxed_952_ = lean_unbox(v_canonical_951_);
v_res_953_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_948_, v_inst_949_, v_value_950_, v_canonical_boxed_952_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef(lean_object* v_m_954_, lean_object* v_inst_955_, lean_object* v_inst_956_, lean_object* v_value_957_, uint8_t v_canonical_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_955_, v_inst_956_, v_value_957_, v_canonical_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___boxed(lean_object* v_m_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_value_963_, lean_object* v_canonical_964_){
_start:
{
uint8_t v_canonical_boxed_965_; lean_object* v_res_966_; 
v_canonical_boxed_965_ = lean_unbox(v_canonical_964_);
v_res_966_ = l_Lean_Doc_mkVersoCodeFromRef(v_m_960_, v_inst_961_, v_inst_962_, v_value_963_, v_canonical_boxed_965_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(lean_object* v_value_967_, uint8_t v_canonical_968_, lean_object* v_toPure_969_, lean_object* v_____do__lift_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_____do__lift_970_, v_value_967_, v_canonical_968_);
v___x_972_ = lean_apply_2(v_toPure_969_, lean_box(0), v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed(lean_object* v_value_973_, lean_object* v_canonical_974_, lean_object* v_toPure_975_, lean_object* v_____do__lift_976_){
_start:
{
uint8_t v_canonical_boxed_977_; lean_object* v_res_978_; 
v_canonical_boxed_977_ = lean_unbox(v_canonical_974_);
v_res_978_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(v_value_973_, v_canonical_boxed_977_, v_toPure_975_, v_____do__lift_976_);
lean_dec(v_____do__lift_976_);
lean_dec_ref(v_value_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_value_981_, uint8_t v_canonical_982_){
_start:
{
lean_object* v_toApplicative_983_; lean_object* v_toBind_984_; lean_object* v_getRef_985_; lean_object* v_toPure_986_; lean_object* v___x_987_; lean_object* v___f_988_; lean_object* v___x_989_; 
v_toApplicative_983_ = lean_ctor_get(v_inst_979_, 0);
lean_inc_ref(v_toApplicative_983_);
v_toBind_984_ = lean_ctor_get(v_inst_979_, 1);
lean_inc(v_toBind_984_);
lean_dec_ref(v_inst_979_);
v_getRef_985_ = lean_ctor_get(v_inst_980_, 0);
lean_inc(v_getRef_985_);
lean_dec_ref(v_inst_980_);
v_toPure_986_ = lean_ctor_get(v_toApplicative_983_, 1);
lean_inc(v_toPure_986_);
lean_dec_ref(v_toApplicative_983_);
v___x_987_ = lean_box(v_canonical_982_);
v___f_988_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_988_, 0, v_value_981_);
lean_closure_set(v___f_988_, 1, v___x_987_);
lean_closure_set(v___f_988_, 2, v_toPure_986_);
v___x_989_ = lean_apply_4(v_toBind_984_, lean_box(0), lean_box(0), v_getRef_985_, v___f_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___boxed(lean_object* v_inst_990_, lean_object* v_inst_991_, lean_object* v_value_992_, lean_object* v_canonical_993_){
_start:
{
uint8_t v_canonical_boxed_994_; lean_object* v_res_995_; 
v_canonical_boxed_994_ = lean_unbox(v_canonical_993_);
v_res_995_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_990_, v_inst_991_, v_value_992_, v_canonical_boxed_994_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef(lean_object* v_m_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_value_999_, uint8_t v_canonical_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_997_, v_inst_998_, v_value_999_, v_canonical_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___boxed(lean_object* v_m_1002_, lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_value_1005_, lean_object* v_canonical_1006_){
_start:
{
uint8_t v_canonical_boxed_1007_; lean_object* v_res_1008_; 
v_canonical_boxed_1007_ = lean_unbox(v_canonical_1006_);
v_res_1008_ = l_Lean_Doc_mkVersoCodeBlockFromRef(v_m_1002_, v_inst_1003_, v_inst_1004_, v_value_1005_, v_canonical_boxed_1007_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_of(lean_object* v_stx_1036_){
_start:
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__2));
lean_inc(v_stx_1036_);
v___x_1038_ = l_Lean_Syntax_isOfKind(v_stx_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__4));
lean_inc(v_stx_1036_);
v___x_1040_ = l_Lean_Syntax_isOfKind(v_stx_1036_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec(v_stx_1036_);
v___x_1041_ = lean_box(0);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v_o_1043_; lean_object* v___x_1044_; lean_object* v_name_1045_; 
v___x_1042_ = lean_unsigned_to_nat(0u);
v_o_1043_ = l_Lean_Syntax_getArg(v_stx_1036_, v___x_1042_);
v___x_1044_ = lean_unsigned_to_nat(1u);
v_name_1045_ = l_Lean_Syntax_getArg(v_stx_1036_, v___x_1044_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_1045_);
v___x_1052_ = l_Lean_Syntax_isOfKind(v_name_1045_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec(v_name_1045_);
lean_dec(v_o_1043_);
lean_dec(v_stx_1036_);
v___x_1053_ = lean_box(0);
return v___x_1053_;
}
else
{
goto v___jp_1046_;
}
}
else
{
goto v___jp_1046_;
}
v___jp_1046_:
{
lean_object* v___x_1047_; lean_object* v_c_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1047_ = lean_unsigned_to_nat(2u);
v_c_1048_ = l_Lean_Syntax_getArg(v_stx_1036_, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1049_, 0, v_stx_1036_);
lean_ctor_set(v___x_1049_, 1, v_o_1043_);
lean_ctor_set(v___x_1049_, 2, v_name_1045_);
lean_ctor_set(v___x_1049_, 3, v_c_1048_);
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
}
}
else
{
lean_object* v___x_1054_; lean_object* v_url_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1054_ = lean_unsigned_to_nat(1u);
v_url_1055_ = l_Lean_Syntax_getArg(v_stx_1036_, v___x_1054_);
v___x_1056_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__8));
lean_inc(v_url_1055_);
v___x_1057_ = l_Lean_Syntax_isOfKind(v_url_1055_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_dec(v_url_1055_);
lean_dec(v_stx_1036_);
v___x_1058_ = lean_box(0);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; lean_object* v_o_1060_; lean_object* v___x_1061_; lean_object* v_c_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1059_ = lean_unsigned_to_nat(0u);
v_o_1060_ = l_Lean_Syntax_getArg(v_stx_1036_, v___x_1059_);
v___x_1061_ = lean_unsigned_to_nat(2u);
v_c_1062_ = l_Lean_Syntax_getArg(v_stx_1036_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1063_, 0, v_stx_1036_);
lean_ctor_set(v___x_1063_, 1, v_o_1060_);
lean_ctor_set(v___x_1063_, 2, v_url_1055_);
lean_ctor_set(v___x_1063_, 3, v_c_1062_);
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText(lean_object* v_v_1069_){
_start:
{
lean_object* v_content_1070_; lean_object* v___x_1071_; 
v_content_1070_ = lean_ctor_get(v_v_1069_, 1);
v___x_1071_ = l_Lean_TSyntax_getVersoText(v_content_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText___boxed(lean_object* v_v_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Doc_TextView_getVersoText(v_v_1072_);
lean_dec_ref(v_v_1072_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object* v_v_1074_){
_start:
{
lean_object* v_content_1075_; lean_object* v___x_1076_; 
v_content_1075_ = lean_ctor_get(v_v_1074_, 1);
v___x_1076_ = l_Lean_TSyntax_getVersoTextSource(v_content_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource___boxed(lean_object* v_v_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Doc_TextView_getVersoTextSource(v_v_1077_);
lean_dec_ref(v_v_1077_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_of(lean_object* v_stx_1092_){
_start:
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__1));
lean_inc(v_stx_1092_);
v___x_1094_ = l_Lean_Syntax_isOfKind(v_stx_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v_stx_1092_);
v___x_1095_ = lean_box(0);
return v___x_1095_;
}
else
{
lean_object* v___x_1096_; lean_object* v_s_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1096_ = lean_unsigned_to_nat(0u);
v_s_1097_ = l_Lean_Syntax_getArg(v_stx_1092_, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__3));
lean_inc(v_s_1097_);
v___x_1099_ = l_Lean_Syntax_isOfKind(v_s_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_dec(v_s_1097_);
lean_dec(v_stx_1092_);
v___x_1100_ = lean_box(0);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_stx_1092_);
lean_ctor_set(v___x_1101_, 1, v_s_1097_);
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_EmphView_of(lean_object* v_stx_1116_){
_start:
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Lean_Doc_EmphView_of___closed__1));
lean_inc(v_stx_1116_);
v___x_1118_ = l_Lean_Syntax_isOfKind(v_stx_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec(v_stx_1116_);
v___x_1119_ = lean_box(0);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; lean_object* v_o_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1120_ = lean_unsigned_to_nat(0u);
v_o_1121_ = l_Lean_Syntax_getArg(v_stx_1116_, v___x_1120_);
v___x_1122_ = ((lean_object*)(l_Lean_Doc_EmphView_of___closed__3));
lean_inc(v_o_1121_);
v___x_1123_ = l_Lean_Syntax_isOfKind(v_o_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_dec(v_o_1121_);
lean_dec(v_stx_1116_);
v___x_1124_ = lean_box(0);
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; lean_object* v_c_1126_; uint8_t v___x_1127_; 
v___x_1125_ = lean_unsigned_to_nat(2u);
v_c_1126_ = l_Lean_Syntax_getArg(v_stx_1116_, v___x_1125_);
lean_inc(v_c_1126_);
v___x_1127_ = l_Lean_Syntax_isOfKind(v_c_1126_, v___x_1122_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec(v_c_1126_);
lean_dec(v_o_1121_);
lean_dec(v_stx_1116_);
v___x_1128_ = lean_box(0);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_inl_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = l_Lean_Syntax_getArg(v_stx_1116_, v___x_1129_);
v_inl_1131_ = l_Lean_Syntax_getArgs(v___x_1130_);
lean_dec(v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1132_, 0, v_stx_1116_);
lean_ctor_set(v___x_1132_, 1, v_o_1121_);
lean_ctor_set(v___x_1132_, 2, v_inl_1131_);
lean_ctor_set(v___x_1132_, 3, v_c_1126_);
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BoldView_of(lean_object* v_stx_1147_){
_start:
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_Lean_Doc_BoldView_of___closed__1));
lean_inc(v_stx_1147_);
v___x_1149_ = l_Lean_Syntax_isOfKind(v_stx_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_dec(v_stx_1147_);
v___x_1150_ = lean_box(0);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; lean_object* v_o_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1151_ = lean_unsigned_to_nat(0u);
v_o_1152_ = l_Lean_Syntax_getArg(v_stx_1147_, v___x_1151_);
v___x_1153_ = ((lean_object*)(l_Lean_Doc_BoldView_of___closed__3));
lean_inc(v_o_1152_);
v___x_1154_ = l_Lean_Syntax_isOfKind(v_o_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
lean_dec(v_o_1152_);
lean_dec(v_stx_1147_);
v___x_1155_ = lean_box(0);
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; lean_object* v_c_1157_; uint8_t v___x_1158_; 
v___x_1156_ = lean_unsigned_to_nat(2u);
v_c_1157_ = l_Lean_Syntax_getArg(v_stx_1147_, v___x_1156_);
lean_inc(v_c_1157_);
v___x_1158_ = l_Lean_Syntax_isOfKind(v_c_1157_, v___x_1153_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec(v_c_1157_);
lean_dec(v_o_1152_);
lean_dec(v_stx_1147_);
v___x_1159_ = lean_box(0);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_inl_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = l_Lean_Syntax_getArg(v_stx_1147_, v___x_1160_);
v_inl_1162_ = l_Lean_Syntax_getArgs(v___x_1161_);
lean_dec(v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1163_, 0, v_stx_1147_);
lean_ctor_set(v___x_1163_, 1, v_o_1152_);
lean_ctor_set(v___x_1163_, 2, v_inl_1162_);
lean_ctor_set(v___x_1163_, 3, v_c_1157_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object* v_v_1165_){
_start:
{
lean_object* v_content_1166_; lean_object* v___x_1167_; 
v_content_1166_ = lean_ctor_get(v_v_1165_, 2);
v___x_1167_ = l_Lean_TSyntax_getVersoCode(v_content_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode___boxed(lean_object* v_v_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Doc_CodeView_getVersoCode(v_v_1168_);
lean_dec_ref(v_v_1168_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_of(lean_object* v_stx_1189_){
_start:
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v_stx_1189_);
v___x_1191_ = l_Lean_Syntax_isOfKind(v_stx_1189_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; 
lean_dec(v_stx_1189_);
v___x_1192_ = lean_box(0);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; lean_object* v_o_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1193_ = lean_unsigned_to_nat(0u);
v_o_1194_ = l_Lean_Syntax_getArg(v_stx_1189_, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__3));
lean_inc(v_o_1194_);
v___x_1196_ = l_Lean_Syntax_isOfKind(v_o_1194_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_dec(v_o_1194_);
lean_dec(v_stx_1189_);
v___x_1197_ = lean_box(0);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; lean_object* v_s_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1198_ = lean_unsigned_to_nat(1u);
v_s_1199_ = l_Lean_Syntax_getArg(v_stx_1189_, v___x_1198_);
v___x_1200_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__5));
lean_inc(v_s_1199_);
v___x_1201_ = l_Lean_Syntax_isOfKind(v_s_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; 
lean_dec(v_s_1199_);
lean_dec(v_o_1194_);
lean_dec(v_stx_1189_);
v___x_1202_ = lean_box(0);
return v___x_1202_;
}
else
{
lean_object* v___x_1203_; lean_object* v_c_1204_; uint8_t v___x_1205_; 
v___x_1203_ = lean_unsigned_to_nat(2u);
v_c_1204_ = l_Lean_Syntax_getArg(v_stx_1189_, v___x_1203_);
lean_inc(v_c_1204_);
v___x_1205_ = l_Lean_Syntax_isOfKind(v_c_1204_, v___x_1195_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; 
lean_dec(v_c_1204_);
lean_dec(v_s_1199_);
lean_dec(v_o_1194_);
lean_dec(v_stx_1189_);
v___x_1206_ = lean_box(0);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1207_, 0, v_stx_1189_);
lean_ctor_set(v___x_1207_, 1, v_o_1194_);
lean_ctor_set(v___x_1207_, 2, v_s_1199_);
lean_ctor_set(v___x_1207_, 3, v_c_1204_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object* v_v_1209_){
_start:
{
lean_object* v_code_1210_; lean_object* v___x_1211_; 
v_code_1210_ = lean_ctor_get(v_v_1209_, 2);
v___x_1211_ = l_Lean_Doc_CodeView_getVersoCode(v_code_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode___boxed(lean_object* v_v_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Doc_MathView_getVersoCode(v_v_1212_);
lean_dec_ref(v_v_1212_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_of(lean_object* v_stx_1240_){
_start:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__1));
lean_inc(v_stx_1240_);
v___x_1242_ = l_Lean_Syntax_isOfKind(v_stx_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__3));
lean_inc(v_stx_1240_);
v___x_1244_ = l_Lean_Syntax_isOfKind(v_stx_1240_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_dec(v_stx_1240_);
v___x_1245_ = lean_box(0);
return v___x_1245_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___y_1249_; 
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = l_Lean_Syntax_getArg(v_stx_1240_, v___x_1246_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__5));
lean_inc(v___x_1247_);
v___x_1269_ = l_Lean_Syntax_isOfKind(v___x_1247_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
lean_dec(v___x_1247_);
lean_dec(v_stx_1240_);
v___x_1270_ = lean_box(0);
return v___x_1270_;
}
else
{
goto v___jp_1262_;
}
}
else
{
goto v___jp_1262_;
}
v___jp_1248_:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Doc_CodeView_of(v___y_1249_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1251_; 
lean_dec(v___x_1247_);
lean_dec(v_stx_1240_);
v___x_1251_ = lean_box(0);
return v___x_1251_;
}
else
{
lean_object* v_val_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1261_; 
v_val_1252_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1254_ = v___x_1250_;
v_isShared_1255_ = v_isSharedCheck_1261_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_val_1252_);
lean_dec(v___x_1250_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1261_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1256_ = 1;
v___x_1257_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1257_, 0, v_stx_1240_);
lean_ctor_set(v___x_1257_, 1, v___x_1247_);
lean_ctor_set(v___x_1257_, 2, v_val_1252_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*3, v___x_1256_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1257_);
v___x_1259_ = v___x_1254_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
v___jp_1262_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = l_Lean_Syntax_getArg(v_stx_1240_, v___x_1263_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v___x_1264_);
v___x_1266_ = l_Lean_Syntax_isOfKind(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec(v___x_1264_);
lean_dec(v___x_1247_);
lean_dec(v_stx_1240_);
v___x_1267_ = lean_box(0);
return v___x_1267_;
}
else
{
v___y_1249_ = v___x_1264_;
goto v___jp_1248_;
}
}
else
{
v___y_1249_ = v___x_1264_;
goto v___jp_1248_;
}
}
}
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = l_Lean_Syntax_getArg(v_stx_1240_, v___x_1271_);
v___x_1273_ = ((lean_object*)(l_Lean_Doc_MathView_of___closed__7));
lean_inc(v___x_1272_);
v___x_1274_ = l_Lean_Syntax_isOfKind(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_dec(v___x_1272_);
lean_dec(v_stx_1240_);
v___x_1275_ = lean_box(0);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = l_Lean_Syntax_getArg(v_stx_1240_, v___x_1276_);
v___x_1278_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v___x_1277_);
v___x_1279_ = l_Lean_Syntax_isOfKind(v___x_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec(v___x_1277_);
lean_dec(v___x_1272_);
lean_dec(v_stx_1240_);
v___x_1280_ = lean_box(0);
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Doc_CodeView_of(v___x_1277_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
lean_dec(v___x_1272_);
lean_dec(v_stx_1240_);
v___x_1282_ = lean_box(0);
return v___x_1282_;
}
else
{
lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1292_; 
v_val_1283_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1287_ = 0;
v___x_1288_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1288_, 0, v_stx_1240_);
lean_ctor_set(v___x_1288_, 1, v___x_1272_);
lean_ctor_set(v___x_1288_, 2, v_val_1283_);
lean_ctor_set_uint8(v___x_1288_, sizeof(void*)*3, v___x_1287_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkView_of(lean_object* v_stx_1300_){
_start:
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_Doc_LinkView_of___closed__1));
lean_inc(v_stx_1300_);
v___x_1302_ = l_Lean_Syntax_isOfKind(v_stx_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec(v_stx_1300_);
v___x_1303_ = lean_box(0);
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; lean_object* v_tgt_1305_; lean_object* v___x_1306_; 
v___x_1304_ = lean_unsigned_to_nat(3u);
v_tgt_1305_ = l_Lean_Syntax_getArg(v_stx_1300_, v___x_1304_);
v___x_1306_ = l_Lean_Doc_LinkTargetView_of(v_tgt_1305_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v___x_1307_; 
lean_dec(v_stx_1300_);
v___x_1307_ = lean_box(0);
return v___x_1307_;
}
else
{
lean_object* v_val_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1323_; 
v_val_1308_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1310_ = v___x_1306_;
v_isShared_1311_ = v_isSharedCheck_1323_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_val_1308_);
lean_dec(v___x_1306_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1323_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v_o_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v_c_1317_; lean_object* v_inl_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v_o_1313_ = l_Lean_Syntax_getArg(v_stx_1300_, v___x_1312_);
v___x_1314_ = lean_unsigned_to_nat(1u);
v___x_1315_ = l_Lean_Syntax_getArg(v_stx_1300_, v___x_1314_);
v___x_1316_ = lean_unsigned_to_nat(2u);
v_c_1317_ = l_Lean_Syntax_getArg(v_stx_1300_, v___x_1316_);
v_inl_1318_ = l_Lean_Syntax_getArgs(v___x_1315_);
lean_dec(v___x_1315_);
v___x_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1319_, 0, v_stx_1300_);
lean_ctor_set(v___x_1319_, 1, v_o_1313_);
lean_ctor_set(v___x_1319_, 2, v_inl_1318_);
lean_ctor_set(v___x_1319_, 3, v_c_1317_);
lean_ctor_set(v___x_1319_, 4, v_val_1308_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1319_);
v___x_1321_ = v___x_1310_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt(lean_object* v_v_1324_){
_start:
{
lean_object* v_alt_1325_; lean_object* v___x_1326_; 
v_alt_1325_ = lean_ctor_get(v_v_1324_, 2);
v___x_1326_ = l_Lean_TSyntax_getVersoImageAlt(v_alt_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt___boxed(lean_object* v_v_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Doc_ImageView_getAlt(v_v_1327_);
lean_dec_ref(v_v_1327_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_of(lean_object* v_stx_1342_){
_start:
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__1));
lean_inc(v_stx_1342_);
v___x_1344_ = l_Lean_Syntax_isOfKind(v_stx_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
lean_dec(v_stx_1342_);
v___x_1345_ = lean_box(0);
return v___x_1345_;
}
else
{
lean_object* v___x_1346_; lean_object* v_alt_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1346_ = lean_unsigned_to_nat(1u);
v_alt_1347_ = l_Lean_Syntax_getArg(v_stx_1342_, v___x_1346_);
v___x_1348_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__3));
lean_inc(v_alt_1347_);
v___x_1349_ = l_Lean_Syntax_isOfKind(v_alt_1347_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_alt_1347_);
lean_dec(v_stx_1342_);
v___x_1350_ = lean_box(0);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; lean_object* v_tgt_1352_; lean_object* v___x_1353_; 
v___x_1351_ = lean_unsigned_to_nat(3u);
v_tgt_1352_ = l_Lean_Syntax_getArg(v_stx_1342_, v___x_1351_);
v___x_1353_ = l_Lean_Doc_LinkTargetView_of(v_tgt_1352_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1354_; 
lean_dec(v_alt_1347_);
lean_dec(v_stx_1342_);
v___x_1354_ = lean_box(0);
return v___x_1354_;
}
else
{
lean_object* v_val_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1367_; 
v_val_1355_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1357_ = v___x_1353_;
v_isShared_1358_ = v_isSharedCheck_1367_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_val_1355_);
lean_dec(v___x_1353_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1367_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v_o_1360_; lean_object* v___x_1361_; lean_object* v_c_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1359_ = lean_unsigned_to_nat(0u);
v_o_1360_ = l_Lean_Syntax_getArg(v_stx_1342_, v___x_1359_);
v___x_1361_ = lean_unsigned_to_nat(2u);
v_c_1362_ = l_Lean_Syntax_getArg(v_stx_1342_, v___x_1361_);
v___x_1363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1363_, 0, v_stx_1342_);
lean_ctor_set(v___x_1363_, 1, v_o_1360_);
lean_ctor_set(v___x_1363_, 2, v_alt_1347_);
lean_ctor_set(v___x_1363_, 3, v_c_1362_);
lean_ctor_set(v___x_1363_, 4, v_val_1355_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1363_);
v___x_1365_ = v___x_1357_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName(lean_object* v_v_1368_){
_start:
{
lean_object* v_name_1369_; lean_object* v___x_1370_; 
v_name_1369_ = lean_ctor_get(v_v_1368_, 2);
v___x_1370_ = l_Lean_TSyntax_getVersoRefName(v_name_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName___boxed(lean_object* v_v_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Doc_FootnoteView_getName(v_v_1371_);
lean_dec_ref(v_v_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_of(lean_object* v_stx_1380_){
_start:
{
lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = ((lean_object*)(l_Lean_Doc_FootnoteView_of___closed__1));
lean_inc(v_stx_1380_);
v___x_1382_ = l_Lean_Syntax_isOfKind(v_stx_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
lean_dec(v_stx_1380_);
v___x_1383_ = lean_box(0);
return v___x_1383_;
}
else
{
lean_object* v___x_1384_; lean_object* v_name_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1384_ = lean_unsigned_to_nat(1u);
v_name_1385_ = l_Lean_Syntax_getArg(v_stx_1380_, v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_1385_);
v___x_1387_ = l_Lean_Syntax_isOfKind(v_name_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; 
lean_dec(v_name_1385_);
lean_dec(v_stx_1380_);
v___x_1388_ = lean_box(0);
return v___x_1388_;
}
else
{
lean_object* v___x_1389_; lean_object* v_o_1390_; lean_object* v___x_1391_; lean_object* v_c_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1389_ = lean_unsigned_to_nat(0u);
v_o_1390_ = l_Lean_Syntax_getArg(v_stx_1380_, v___x_1389_);
v___x_1391_ = lean_unsigned_to_nat(2u);
v_c_1392_ = l_Lean_Syntax_getArg(v_stx_1380_, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1393_, 0, v_stx_1380_);
lean_ctor_set(v___x_1393_, 1, v_o_1390_);
lean_ctor_set(v___x_1393_, 2, v_name_1385_);
lean_ctor_set(v___x_1393_, 3, v_c_1392_);
v___x_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinebreakView_of(lean_object* v_stx_1395_){
_start:
{
lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1396_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
lean_inc(v_stx_1395_);
v___x_1397_ = l_Lean_Syntax_isOfKind(v_stx_1395_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
lean_dec(v_stx_1395_);
v___x_1398_ = lean_box(0);
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = l_Lean_Syntax_getArg(v_stx_1395_, v___x_1399_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_stx_1395_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_RoleView_of(lean_object* v_stx_1410_){
_start:
{
lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = ((lean_object*)(l_Lean_Doc_RoleView_of___closed__1));
lean_inc(v_stx_1410_);
v___x_1412_ = l_Lean_Syntax_isOfKind(v_stx_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
lean_dec(v_stx_1410_);
v___x_1413_ = lean_box(0);
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; lean_object* v_name_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1414_ = lean_unsigned_to_nat(1u);
v_name_1415_ = l_Lean_Syntax_getArg(v_stx_1410_, v___x_1414_);
v___x_1416_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_1415_);
v___x_1417_ = l_Lean_Syntax_isOfKind(v_name_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec(v_name_1415_);
lean_dec(v_stx_1410_);
v___x_1418_ = lean_box(0);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; lean_object* v_bo_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v_bc_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1419_ = lean_unsigned_to_nat(0u);
v_bo_1420_ = l_Lean_Syntax_getArg(v_stx_1410_, v___x_1419_);
v___x_1421_ = lean_unsigned_to_nat(2u);
v___x_1422_ = l_Lean_Syntax_getArg(v_stx_1410_, v___x_1421_);
v___x_1423_ = lean_unsigned_to_nat(3u);
v_bc_1424_ = l_Lean_Syntax_getArg(v_stx_1410_, v___x_1423_);
v___x_1425_ = lean_unsigned_to_nat(4u);
v___x_1426_ = l_Lean_Syntax_getArg(v_stx_1410_, v___x_1425_);
lean_inc(v___x_1426_);
v___x_1427_ = l_Lean_Syntax_matchesNull(v___x_1426_, v___x_1414_);
if (v___x_1427_ == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = l_Lean_Syntax_matchesNull(v___x_1426_, v___x_1419_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
lean_dec(v_bc_1424_);
lean_dec(v___x_1422_);
lean_dec(v_bo_1420_);
lean_dec(v_name_1415_);
lean_dec(v_stx_1410_);
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1430_ = lean_unsigned_to_nat(6u);
v___x_1431_ = l_Lean_Syntax_getArg(v_stx_1410_, v___x_1430_);
v___x_1432_ = l_Lean_Syntax_matchesNull(v___x_1431_, v___x_1419_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; 
lean_dec(v_bc_1424_);
lean_dec(v___x_1422_);
lean_dec(v_bo_1420_);
lean_dec(v_name_1415_);
lean_dec(v_stx_1410_);
v___x_1433_ = lean_box(0);
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v_inl_1436_; lean_object* v_args_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1434_ = lean_unsigned_to_nat(5u);
v___x_1435_ = l_Lean_Syntax_getArg(v_stx_1410_, v___x_1434_);
v_inl_1436_ = l_Lean_Syntax_getArgs(v___x_1435_);
lean_dec(v___x_1435_);
v_args_1437_ = l_Lean_Syntax_getArgs(v___x_1422_);
lean_dec(v___x_1422_);
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1439_, 0, v_stx_1410_);
lean_ctor_set(v___x_1439_, 1, v_bo_1420_);
lean_ctor_set(v___x_1439_, 2, v_name_1415_);
lean_ctor_set(v___x_1439_, 3, v_args_1437_);
lean_ctor_set(v___x_1439_, 4, v_bc_1424_);
lean_ctor_set(v___x_1439_, 5, v___x_1438_);
lean_ctor_set(v___x_1439_, 6, v_inl_1436_);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
}
}
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = lean_unsigned_to_nat(6u);
v___x_1442_ = l_Lean_Syntax_getArg(v_stx_1410_, v___x_1441_);
lean_inc(v___x_1442_);
v___x_1443_ = l_Lean_Syntax_matchesNull(v___x_1442_, v___x_1414_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_dec(v___x_1442_);
lean_dec(v___x_1426_);
lean_dec(v_bc_1424_);
lean_dec(v___x_1422_);
lean_dec(v_bo_1420_);
lean_dec(v_name_1415_);
lean_dec(v_stx_1410_);
v___x_1444_ = lean_box(0);
return v___x_1444_;
}
else
{
lean_object* v_so_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_sc_1448_; lean_object* v_inl_1449_; lean_object* v_args_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_so_1445_ = l_Lean_Syntax_getArg(v___x_1426_, v___x_1419_);
lean_dec(v___x_1426_);
v___x_1446_ = lean_unsigned_to_nat(5u);
v___x_1447_ = l_Lean_Syntax_getArg(v_stx_1410_, v___x_1446_);
v_sc_1448_ = l_Lean_Syntax_getArg(v___x_1442_, v___x_1419_);
lean_dec(v___x_1442_);
v_inl_1449_ = l_Lean_Syntax_getArgs(v___x_1447_);
lean_dec(v___x_1447_);
v_args_1450_ = l_Lean_Syntax_getArgs(v___x_1422_);
lean_dec(v___x_1422_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_so_1445_);
lean_ctor_set(v___x_1451_, 1, v_sc_1448_);
v___x_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1453_, 0, v_stx_1410_);
lean_ctor_set(v___x_1453_, 1, v_bo_1420_);
lean_ctor_set(v___x_1453_, 2, v_name_1415_);
lean_ctor_set(v___x_1453_, 3, v_args_1450_);
lean_ctor_set(v___x_1453_, 4, v_bc_1424_);
lean_ctor_set(v___x_1453_, 5, v___x_1452_);
lean_ctor_set(v___x_1453_, 6, v_inl_1449_);
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
return v___x_1454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx(lean_object* v_x_1455_){
_start:
{
switch(lean_obj_tag(v_x_1455_))
{
case 0:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_unsigned_to_nat(0u);
return v___x_1456_;
}
case 1:
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
return v___x_1457_;
}
case 2:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_unsigned_to_nat(2u);
return v___x_1458_;
}
case 3:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_unsigned_to_nat(3u);
return v___x_1459_;
}
case 4:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_unsigned_to_nat(4u);
return v___x_1460_;
}
case 5:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_unsigned_to_nat(5u);
return v___x_1461_;
}
case 6:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_unsigned_to_nat(6u);
return v___x_1462_;
}
case 7:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_unsigned_to_nat(7u);
return v___x_1463_;
}
case 8:
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_unsigned_to_nat(8u);
return v___x_1464_;
}
default: 
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_unsigned_to_nat(9u);
return v___x_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___boxed(lean_object* v_x_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Doc_InlineView_ctorIdx(v_x_1466_);
lean_dec_ref(v_x_1466_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___redArg(lean_object* v_t_1468_, lean_object* v_k_1469_){
_start:
{
lean_object* v_view_1470_; lean_object* v___x_1471_; 
v_view_1470_ = lean_ctor_get(v_t_1468_, 0);
lean_inc_ref(v_view_1470_);
lean_dec_ref(v_t_1468_);
v___x_1471_ = lean_apply_1(v_k_1469_, v_view_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim(lean_object* v_motive_1472_, lean_object* v_ctorIdx_1473_, lean_object* v_t_1474_, lean_object* v_h_1475_, lean_object* v_k_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1474_, v_k_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___boxed(lean_object* v_motive_1478_, lean_object* v_ctorIdx_1479_, lean_object* v_t_1480_, lean_object* v_h_1481_, lean_object* v_k_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Doc_InlineView_ctorElim(v_motive_1478_, v_ctorIdx_1479_, v_t_1480_, v_h_1481_, v_k_1482_);
lean_dec(v_ctorIdx_1479_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim___redArg(lean_object* v_t_1484_, lean_object* v_text_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1484_, v_text_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim(lean_object* v_motive_1487_, lean_object* v_t_1488_, lean_object* v_h_1489_, lean_object* v_text_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1488_, v_text_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim___redArg(lean_object* v_t_1492_, lean_object* v_emph_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1492_, v_emph_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim(lean_object* v_motive_1495_, lean_object* v_t_1496_, lean_object* v_h_1497_, lean_object* v_emph_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1496_, v_emph_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim___redArg(lean_object* v_t_1500_, lean_object* v_bold_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1500_, v_bold_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim(lean_object* v_motive_1503_, lean_object* v_t_1504_, lean_object* v_h_1505_, lean_object* v_bold_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1504_, v_bold_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim___redArg(lean_object* v_t_1508_, lean_object* v_code_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1508_, v_code_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim(lean_object* v_motive_1511_, lean_object* v_t_1512_, lean_object* v_h_1513_, lean_object* v_code_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1512_, v_code_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim___redArg(lean_object* v_t_1516_, lean_object* v_math_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1516_, v_math_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim(lean_object* v_motive_1519_, lean_object* v_t_1520_, lean_object* v_h_1521_, lean_object* v_math_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1520_, v_math_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim___redArg(lean_object* v_t_1524_, lean_object* v_link_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1524_, v_link_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim(lean_object* v_motive_1527_, lean_object* v_t_1528_, lean_object* v_h_1529_, lean_object* v_link_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1528_, v_link_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim___redArg(lean_object* v_t_1532_, lean_object* v_image_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1532_, v_image_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim(lean_object* v_motive_1535_, lean_object* v_t_1536_, lean_object* v_h_1537_, lean_object* v_image_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1536_, v_image_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim___redArg(lean_object* v_t_1540_, lean_object* v_footnote_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1540_, v_footnote_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim(lean_object* v_motive_1543_, lean_object* v_t_1544_, lean_object* v_h_1545_, lean_object* v_footnote_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1544_, v_footnote_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim___redArg(lean_object* v_t_1548_, lean_object* v_linebreak_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1548_, v_linebreak_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim(lean_object* v_motive_1551_, lean_object* v_t_1552_, lean_object* v_h_1553_, lean_object* v_linebreak_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1552_, v_linebreak_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim___redArg(lean_object* v_t_1556_, lean_object* v_role_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1556_, v_role_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim(lean_object* v_motive_1559_, lean_object* v_t_1560_, lean_object* v_h_1561_, lean_object* v_role_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_1560_, v_role_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTextViewInlineView___lam__0(lean_object* v_view_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_view_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeEmphViewInlineView___lam__0(lean_object* v_view_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_view_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBoldViewInlineView___lam__0(lean_object* v_view_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_view_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeViewInlineView___lam__0(lean_object* v_view_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_view_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMathViewInlineView___lam__0(lean_object* v_view_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_view_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkViewInlineView___lam__0(lean_object* v_view_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1589_, 0, v_view_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeImageViewInlineView___lam__0(lean_object* v_view_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1593_, 0, v_view_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0(lean_object* v_view_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_view_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0(lean_object* v_view_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_view_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeRoleViewInlineView___lam__0(lean_object* v_view_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_view_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx(lean_object* v_x_1608_){
_start:
{
lean_object* v_view_1609_; lean_object* v_stx_1610_; 
v_view_1609_ = lean_ctor_get(v_x_1608_, 0);
v_stx_1610_ = lean_ctor_get(v_view_1609_, 0);
lean_inc(v_stx_1610_);
return v_stx_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx___boxed(lean_object* v_x_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Doc_InlineView_stx(v_x_1611_);
lean_dec_ref(v_x_1611_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_of(lean_object* v_stx_1613_){
_start:
{
lean_object* v___x_1614_; 
lean_inc(v_stx_1613_);
v___x_1614_ = l_Lean_Doc_TextView_of(v_stx_1613_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v___x_1615_; 
lean_inc(v_stx_1613_);
v___x_1615_ = l_Lean_Doc_EmphView_of(v_stx_1613_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v___x_1616_; 
lean_inc(v_stx_1613_);
v___x_1616_ = l_Lean_Doc_BoldView_of(v_stx_1613_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v___x_1617_; 
lean_inc(v_stx_1613_);
v___x_1617_ = l_Lean_Doc_CodeView_of(v_stx_1613_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v___x_1618_; 
lean_inc(v_stx_1613_);
v___x_1618_ = l_Lean_Doc_MathView_of(v_stx_1613_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v___x_1619_; 
lean_inc(v_stx_1613_);
v___x_1619_ = l_Lean_Doc_LinkView_of(v_stx_1613_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v___x_1620_; 
lean_inc(v_stx_1613_);
v___x_1620_ = l_Lean_Doc_ImageView_of(v_stx_1613_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v___x_1621_; 
lean_inc(v_stx_1613_);
v___x_1621_ = l_Lean_Doc_FootnoteView_of(v_stx_1613_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v___x_1622_; 
lean_inc(v_stx_1613_);
v___x_1622_ = l_Lean_Doc_LinebreakView_of(v_stx_1613_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Doc_RoleView_of(v_stx_1613_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_box(0);
return v___x_1624_;
}
else
{
lean_object* v_val_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1633_; 
v_val_1625_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1627_ = v___x_1623_;
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_val_1625_);
lean_dec(v___x_1623_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_alloc_ctor(9, 1, 0);
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
else
{
lean_object* v_val_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1642_; 
lean_dec(v_stx_1613_);
v_val_1634_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1636_ = v___x_1622_;
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_val_1634_);
lean_dec(v___x_1622_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1638_, 0, v_val_1634_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1638_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v_val_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_stx_1613_);
v_val_1643_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1645_ = v___x_1621_;
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_val_1643_);
lean_dec(v___x_1621_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_val_1643_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_stx_1613_);
v_val_1652_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1654_ = v___x_1620_;
v_isShared_1655_ = v_isSharedCheck_1660_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_val_1652_);
lean_dec(v___x_1620_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1660_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1656_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_val_1652_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1656_);
v___x_1658_ = v___x_1654_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v_val_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_stx_1613_);
v_val_1661_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1663_ = v___x_1619_;
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_val_1661_);
lean_dec(v___x_1619_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_val_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1665_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_val_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_stx_1613_);
v_val_1670_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1672_ = v___x_1618_;
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_val_1670_);
lean_dec(v___x_1618_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_val_1670_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1674_);
v___x_1676_ = v___x_1672_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_stx_1613_);
v_val_1679_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1681_ = v___x_1617_;
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v___x_1617_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_val_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_val_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_stx_1613_);
v_val_1688_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1690_ = v___x_1616_;
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_val_1688_);
lean_dec(v___x_1616_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_val_1688_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1692_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_object* v_val_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_stx_1613_);
v_val_1697_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1699_ = v___x_1615_;
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_val_1697_);
lean_dec(v___x_1615_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1701_, 0, v_val_1697_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1701_);
v___x_1703_ = v___x_1699_;
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
else
{
lean_object* v_val_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_stx_1613_);
v_val_1706_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1708_ = v___x_1614_;
v_isShared_1709_ = v_isSharedCheck_1714_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_val_1706_);
lean_dec(v___x_1614_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1714_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_val_1706_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1710_);
v___x_1712_ = v___x_1708_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(uint32_t v_a_1715_, lean_object* v_x_1716_){
_start:
{
if (lean_obj_tag(v_x_1716_) == 0)
{
uint8_t v___x_1717_; 
v___x_1717_ = 0;
return v___x_1717_;
}
else
{
lean_object* v_head_1718_; lean_object* v_tail_1719_; uint32_t v___x_1720_; uint8_t v___x_1721_; 
v_head_1718_ = lean_ctor_get(v_x_1716_, 0);
v_tail_1719_ = lean_ctor_get(v_x_1716_, 1);
v___x_1720_ = lean_unbox_uint32(v_head_1718_);
v___x_1721_ = lean_uint32_dec_eq(v_a_1715_, v___x_1720_);
if (v___x_1721_ == 0)
{
v_x_1716_ = v_tail_1719_;
goto _start;
}
else
{
return v___x_1721_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0___boxed(lean_object* v_a_1723_, lean_object* v_x_1724_){
_start:
{
uint32_t v_a_boxed_1725_; uint8_t v_res_1726_; lean_object* v_r_1727_; 
v_a_boxed_1725_ = lean_unbox_uint32(v_a_1723_);
lean_dec(v_a_1723_);
v_res_1726_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v_a_boxed_1725_, v_x_1724_);
lean_dec(v_x_1724_);
v_r_1727_ = lean_box(v_res_1726_);
return v_r_1727_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = 43;
v___x_1743_ = lean_box_uint32(v___x_1742_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__5(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_box(0);
v___x_1745_ = l_Lean_Doc_UnorderedListItemView_of___closed__5___boxed__const__1;
v___x_1746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v___x_1744_);
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = 45;
v___x_1748_ = lean_box_uint32(v___x_1747_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__6(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__5, &l_Lean_Doc_UnorderedListItemView_of___closed__5_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__5);
v___x_1750_ = l_Lean_Doc_UnorderedListItemView_of___closed__6___boxed__const__1;
v___x_1751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v___x_1749_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = 42;
v___x_1753_ = lean_box_uint32(v___x_1752_);
return v___x_1753_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__7(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__6, &l_Lean_Doc_UnorderedListItemView_of___closed__6_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__6);
v___x_1755_ = l_Lean_Doc_UnorderedListItemView_of___closed__7___boxed__const__1;
v___x_1756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of(lean_object* v_stx_1757_){
_start:
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__2));
lean_inc(v_stx_1757_);
v___x_1759_ = l_Lean_Syntax_isOfKind(v_stx_1757_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_dec(v_stx_1757_);
v___x_1760_ = lean_box(0);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; lean_object* v_m_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1761_ = lean_unsigned_to_nat(0u);
v_m_1762_ = l_Lean_Syntax_getArg(v_stx_1757_, v___x_1761_);
v___x_1763_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__4));
lean_inc(v_m_1762_);
v___x_1764_ = l_Lean_Syntax_isOfKind(v_m_1762_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
lean_dec(v_m_1762_);
lean_dec(v_stx_1757_);
v___x_1765_ = lean_box(0);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1766_ = l_Lean_TSyntax_getVersoDelimiter(v_m_1762_);
v___x_1767_ = lean_string_utf8_byte_size(v___x_1766_);
v___x_1768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1761_);
lean_ctor_set(v___x_1768_, 2, v___x_1767_);
v___x_1769_ = l_String_Slice_Pos_get_x3f(v___x_1768_, v___x_1761_);
lean_dec_ref_known(v___x_1768_, 3);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1770_; 
lean_dec(v_m_1762_);
lean_dec(v_stx_1757_);
v___x_1770_ = lean_box(0);
return v___x_1770_;
}
else
{
lean_object* v_val_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1786_; 
v_val_1771_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1773_ = v___x_1769_;
v_isShared_1774_ = v_isSharedCheck_1786_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_val_1771_);
lean_dec(v___x_1769_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1786_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; uint32_t v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__7, &l_Lean_Doc_UnorderedListItemView_of___closed__7_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__7);
v___x_1776_ = lean_unbox_uint32(v_val_1771_);
lean_dec(v_val_1771_);
v___x_1777_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v___x_1776_, v___x_1775_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_del_object(v___x_1773_);
lean_dec(v_m_1762_);
lean_dec(v_stx_1757_);
v___x_1778_ = lean_box(0);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v_bs_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1779_ = lean_unsigned_to_nat(1u);
v___x_1780_ = l_Lean_Syntax_getArg(v_stx_1757_, v___x_1779_);
v_bs_1781_ = l_Lean_Syntax_getArgs(v___x_1780_);
lean_dec(v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1782_, 0, v_stx_1757_);
lean_ctor_set(v___x_1782_, 1, v_m_1762_);
lean_ctor_set(v___x_1782_, 2, v_bs_1781_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1782_);
v___x_1784_ = v___x_1773_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(lean_object* v_s_1787_, lean_object* v_pos_1788_){
_start:
{
lean_object* v_str_1789_; lean_object* v_startInclusive_1790_; lean_object* v_endExclusive_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v_decide_1795_; 
v_str_1789_ = lean_ctor_get(v_s_1787_, 0);
v_startInclusive_1790_ = lean_ctor_get(v_s_1787_, 1);
v_endExclusive_1791_ = lean_ctor_get(v_s_1787_, 2);
v___x_1792_ = lean_nat_add(v_startInclusive_1790_, v_pos_1788_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_nat_sub(v_endExclusive_1791_, v___x_1792_);
v_decide_1795_ = lean_nat_dec_eq(v___x_1793_, v___x_1794_);
lean_dec(v___x_1794_);
if (v_decide_1795_ == 0)
{
uint32_t v___x_1796_; uint32_t v___x_1797_; uint8_t v___x_1798_; 
v___x_1796_ = lean_string_utf8_get_fast(v_str_1789_, v___x_1792_);
v___x_1797_ = 48;
v___x_1798_ = lean_uint32_dec_le(v___x_1797_, v___x_1796_);
if (v___x_1798_ == 0)
{
lean_dec(v___x_1792_);
return v_pos_1788_;
}
else
{
uint32_t v___x_1799_; uint8_t v___x_1800_; 
v___x_1799_ = 57;
v___x_1800_ = lean_uint32_dec_le(v___x_1796_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_dec(v___x_1792_);
return v_pos_1788_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1801_ = lean_string_utf8_next_fast(v_str_1789_, v___x_1792_);
v___x_1802_ = lean_nat_sub(v___x_1801_, v___x_1792_);
lean_dec(v___x_1792_);
v___x_1803_ = lean_nat_add(v_pos_1788_, v___x_1802_);
lean_dec(v___x_1802_);
v___x_1804_ = lean_unsigned_to_nat(1u);
v___x_1805_ = lean_nat_add(v_pos_1788_, v___x_1804_);
v___x_1806_ = lean_nat_dec_le(v___x_1805_, v___x_1803_);
lean_dec(v___x_1805_);
if (v___x_1806_ == 0)
{
lean_dec(v___x_1803_);
return v_pos_1788_;
}
else
{
lean_dec(v_pos_1788_);
v_pos_1788_ = v___x_1803_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_1792_);
return v_pos_1788_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0___boxed(lean_object* v_s_1808_, lean_object* v_pos_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v_s_1808_, v_pos_1809_);
lean_dec_ref(v_s_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_number(lean_object* v_v_1811_){
_start:
{
lean_object* v_marker_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1827_; 
v_marker_1812_ = lean_ctor_get(v_v_1811_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_v_1811_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; lean_object* v_unused_1829_; 
v_unused_1828_ = lean_ctor_get(v_v_1811_, 2);
lean_dec(v_unused_1828_);
v_unused_1829_ = lean_ctor_get(v_v_1811_, 0);
lean_dec(v_unused_1829_);
v___x_1814_ = v_v_1811_;
v_isShared_1815_ = v_isSharedCheck_1827_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_marker_1812_);
lean_dec(v_v_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1827_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1816_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_1812_);
lean_dec(v_marker_1812_);
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1818_ = lean_string_utf8_byte_size(v___x_1816_);
lean_inc_ref(v___x_1816_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 2, v___x_1818_);
lean_ctor_set(v___x_1814_, 1, v___x_1817_);
lean_ctor_set(v___x_1814_, 0, v___x_1816_);
v___x_1820_ = v___x_1814_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1826_, 2, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1821_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v___x_1820_, v___x_1817_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = lean_string_utf8_extract_fast(v___x_1816_, v___x_1817_, v___x_1821_);
lean_dec(v___x_1821_);
lean_dec_ref(v___x_1816_);
v___x_1823_ = lean_string_utf8_byte_size(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1817_);
lean_ctor_set(v___x_1824_, 2, v___x_1823_);
v___x_1825_ = l_String_Slice_toNat_x3f(v___x_1824_);
lean_dec_ref_known(v___x_1824_, 3);
return v___x_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_of(lean_object* v_stx_1830_){
_start:
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__2));
lean_inc(v_stx_1830_);
v___x_1832_ = l_Lean_Syntax_isOfKind(v_stx_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; 
lean_dec(v_stx_1830_);
v___x_1833_ = lean_box(0);
return v___x_1833_;
}
else
{
lean_object* v___x_1834_; lean_object* v_m_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1834_ = lean_unsigned_to_nat(0u);
v_m_1835_ = l_Lean_Syntax_getArg(v_stx_1830_, v___x_1834_);
v___x_1836_ = ((lean_object*)(l_Lean_Doc_UnorderedListItemView_of___closed__4));
lean_inc(v_m_1835_);
v___x_1837_ = l_Lean_Syntax_isOfKind(v_m_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
lean_dec(v_m_1835_);
lean_dec(v_stx_1830_);
v___x_1838_ = lean_box(0);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1839_ = l_Lean_TSyntax_getVersoDelimiter(v_m_1835_);
v___x_1840_ = lean_string_utf8_byte_size(v___x_1839_);
v___x_1841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1834_);
lean_ctor_set(v___x_1841_, 2, v___x_1840_);
v___x_1842_ = l_String_Slice_Pos_get_x3f(v___x_1841_, v___x_1834_);
lean_dec_ref_known(v___x_1841_, 3);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1843_; 
lean_dec(v_m_1835_);
lean_dec(v_stx_1830_);
v___x_1843_ = lean_box(0);
return v___x_1843_;
}
else
{
lean_object* v_val_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1863_; 
v_val_1844_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1846_ = v___x_1842_;
v_isShared_1847_ = v_isSharedCheck_1863_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_val_1844_);
lean_dec(v___x_1842_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1863_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint32_t v___x_1848_; uint32_t v___x_1849_; uint8_t v___x_1850_; 
v___x_1848_ = 48;
v___x_1849_ = lean_unbox_uint32(v_val_1844_);
v___x_1850_ = lean_uint32_dec_le(v___x_1848_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; 
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_dec(v_m_1835_);
lean_dec(v_stx_1830_);
v___x_1851_ = lean_box(0);
return v___x_1851_;
}
else
{
uint32_t v___x_1852_; uint32_t v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = 57;
v___x_1853_ = lean_unbox_uint32(v_val_1844_);
lean_dec(v_val_1844_);
v___x_1854_ = lean_uint32_dec_le(v___x_1853_, v___x_1852_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; 
lean_del_object(v___x_1846_);
lean_dec(v_m_1835_);
lean_dec(v_stx_1830_);
v___x_1855_ = lean_box(0);
return v___x_1855_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_bs_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1856_ = lean_unsigned_to_nat(1u);
v___x_1857_ = l_Lean_Syntax_getArg(v_stx_1830_, v___x_1856_);
v_bs_1858_ = l_Lean_Syntax_getArgs(v___x_1857_);
lean_dec(v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1859_, 0, v_stx_1830_);
lean_ctor_set(v___x_1859_, 1, v_m_1835_);
lean_ctor_set(v___x_1859_, 2, v_bs_1858_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1859_);
v___x_1861_ = v___x_1846_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescItemView_of(lean_object* v_stx_1871_){
_start:
{
lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_Lean_Doc_DescItemView_of___closed__1));
lean_inc(v_stx_1871_);
v___x_1873_ = l_Lean_Syntax_isOfKind(v_stx_1871_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
lean_dec(v_stx_1871_);
v___x_1874_ = lean_box(0);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; lean_object* v_marker_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v_desc_1881_; lean_object* v_term_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1875_ = lean_unsigned_to_nat(0u);
v_marker_1876_ = l_Lean_Syntax_getArg(v_stx_1871_, v___x_1875_);
v___x_1877_ = lean_unsigned_to_nat(1u);
v___x_1878_ = l_Lean_Syntax_getArg(v_stx_1871_, v___x_1877_);
v___x_1879_ = lean_unsigned_to_nat(2u);
v___x_1880_ = l_Lean_Syntax_getArg(v_stx_1871_, v___x_1879_);
v_desc_1881_ = l_Lean_Syntax_getArgs(v___x_1880_);
lean_dec(v___x_1880_);
v_term_1882_ = l_Lean_Syntax_getArgs(v___x_1878_);
lean_dec(v___x_1878_);
v___x_1883_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1883_, 0, v_stx_1871_);
lean_ctor_set(v___x_1883_, 1, v_marker_1876_);
lean_ctor_set(v___x_1883_, 2, v_term_1882_);
lean_ctor_set(v___x_1883_, 3, v_desc_1881_);
v___x_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ParaView_of(lean_object* v_stx_1900_){
_start:
{
lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = ((lean_object*)(l_Lean_Doc_ParaView_of___closed__2));
lean_inc(v_stx_1900_);
v___x_1902_ = l_Lean_Syntax_isOfKind(v_stx_1900_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
lean_dec(v_stx_1900_);
v___x_1903_ = lean_box(0);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v_inl_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = l_Lean_Syntax_getArg(v_stx_1900_, v___x_1904_);
v_inl_1906_ = l_Lean_Syntax_getArgs(v___x_1905_);
lean_dec(v___x_1905_);
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_stx_1900_);
lean_ctor_set(v___x_1907_, 1, v_inl_1906_);
v___x_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(size_t v_sz_1909_, size_t v_i_1910_, lean_object* v_bs_1911_){
_start:
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_usize_dec_lt(v_i_1910_, v_sz_1909_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_bs_1911_);
return v___x_1913_;
}
else
{
lean_object* v_v_1914_; lean_object* v___x_1915_; 
v_v_1914_ = lean_array_uget_borrowed(v_bs_1911_, v_i_1910_);
lean_inc(v_v_1914_);
v___x_1915_ = l_Lean_Doc_UnorderedListItemView_of(v_v_1914_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v___x_1916_; 
lean_dec_ref(v_bs_1911_);
v___x_1916_ = lean_box(0);
return v___x_1916_;
}
else
{
lean_object* v_val_1917_; lean_object* v___x_1918_; lean_object* v_bs_x27_1919_; size_t v___x_1920_; size_t v___x_1921_; lean_object* v___x_1922_; 
v_val_1917_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_val_1917_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1918_ = lean_unsigned_to_nat(0u);
v_bs_x27_1919_ = lean_array_uset(v_bs_1911_, v_i_1910_, v___x_1918_);
v___x_1920_ = ((size_t)1ULL);
v___x_1921_ = lean_usize_add(v_i_1910_, v___x_1920_);
v___x_1922_ = lean_array_uset(v_bs_x27_1919_, v_i_1910_, v_val_1917_);
v_i_1910_ = v___x_1921_;
v_bs_1911_ = v___x_1922_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0___boxed(lean_object* v_sz_1924_, lean_object* v_i_1925_, lean_object* v_bs_1926_){
_start:
{
size_t v_sz_boxed_1927_; size_t v_i_boxed_1928_; lean_object* v_res_1929_; 
v_sz_boxed_1927_ = lean_unbox_usize(v_sz_1924_);
lean_dec(v_sz_1924_);
v_i_boxed_1928_ = lean_unbox_usize(v_i_1925_);
lean_dec(v_i_1925_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_boxed_1927_, v_i_boxed_1928_, v_bs_1926_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListView_of(lean_object* v_stx_1937_){
_start:
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = ((lean_object*)(l_Lean_Doc_UnorderedListView_of___closed__1));
lean_inc(v_stx_1937_);
v___x_1939_ = l_Lean_Syntax_isOfKind(v_stx_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; 
lean_dec(v_stx_1937_);
v___x_1940_ = lean_box(0);
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v_items_1943_; size_t v_sz_1944_; size_t v___x_1945_; lean_object* v___x_1946_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = l_Lean_Syntax_getArg(v_stx_1937_, v___x_1941_);
v_items_1943_ = l_Lean_Syntax_getArgs(v___x_1942_);
lean_dec(v___x_1942_);
v_sz_1944_ = lean_array_size(v_items_1943_);
v___x_1945_ = ((size_t)0ULL);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_1944_, v___x_1945_, v_items_1943_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v___x_1947_; 
lean_dec(v_stx_1937_);
v___x_1947_ = lean_box(0);
return v___x_1947_;
}
else
{
lean_object* v_val_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
v_val_1948_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1950_ = v___x_1946_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_val_1948_);
lean_dec(v___x_1946_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_stx_1937_);
lean_ctor_set(v___x_1952_, 1, v_val_1948_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1952_);
v___x_1954_ = v___x_1950_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(size_t v_sz_1957_, size_t v_i_1958_, lean_object* v_bs_1959_){
_start:
{
uint8_t v___x_1960_; 
v___x_1960_ = lean_usize_dec_lt(v_i_1958_, v_sz_1957_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1961_, 0, v_bs_1959_);
return v___x_1961_;
}
else
{
lean_object* v_v_1962_; lean_object* v___x_1963_; 
v_v_1962_ = lean_array_uget_borrowed(v_bs_1959_, v_i_1958_);
lean_inc(v_v_1962_);
v___x_1963_ = l_Lean_Doc_OrderedListItemView_of(v_v_1962_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref(v_bs_1959_);
v___x_1964_ = lean_box(0);
return v___x_1964_;
}
else
{
lean_object* v_val_1965_; lean_object* v___x_1966_; lean_object* v_bs_x27_1967_; size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v_val_1965_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_val_1965_);
lean_dec_ref_known(v___x_1963_, 1);
v___x_1966_ = lean_unsigned_to_nat(0u);
v_bs_x27_1967_ = lean_array_uset(v_bs_1959_, v_i_1958_, v___x_1966_);
v___x_1968_ = ((size_t)1ULL);
v___x_1969_ = lean_usize_add(v_i_1958_, v___x_1968_);
v___x_1970_ = lean_array_uset(v_bs_x27_1967_, v_i_1958_, v_val_1965_);
v_i_1958_ = v___x_1969_;
v_bs_1959_ = v___x_1970_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0___boxed(lean_object* v_sz_1972_, lean_object* v_i_1973_, lean_object* v_bs_1974_){
_start:
{
size_t v_sz_boxed_1975_; size_t v_i_boxed_1976_; lean_object* v_res_1977_; 
v_sz_boxed_1975_ = lean_unbox_usize(v_sz_1972_);
lean_dec(v_sz_1972_);
v_i_boxed_1976_ = lean_unbox_usize(v_i_1973_);
lean_dec(v_i_1973_);
v_res_1977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_boxed_1975_, v_i_boxed_1976_, v_bs_1974_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListView_of(lean_object* v_stx_1985_){
_start:
{
lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = ((lean_object*)(l_Lean_Doc_OrderedListView_of___closed__1));
lean_inc(v_stx_1985_);
v___x_1987_ = l_Lean_Syntax_isOfKind(v_stx_1985_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; 
lean_dec(v_stx_1985_);
v___x_1988_ = lean_box(0);
return v___x_1988_;
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v_items_1991_; size_t v_sz_1992_; size_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = l_Lean_Syntax_getArg(v_stx_1985_, v___x_1989_);
v_items_1991_ = l_Lean_Syntax_getArgs(v___x_1990_);
lean_dec(v___x_1990_);
v_sz_1992_ = lean_array_size(v_items_1991_);
v___x_1993_ = ((size_t)0ULL);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_1992_, v___x_1993_, v_items_1991_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v___x_1995_; 
lean_dec(v_stx_1985_);
v___x_1995_ = lean_box(0);
return v___x_1995_;
}
else
{
lean_object* v_val_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2013_; 
v_val_1996_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1998_ = v___x_1994_;
v_isShared_1999_ = v_isSharedCheck_2013_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_val_1996_);
lean_dec(v___x_1994_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2013_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___y_2001_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2008_ = lean_array_get_size(v_val_1996_);
v___x_2009_ = lean_nat_dec_lt(v___x_1989_, v___x_2008_);
if (v___x_2009_ == 0)
{
goto v___jp_2006_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_array_fget_borrowed(v_val_1996_, v___x_1989_);
lean_inc(v___x_2010_);
v___x_2011_ = l_Lean_Doc_OrderedListItemView_number(v___x_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
goto v___jp_2006_;
}
else
{
lean_object* v_val_2012_; 
v_val_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_val_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___y_2001_ = v_val_2012_;
goto v___jp_2000_;
}
}
v___jp_2000_:
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2002_, 0, v_stx_1985_);
lean_ctor_set(v___x_2002_, 1, v___y_2001_);
lean_ctor_set(v___x_2002_, 2, v_val_1996_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2002_);
v___x_2004_ = v___x_1998_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
v___jp_2006_:
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_unsigned_to_nat(1u);
v___y_2001_ = v___x_2007_;
goto v___jp_2000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(size_t v_sz_2014_, size_t v_i_2015_, lean_object* v_bs_2016_){
_start:
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_usize_dec_lt(v_i_2015_, v_sz_2014_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_bs_2016_);
return v___x_2018_;
}
else
{
lean_object* v_v_2019_; lean_object* v___x_2020_; 
v_v_2019_ = lean_array_uget_borrowed(v_bs_2016_, v_i_2015_);
lean_inc(v_v_2019_);
v___x_2020_ = l_Lean_Doc_DescItemView_of(v_v_2019_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v___x_2021_; 
lean_dec_ref(v_bs_2016_);
v___x_2021_ = lean_box(0);
return v___x_2021_;
}
else
{
lean_object* v_val_2022_; lean_object* v___x_2023_; lean_object* v_bs_x27_2024_; size_t v___x_2025_; size_t v___x_2026_; lean_object* v___x_2027_; 
v_val_2022_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_val_2022_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2023_ = lean_unsigned_to_nat(0u);
v_bs_x27_2024_ = lean_array_uset(v_bs_2016_, v_i_2015_, v___x_2023_);
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_2015_, v___x_2025_);
v___x_2027_ = lean_array_uset(v_bs_x27_2024_, v_i_2015_, v_val_2022_);
v_i_2015_ = v___x_2026_;
v_bs_2016_ = v___x_2027_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0___boxed(lean_object* v_sz_2029_, lean_object* v_i_2030_, lean_object* v_bs_2031_){
_start:
{
size_t v_sz_boxed_2032_; size_t v_i_boxed_2033_; lean_object* v_res_2034_; 
v_sz_boxed_2032_ = lean_unbox_usize(v_sz_2029_);
lean_dec(v_sz_2029_);
v_i_boxed_2033_ = lean_unbox_usize(v_i_2030_);
lean_dec(v_i_2030_);
v_res_2034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_boxed_2032_, v_i_boxed_2033_, v_bs_2031_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescListView_of(lean_object* v_stx_2042_){
_start:
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = ((lean_object*)(l_Lean_Doc_DescListView_of___closed__1));
lean_inc(v_stx_2042_);
v___x_2044_ = l_Lean_Syntax_isOfKind(v_stx_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; 
lean_dec(v_stx_2042_);
v___x_2045_ = lean_box(0);
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v_items_2048_; size_t v_sz_2049_; size_t v___x_2050_; lean_object* v___x_2051_; 
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = l_Lean_Syntax_getArg(v_stx_2042_, v___x_2046_);
v_items_2048_ = l_Lean_Syntax_getArgs(v___x_2047_);
lean_dec(v___x_2047_);
v_sz_2049_ = lean_array_size(v_items_2048_);
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_2049_, v___x_2050_, v_items_2048_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v___x_2052_; 
lean_dec(v_stx_2042_);
v___x_2052_ = lean_box(0);
return v___x_2052_;
}
else
{
lean_object* v_val_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2061_; 
v_val_2053_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2055_ = v___x_2051_;
v_isShared_2056_ = v_isSharedCheck_2061_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_val_2053_);
lean_dec(v___x_2051_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2061_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2057_, 0, v_stx_2042_);
lean_ctor_set(v___x_2057_, 1, v_val_2053_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2057_);
v___x_2059_ = v___x_2055_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockquoteView_of(lean_object* v_stx_2069_){
_start:
{
lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = ((lean_object*)(l_Lean_Doc_BlockquoteView_of___closed__1));
lean_inc(v_stx_2069_);
v___x_2071_ = l_Lean_Syntax_isOfKind(v_stx_2069_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
lean_dec(v_stx_2069_);
v___x_2072_ = lean_box(0);
return v___x_2072_;
}
else
{
lean_object* v___x_2073_; lean_object* v_gt_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v_bs_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2073_ = lean_unsigned_to_nat(0u);
v_gt_2074_ = l_Lean_Syntax_getArg(v_stx_2069_, v___x_2073_);
v___x_2075_ = lean_unsigned_to_nat(1u);
v___x_2076_ = l_Lean_Syntax_getArg(v_stx_2069_, v___x_2075_);
v_bs_2077_ = l_Lean_Syntax_getArgs(v___x_2076_);
lean_dec(v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2078_, 0, v_stx_2069_);
lean_ctor_set(v___x_2078_, 1, v_gt_2074_);
lean_ctor_set(v___x_2078_, 2, v_bs_2077_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object* v_v_2080_){
_start:
{
lean_object* v_content_2081_; lean_object* v___x_2082_; 
v_content_2081_ = lean_ctor_get(v_v_2080_, 4);
v___x_2082_ = l_Lean_TSyntax_getVersoCodeBlock(v_content_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock___boxed(lean_object* v_v_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_v_2083_);
lean_dec_ref(v_v_2083_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_of(lean_object* v_stx_2104_){
_start:
{
lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__1));
lean_inc(v_stx_2104_);
v___x_2106_ = l_Lean_Syntax_isOfKind(v_stx_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; 
lean_dec(v_stx_2104_);
v___x_2107_ = lean_box(0);
return v___x_2107_;
}
else
{
lean_object* v___x_2108_; lean_object* v_openFence_2109_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v_name_2132_; lean_object* v_args_2133_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2108_ = lean_unsigned_to_nat(0u);
v_openFence_2109_ = l_Lean_Syntax_getArg(v_stx_2104_, v___x_2108_);
v___x_2146_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__5));
lean_inc(v_openFence_2109_);
v___x_2147_ = l_Lean_Syntax_isOfKind(v_openFence_2109_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; 
lean_dec(v_openFence_2109_);
lean_dec(v_stx_2104_);
v___x_2148_ = lean_box(0);
return v___x_2148_;
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2149_ = lean_unsigned_to_nat(1u);
v___x_2150_ = l_Lean_Syntax_getArg(v_stx_2104_, v___x_2149_);
v___x_2151_ = l_Lean_Syntax_isNone(v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2150_);
v___x_2153_ = l_Lean_Syntax_matchesNull(v___x_2150_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; 
lean_dec(v___x_2150_);
lean_dec(v_openFence_2109_);
lean_dec(v_stx_2104_);
v___x_2154_ = lean_box(0);
return v___x_2154_;
}
else
{
lean_object* v_name_2155_; 
v_name_2155_ = l_Lean_Syntax_getArg(v___x_2150_, v___x_2108_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2155_);
v___x_2162_ = l_Lean_Syntax_isOfKind(v_name_2155_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; 
lean_dec(v_name_2155_);
lean_dec(v___x_2150_);
lean_dec(v_openFence_2109_);
lean_dec(v_stx_2104_);
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
else
{
goto v___jp_2156_;
}
}
else
{
goto v___jp_2156_;
}
v___jp_2156_:
{
lean_object* v___x_2157_; lean_object* v_args_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2157_ = l_Lean_Syntax_getArg(v___x_2150_, v___x_2149_);
lean_dec(v___x_2150_);
v_args_2158_ = l_Lean_Syntax_getArgs(v___x_2157_);
lean_dec(v___x_2157_);
v___x_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2159_, 0, v_name_2155_);
v___x_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2160_, 0, v_args_2158_);
v_name_2132_ = v___x_2159_;
v_args_2133_ = v___x_2160_;
goto v___jp_2131_;
}
}
}
else
{
lean_object* v___x_2164_; 
lean_dec(v___x_2150_);
v___x_2164_ = lean_box(0);
v_name_2132_ = v___x_2164_;
v_args_2133_ = v___x_2164_;
goto v___jp_2131_;
}
}
v___jp_2110_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2115_, 0, v_stx_2104_);
lean_ctor_set(v___x_2115_, 1, v_openFence_2109_);
lean_ctor_set(v___x_2115_, 2, v___y_2112_);
lean_ctor_set(v___x_2115_, 3, v___y_2114_);
lean_ctor_set(v___x_2115_, 4, v___y_2111_);
lean_ctor_set(v___x_2115_, 5, v___y_2113_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
return v___x_2116_;
}
v___jp_2117_:
{
if (lean_obj_tag(v___y_2118_) == 0)
{
lean_object* v___x_2122_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0));
v___y_2111_ = v___y_2121_;
v___y_2112_ = v___y_2119_;
v___y_2113_ = v___y_2120_;
v___y_2114_ = v___x_2122_;
goto v___jp_2110_;
}
else
{
lean_object* v_val_2123_; 
v_val_2123_ = lean_ctor_get(v___y_2118_, 0);
lean_inc(v_val_2123_);
lean_dec_ref_known(v___y_2118_, 1);
v___y_2111_ = v___y_2121_;
v___y_2112_ = v___y_2119_;
v___y_2113_ = v___y_2120_;
v___y_2114_ = v_val_2123_;
goto v___jp_2110_;
}
}
v___jp_2124_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v___y_2128_);
v___x_2130_ = l_Lean_Syntax_setInfo(v___x_2129_, v___y_2126_);
v___y_2118_ = v___y_2125_;
v___y_2119_ = v___y_2127_;
v___y_2120_ = v___y_2128_;
v___y_2121_ = v___x_2130_;
goto v___jp_2117_;
}
v___jp_2131_:
{
lean_object* v___x_2134_; lean_object* v_s_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2134_ = lean_unsigned_to_nat(2u);
v_s_2135_ = l_Lean_Syntax_getArg(v_stx_2104_, v___x_2134_);
v___x_2136_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__3));
lean_inc(v_s_2135_);
v___x_2137_ = l_Lean_Syntax_isOfKind(v_s_2135_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; 
lean_dec(v_s_2135_);
lean_dec(v_args_2133_);
lean_dec(v_name_2132_);
lean_dec(v_openFence_2109_);
lean_dec(v_stx_2104_);
v___x_2138_ = lean_box(0);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; lean_object* v_closeFence_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2139_ = lean_unsigned_to_nat(3u);
v_closeFence_2140_ = l_Lean_Syntax_getArg(v_stx_2104_, v___x_2139_);
v___x_2141_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__5));
lean_inc(v_closeFence_2140_);
v___x_2142_ = l_Lean_Syntax_isOfKind(v_closeFence_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_dec(v_closeFence_2140_);
lean_dec(v_s_2135_);
lean_dec(v_args_2133_);
lean_dec(v_name_2132_);
lean_dec(v_openFence_2109_);
lean_dec(v_stx_2104_);
v___x_2143_ = lean_box(0);
return v___x_2143_;
}
else
{
uint8_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = 0;
v___x_2145_ = l_Lean_Syntax_getPos_x3f(v_s_2135_, v___x_2144_);
if (lean_obj_tag(v___x_2145_) == 0)
{
v___y_2125_ = v_args_2133_;
v___y_2126_ = v_s_2135_;
v___y_2127_ = v_name_2132_;
v___y_2128_ = v_closeFence_2140_;
goto v___jp_2124_;
}
else
{
lean_dec_ref_known(v___x_2145_, 1);
if (v___x_2106_ == 0)
{
v___y_2125_ = v_args_2133_;
v___y_2126_ = v_s_2135_;
v___y_2127_ = v_name_2132_;
v___y_2128_ = v_closeFence_2140_;
goto v___jp_2124_;
}
else
{
v___y_2118_ = v_args_2133_;
v___y_2119_ = v_name_2132_;
v___y_2120_ = v_closeFence_2140_;
v___y_2121_ = v_s_2135_;
goto v___jp_2117_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DirectiveView_of(lean_object* v_stx_2178_){
_start:
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = ((lean_object*)(l_Lean_Doc_DirectiveView_of___closed__1));
lean_inc(v_stx_2178_);
v___x_2180_ = l_Lean_Syntax_isOfKind(v_stx_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; 
lean_dec(v_stx_2178_);
v___x_2181_ = lean_box(0);
return v___x_2181_;
}
else
{
lean_object* v___x_2182_; lean_object* v_opener_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2182_ = lean_unsigned_to_nat(0u);
v_opener_2183_ = l_Lean_Syntax_getArg(v_stx_2178_, v___x_2182_);
v___x_2184_ = ((lean_object*)(l_Lean_Doc_DirectiveView_of___closed__3));
lean_inc(v_opener_2183_);
v___x_2185_ = l_Lean_Syntax_isOfKind(v_opener_2183_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
lean_dec(v_opener_2183_);
lean_dec(v_stx_2178_);
v___x_2186_ = lean_box(0);
return v___x_2186_;
}
else
{
lean_object* v___x_2187_; lean_object* v_name_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2187_ = lean_unsigned_to_nat(1u);
v_name_2188_ = l_Lean_Syntax_getArg(v_stx_2178_, v___x_2187_);
v___x_2189_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2188_);
v___x_2190_ = l_Lean_Syntax_isOfKind(v_name_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_dec(v_name_2188_);
lean_dec(v_opener_2183_);
lean_dec(v_stx_2178_);
v___x_2191_ = lean_box(0);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v_closer_2193_; uint8_t v___x_2194_; 
v___x_2192_ = lean_unsigned_to_nat(4u);
v_closer_2193_ = l_Lean_Syntax_getArg(v_stx_2178_, v___x_2192_);
lean_inc(v_closer_2193_);
v___x_2194_ = l_Lean_Syntax_isOfKind(v_closer_2193_, v___x_2184_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; 
lean_dec(v_closer_2193_);
lean_dec(v_name_2188_);
lean_dec(v_opener_2183_);
lean_dec(v_stx_2178_);
v___x_2195_ = lean_box(0);
return v___x_2195_;
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_bs_2200_; lean_object* v_args_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2196_ = lean_unsigned_to_nat(2u);
v___x_2197_ = l_Lean_Syntax_getArg(v_stx_2178_, v___x_2196_);
v___x_2198_ = lean_unsigned_to_nat(3u);
v___x_2199_ = l_Lean_Syntax_getArg(v_stx_2178_, v___x_2198_);
v_bs_2200_ = l_Lean_Syntax_getArgs(v___x_2199_);
lean_dec(v___x_2199_);
v_args_2201_ = l_Lean_Syntax_getArgs(v___x_2197_);
lean_dec(v___x_2197_);
v___x_2202_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2202_, 0, v_stx_2178_);
lean_ctor_set(v___x_2202_, 1, v_opener_2183_);
lean_ctor_set(v___x_2202_, 2, v_name_2188_);
lean_ctor_set(v___x_2202_, 3, v_args_2201_);
lean_ctor_set(v___x_2202_, 4, v_bs_2200_);
lean_ctor_set(v___x_2202_, 5, v_closer_2193_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CommandView_of(lean_object* v_stx_2211_){
_start:
{
lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = ((lean_object*)(l_Lean_Doc_CommandView_of___closed__1));
lean_inc(v_stx_2211_);
v___x_2213_ = l_Lean_Syntax_isOfKind(v_stx_2211_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_dec(v_stx_2211_);
v___x_2214_ = lean_box(0);
return v___x_2214_;
}
else
{
lean_object* v___x_2215_; lean_object* v_name_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; 
v___x_2215_ = lean_unsigned_to_nat(1u);
v_name_2216_ = l_Lean_Syntax_getArg(v_stx_2211_, v___x_2215_);
v___x_2217_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2216_);
v___x_2218_ = l_Lean_Syntax_isOfKind(v_name_2216_, v___x_2217_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; 
lean_dec(v_name_2216_);
lean_dec(v_stx_2211_);
v___x_2219_ = lean_box(0);
return v___x_2219_;
}
else
{
lean_object* v___x_2220_; lean_object* v_braceOpen_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_braceClose_2225_; lean_object* v_args_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2220_ = lean_unsigned_to_nat(0u);
v_braceOpen_2221_ = l_Lean_Syntax_getArg(v_stx_2211_, v___x_2220_);
v___x_2222_ = lean_unsigned_to_nat(2u);
v___x_2223_ = l_Lean_Syntax_getArg(v_stx_2211_, v___x_2222_);
v___x_2224_ = lean_unsigned_to_nat(3u);
v_braceClose_2225_ = l_Lean_Syntax_getArg(v_stx_2211_, v___x_2224_);
v_args_2226_ = l_Lean_Syntax_getArgs(v___x_2223_);
lean_dec(v___x_2223_);
v___x_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2227_, 0, v_stx_2211_);
lean_ctor_set(v___x_2227_, 1, v_braceOpen_2221_);
lean_ctor_set(v___x_2227_, 2, v_name_2216_);
lean_ctor_set(v___x_2227_, 3, v_args_2226_);
lean_ctor_set(v___x_2227_, 4, v_braceClose_2225_);
v___x_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_HeaderView_of(lean_object* v_stx_2242_){
_start:
{
lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_Doc_HeaderView_of___closed__1));
lean_inc(v_stx_2242_);
v___x_2244_ = l_Lean_Syntax_isOfKind(v_stx_2242_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; 
lean_dec(v_stx_2242_);
v___x_2245_ = lean_box(0);
return v___x_2245_;
}
else
{
lean_object* v___x_2246_; lean_object* v_marker_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2246_ = lean_unsigned_to_nat(0u);
v_marker_2247_ = l_Lean_Syntax_getArg(v_stx_2242_, v___x_2246_);
v___x_2248_ = ((lean_object*)(l_Lean_Doc_HeaderView_of___closed__3));
lean_inc(v_marker_2247_);
v___x_2249_ = l_Lean_Syntax_isOfKind(v_marker_2247_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; 
lean_dec(v_marker_2247_);
lean_dec(v_stx_2242_);
v___x_2250_ = lean_box(0);
return v___x_2250_;
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v_content_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = l_Lean_Syntax_getArg(v_stx_2242_, v___x_2251_);
v_content_2253_ = l_Lean_Syntax_getArgs(v___x_2252_);
lean_dec(v___x_2252_);
v___x_2254_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_2247_);
v___x_2255_ = lean_string_length(v___x_2254_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = lean_nat_sub(v___x_2255_, v___x_2251_);
v___x_2257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2257_, 0, v_stx_2242_);
lean_ctor_set(v___x_2257_, 1, v_marker_2247_);
lean_ctor_set(v___x_2257_, 2, v___x_2256_);
lean_ctor_set(v___x_2257_, 3, v_content_2253_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName(lean_object* v_v_2259_){
_start:
{
lean_object* v_name_2260_; lean_object* v___x_2261_; 
v_name_2260_ = lean_ctor_get(v_v_2259_, 2);
v___x_2261_ = l_Lean_TSyntax_getVersoRefName(v_name_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName___boxed(lean_object* v_v_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Doc_LinkRefView_getName(v_v_2262_);
lean_dec_ref(v_v_2262_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object* v_v_2264_){
_start:
{
lean_object* v_url_2265_; lean_object* v___x_2266_; 
v_url_2265_ = lean_ctor_get(v_v_2264_, 4);
v___x_2266_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_url_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl___boxed(lean_object* v_v_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Doc_LinkRefView_getUrl(v_v_2267_);
lean_dec_ref(v_v_2267_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_of(lean_object* v_stx_2282_){
_start:
{
lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__1));
lean_inc(v_stx_2282_);
v___x_2284_ = l_Lean_Syntax_isOfKind(v_stx_2282_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; 
lean_dec(v_stx_2282_);
v___x_2285_ = lean_box(0);
return v___x_2285_;
}
else
{
lean_object* v___x_2286_; lean_object* v_name_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2286_ = lean_unsigned_to_nat(1u);
v_name_2287_ = l_Lean_Syntax_getArg(v_stx_2282_, v___x_2286_);
v___x_2288_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_2287_);
v___x_2289_ = l_Lean_Syntax_isOfKind(v_name_2287_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; 
lean_dec(v_name_2287_);
lean_dec(v_stx_2282_);
v___x_2290_ = lean_box(0);
return v___x_2290_;
}
else
{
lean_object* v___x_2291_; lean_object* v_url_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2291_ = lean_unsigned_to_nat(3u);
v_url_2292_ = l_Lean_Syntax_getArg(v_stx_2282_, v___x_2291_);
v___x_2293_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__3));
lean_inc(v_url_2292_);
v___x_2294_ = l_Lean_Syntax_isOfKind(v_url_2292_, v___x_2293_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; 
lean_dec(v_url_2292_);
lean_dec(v_name_2287_);
lean_dec(v_stx_2282_);
v___x_2295_ = lean_box(0);
return v___x_2295_;
}
else
{
lean_object* v___x_2296_; lean_object* v_opener_2297_; lean_object* v___x_2298_; lean_object* v_closer_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2296_ = lean_unsigned_to_nat(0u);
v_opener_2297_ = l_Lean_Syntax_getArg(v_stx_2282_, v___x_2296_);
v___x_2298_ = lean_unsigned_to_nat(2u);
v_closer_2299_ = l_Lean_Syntax_getArg(v_stx_2282_, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2300_, 0, v_stx_2282_);
lean_ctor_set(v___x_2300_, 1, v_opener_2297_);
lean_ctor_set(v___x_2300_, 2, v_name_2287_);
lean_ctor_set(v___x_2300_, 3, v_closer_2299_);
lean_ctor_set(v___x_2300_, 4, v_url_2292_);
v___x_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object* v_v_2302_){
_start:
{
lean_object* v_name_2303_; lean_object* v___x_2304_; 
v_name_2303_ = lean_ctor_get(v_v_2302_, 2);
v___x_2304_ = l_Lean_TSyntax_getVersoRefName(v_name_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName___boxed(lean_object* v_v_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_Doc_FootnoteRefView_getName(v_v_2305_);
lean_dec_ref(v_v_2305_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_of(lean_object* v_stx_2314_){
_start:
{
lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_Doc_FootnoteRefView_of___closed__1));
lean_inc(v_stx_2314_);
v___x_2316_ = l_Lean_Syntax_isOfKind(v_stx_2314_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; 
lean_dec(v_stx_2314_);
v___x_2317_ = lean_box(0);
return v___x_2317_;
}
else
{
lean_object* v___x_2318_; lean_object* v_name_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2318_ = lean_unsigned_to_nat(1u);
v_name_2319_ = l_Lean_Syntax_getArg(v_stx_2314_, v___x_2318_);
v___x_2320_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__6));
lean_inc(v_name_2319_);
v___x_2321_ = l_Lean_Syntax_isOfKind(v_name_2319_, v___x_2320_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; 
lean_dec(v_name_2319_);
lean_dec(v_stx_2314_);
v___x_2322_ = lean_box(0);
return v___x_2322_;
}
else
{
lean_object* v___x_2323_; lean_object* v_opener_2324_; lean_object* v___x_2325_; lean_object* v_closer_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v_content_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2323_ = lean_unsigned_to_nat(0u);
v_opener_2324_ = l_Lean_Syntax_getArg(v_stx_2314_, v___x_2323_);
v___x_2325_ = lean_unsigned_to_nat(2u);
v_closer_2326_ = l_Lean_Syntax_getArg(v_stx_2314_, v___x_2325_);
v___x_2327_ = lean_unsigned_to_nat(3u);
v___x_2328_ = l_Lean_Syntax_getArg(v_stx_2314_, v___x_2327_);
v_content_2329_ = l_Lean_Syntax_getArgs(v___x_2328_);
lean_dec(v___x_2328_);
v___x_2330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2330_, 0, v_stx_2314_);
lean_ctor_set(v___x_2330_, 1, v_opener_2324_);
lean_ctor_set(v___x_2330_, 2, v_name_2319_);
lean_ctor_set(v___x_2330_, 3, v_closer_2326_);
lean_ctor_set(v___x_2330_, 4, v_content_2329_);
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
return v___x_2331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(size_t v_sz_2332_, size_t v_i_2333_, lean_object* v_bs_2334_){
_start:
{
uint8_t v___x_2335_; 
v___x_2335_ = lean_usize_dec_lt(v_i_2333_, v_sz_2332_);
if (v___x_2335_ == 0)
{
return v_bs_2334_;
}
else
{
lean_object* v_v_2336_; lean_object* v___x_2337_; lean_object* v_bs_x27_2338_; size_t v___x_2339_; size_t v___x_2340_; lean_object* v___x_2341_; 
v_v_2336_ = lean_array_uget(v_bs_2334_, v_i_2333_);
v___x_2337_ = lean_unsigned_to_nat(0u);
v_bs_x27_2338_ = lean_array_uset(v_bs_2334_, v_i_2333_, v___x_2337_);
v___x_2339_ = ((size_t)1ULL);
v___x_2340_ = lean_usize_add(v_i_2333_, v___x_2339_);
v___x_2341_ = lean_array_uset(v_bs_x27_2338_, v_i_2333_, v_v_2336_);
v_i_2333_ = v___x_2340_;
v_bs_2334_ = v___x_2341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0___boxed(lean_object* v_sz_2343_, lean_object* v_i_2344_, lean_object* v_bs_2345_){
_start:
{
size_t v_sz_boxed_2346_; size_t v_i_boxed_2347_; lean_object* v_res_2348_; 
v_sz_boxed_2346_ = lean_unbox_usize(v_sz_2343_);
lean_dec(v_sz_2343_);
v_i_boxed_2347_ = lean_unbox_usize(v_i_2344_);
lean_dec(v_i_2344_);
v_res_2348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_boxed_2346_, v_i_boxed_2347_, v_bs_2345_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields(lean_object* v_v_2349_){
_start:
{
lean_object* v_contents_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; size_t v_sz_2354_; size_t v___x_2355_; lean_object* v___x_2356_; 
v_contents_2350_ = lean_ctor_get(v_v_2349_, 2);
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = l_Lean_Syntax_getArg(v_contents_2350_, v___x_2351_);
v___x_2353_ = l_Lean_Syntax_getSepArgs(v___x_2352_);
lean_dec(v___x_2352_);
v_sz_2354_ = lean_array_size(v___x_2353_);
v___x_2355_ = ((size_t)0ULL);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_2354_, v___x_2355_, v___x_2353_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields___boxed(lean_object* v_v_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_Doc_MetadataView_fields(v_v_2357_);
lean_dec_ref(v_v_2357_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_of(lean_object* v_stx_2373_){
_start:
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Lean_Doc_MetadataView_of___closed__1));
lean_inc(v_stx_2373_);
v___x_2375_ = l_Lean_Syntax_isOfKind(v_stx_2373_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
lean_dec(v_stx_2373_);
v___x_2376_ = lean_box(0);
return v___x_2376_;
}
else
{
lean_object* v___x_2377_; lean_object* v_contents_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2377_ = lean_unsigned_to_nat(1u);
v_contents_2378_ = l_Lean_Syntax_getArg(v_stx_2373_, v___x_2377_);
v___x_2379_ = ((lean_object*)(l_Lean_Doc_MetadataView_of___closed__4));
lean_inc(v_contents_2378_);
v___x_2380_ = l_Lean_Syntax_isOfKind(v_contents_2378_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
lean_dec(v_contents_2378_);
lean_dec(v_stx_2373_);
v___x_2381_ = lean_box(0);
return v___x_2381_;
}
else
{
lean_object* v___x_2382_; lean_object* v_opener_2383_; lean_object* v___x_2384_; lean_object* v_closer_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2382_ = lean_unsigned_to_nat(0u);
v_opener_2383_ = l_Lean_Syntax_getArg(v_stx_2373_, v___x_2382_);
v___x_2384_ = lean_unsigned_to_nat(2u);
v_closer_2385_ = l_Lean_Syntax_getArg(v_stx_2373_, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2386_, 0, v_stx_2373_);
lean_ctor_set(v___x_2386_, 1, v_opener_2383_);
lean_ctor_set(v___x_2386_, 2, v_contents_2378_);
lean_ctor_set(v___x_2386_, 3, v_closer_2385_);
v___x_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx(lean_object* v_x_2388_){
_start:
{
switch(lean_obj_tag(v_x_2388_))
{
case 0:
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_unsigned_to_nat(0u);
return v___x_2389_;
}
case 1:
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_unsigned_to_nat(1u);
return v___x_2390_;
}
case 2:
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_unsigned_to_nat(2u);
return v___x_2391_;
}
case 3:
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_unsigned_to_nat(3u);
return v___x_2392_;
}
case 4:
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_unsigned_to_nat(4u);
return v___x_2393_;
}
case 5:
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_unsigned_to_nat(5u);
return v___x_2394_;
}
case 6:
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_unsigned_to_nat(6u);
return v___x_2395_;
}
case 7:
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_unsigned_to_nat(7u);
return v___x_2396_;
}
case 8:
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_unsigned_to_nat(8u);
return v___x_2397_;
}
case 9:
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_unsigned_to_nat(9u);
return v___x_2398_;
}
case 10:
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_unsigned_to_nat(10u);
return v___x_2399_;
}
default: 
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_unsigned_to_nat(11u);
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___boxed(lean_object* v_x_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_Doc_BlockView_ctorIdx(v_x_2401_);
lean_dec_ref(v_x_2401_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___redArg(lean_object* v_t_2403_, lean_object* v_k_2404_){
_start:
{
lean_object* v_view_2405_; lean_object* v___x_2406_; 
v_view_2405_ = lean_ctor_get(v_t_2403_, 0);
lean_inc_ref(v_view_2405_);
lean_dec_ref(v_t_2403_);
v___x_2406_ = lean_apply_1(v_k_2404_, v_view_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim(lean_object* v_motive_2407_, lean_object* v_ctorIdx_2408_, lean_object* v_t_2409_, lean_object* v_h_2410_, lean_object* v_k_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2409_, v_k_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___boxed(lean_object* v_motive_2413_, lean_object* v_ctorIdx_2414_, lean_object* v_t_2415_, lean_object* v_h_2416_, lean_object* v_k_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Doc_BlockView_ctorElim(v_motive_2413_, v_ctorIdx_2414_, v_t_2415_, v_h_2416_, v_k_2417_);
lean_dec(v_ctorIdx_2414_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim___redArg(lean_object* v_t_2419_, lean_object* v_para_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2419_, v_para_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim(lean_object* v_motive_2422_, lean_object* v_t_2423_, lean_object* v_h_2424_, lean_object* v_para_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2423_, v_para_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim___redArg(lean_object* v_t_2427_, lean_object* v_ul_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2427_, v_ul_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim(lean_object* v_motive_2430_, lean_object* v_t_2431_, lean_object* v_h_2432_, lean_object* v_ul_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2431_, v_ul_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim___redArg(lean_object* v_t_2435_, lean_object* v_ol_2436_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2435_, v_ol_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim(lean_object* v_motive_2438_, lean_object* v_t_2439_, lean_object* v_h_2440_, lean_object* v_ol_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2439_, v_ol_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim___redArg(lean_object* v_t_2443_, lean_object* v_dl_2444_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2443_, v_dl_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim(lean_object* v_motive_2446_, lean_object* v_t_2447_, lean_object* v_h_2448_, lean_object* v_dl_2449_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2447_, v_dl_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim___redArg(lean_object* v_t_2451_, lean_object* v_blockquote_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2451_, v_blockquote_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim(lean_object* v_motive_2454_, lean_object* v_t_2455_, lean_object* v_h_2456_, lean_object* v_blockquote_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2455_, v_blockquote_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim___redArg(lean_object* v_t_2459_, lean_object* v_codeblock_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2459_, v_codeblock_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim(lean_object* v_motive_2462_, lean_object* v_t_2463_, lean_object* v_h_2464_, lean_object* v_codeblock_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2463_, v_codeblock_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim___redArg(lean_object* v_t_2467_, lean_object* v_directive_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2467_, v_directive_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim(lean_object* v_motive_2470_, lean_object* v_t_2471_, lean_object* v_h_2472_, lean_object* v_directive_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2471_, v_directive_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim___redArg(lean_object* v_t_2475_, lean_object* v_command_2476_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2475_, v_command_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim(lean_object* v_motive_2478_, lean_object* v_t_2479_, lean_object* v_h_2480_, lean_object* v_command_2481_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2479_, v_command_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim___redArg(lean_object* v_t_2483_, lean_object* v_header_2484_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2483_, v_header_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim(lean_object* v_motive_2486_, lean_object* v_t_2487_, lean_object* v_h_2488_, lean_object* v_header_2489_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2487_, v_header_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim___redArg(lean_object* v_t_2491_, lean_object* v_linkRef_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2491_, v_linkRef_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim(lean_object* v_motive_2494_, lean_object* v_t_2495_, lean_object* v_h_2496_, lean_object* v_linkRef_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2495_, v_linkRef_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim___redArg(lean_object* v_t_2499_, lean_object* v_footnoteRef_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2499_, v_footnoteRef_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim(lean_object* v_motive_2502_, lean_object* v_t_2503_, lean_object* v_h_2504_, lean_object* v_footnoteRef_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2503_, v_footnoteRef_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim___redArg(lean_object* v_t_2507_, lean_object* v_metadata_2508_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2507_, v_metadata_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim(lean_object* v_motive_2510_, lean_object* v_t_2511_, lean_object* v_h_2512_, lean_object* v_metadata_2513_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_2511_, v_metadata_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeParaViewBlockView___lam__0(lean_object* v_view_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_view_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0(lean_object* v_view_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_view_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0(lean_object* v_view_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_view_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDescListViewBlockView___lam__0(lean_object* v_view_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_view_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0(lean_object* v_view_2535_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_view_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0(lean_object* v_view_2539_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_view_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0(lean_object* v_view_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2544_, 0, v_view_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCommandViewBlockView___lam__0(lean_object* v_view_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_view_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___lam__0(lean_object* v_view_2551_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_view_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0(lean_object* v_view_2555_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_view_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0(lean_object* v_view_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_view_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___lam__0(lean_object* v_view_2563_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_view_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx(lean_object* v_x_2567_){
_start:
{
lean_object* v_view_2568_; lean_object* v_stx_2569_; 
v_view_2568_ = lean_ctor_get(v_x_2567_, 0);
v_stx_2569_ = lean_ctor_get(v_view_2568_, 0);
lean_inc(v_stx_2569_);
return v_stx_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx___boxed(lean_object* v_x_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Doc_BlockView_stx(v_x_2570_);
lean_dec_ref(v_x_2570_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_of(lean_object* v_stx_2572_){
_start:
{
lean_object* v___x_2573_; 
lean_inc(v_stx_2572_);
v___x_2573_ = l_Lean_Doc_ParaView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2574_; 
lean_inc(v_stx_2572_);
v___x_2574_ = l_Lean_Doc_UnorderedListView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v___x_2575_; 
lean_inc(v_stx_2572_);
v___x_2575_ = l_Lean_Doc_OrderedListView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v___x_2576_; 
lean_inc(v_stx_2572_);
v___x_2576_ = l_Lean_Doc_DescListView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v___x_2577_; 
lean_inc(v_stx_2572_);
v___x_2577_ = l_Lean_Doc_BlockquoteView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v___x_2578_; 
lean_inc(v_stx_2572_);
v___x_2578_ = l_Lean_Doc_CodeBlockView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v___x_2579_; 
lean_inc(v_stx_2572_);
v___x_2579_ = l_Lean_Doc_DirectiveView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v___x_2580_; 
lean_inc(v_stx_2572_);
v___x_2580_ = l_Lean_Doc_CommandView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v___x_2581_; 
lean_inc(v_stx_2572_);
v___x_2581_ = l_Lean_Doc_HeaderView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v___x_2582_; 
lean_inc(v_stx_2572_);
v___x_2582_ = l_Lean_Doc_LinkRefView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v___x_2583_; 
lean_inc(v_stx_2572_);
v___x_2583_ = l_Lean_Doc_FootnoteRefView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_Doc_MetadataView_of(v_stx_2572_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_box(0);
return v___x_2585_;
}
else
{
lean_object* v_val_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2594_; 
v_val_2586_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2588_ = v___x_2584_;
v_isShared_2589_ = v_isSharedCheck_2594_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_val_2586_);
lean_dec(v___x_2584_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2594_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2590_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_2590_, 0, v_val_2586_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2590_);
v___x_2592_ = v___x_2588_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
else
{
lean_object* v_val_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_stx_2572_);
v_val_2595_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2597_ = v___x_2583_;
v_isShared_2598_ = v_isSharedCheck_2603_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_val_2595_);
lean_dec(v___x_2583_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2603_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2599_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_val_2595_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2599_);
v___x_2601_ = v___x_2597_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
else
{
lean_object* v_val_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2612_; 
lean_dec(v_stx_2572_);
v_val_2604_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2606_ = v___x_2582_;
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_val_2604_);
lean_dec(v___x_2582_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2608_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_2608_, 0, v_val_2604_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2608_);
v___x_2610_ = v___x_2606_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v_val_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_stx_2572_);
v_val_2613_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2615_ = v___x_2581_;
v_isShared_2616_ = v_isSharedCheck_2621_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_val_2613_);
lean_dec(v___x_2581_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2621_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2617_; lean_object* v___x_2619_; 
v___x_2617_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2617_, 0, v_val_2613_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2617_);
v___x_2619_ = v___x_2615_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_val_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_stx_2572_);
v_val_2622_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2624_ = v___x_2580_;
v_isShared_2625_ = v_isSharedCheck_2630_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_val_2622_);
lean_dec(v___x_2580_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2630_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2626_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_val_2622_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2626_);
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_val_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_stx_2572_);
v_val_2631_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2633_ = v___x_2579_;
v_isShared_2634_ = v_isSharedCheck_2639_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_val_2631_);
lean_dec(v___x_2579_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2639_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2635_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_2635_, 0, v_val_2631_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2635_);
v___x_2637_ = v___x_2633_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v_val_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_stx_2572_);
v_val_2640_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2642_ = v___x_2578_;
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_val_2640_);
lean_dec(v___x_2578_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2644_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_val_2640_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2644_);
v___x_2646_ = v___x_2642_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
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
else
{
lean_object* v_val_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v_stx_2572_);
v_val_2649_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2651_ = v___x_2577_;
v_isShared_2652_ = v_isSharedCheck_2657_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_val_2649_);
lean_dec(v___x_2577_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2657_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2653_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_val_2649_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2653_);
v___x_2655_ = v___x_2651_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_val_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2666_; 
lean_dec(v_stx_2572_);
v_val_2658_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2660_ = v___x_2576_;
v_isShared_2661_ = v_isSharedCheck_2666_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_val_2658_);
lean_dec(v___x_2576_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2666_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_val_2658_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2662_);
v___x_2664_ = v___x_2660_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
else
{
lean_object* v_val_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_stx_2572_);
v_val_2667_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2669_ = v___x_2575_;
v_isShared_2670_ = v_isSharedCheck_2675_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_val_2667_);
lean_dec(v___x_2575_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2675_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2671_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2671_, 0, v_val_2667_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2671_);
v___x_2673_ = v___x_2669_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_object* v_val_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v_stx_2572_);
v_val_2676_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2678_ = v___x_2574_;
v_isShared_2679_ = v_isSharedCheck_2684_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_val_2676_);
lean_dec(v___x_2574_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2684_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_val_2676_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2680_);
v___x_2682_ = v___x_2678_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v_val_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_stx_2572_);
v_val_2685_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2687_ = v___x_2573_;
v_isShared_2688_ = v_isSharedCheck_2693_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_val_2685_);
lean_dec(v___x_2573_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2693_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v_val_2685_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2689_);
v___x_2691_ = v___x_2687_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoInline_view(lean_object* v_stx_2694_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_Doc_InlineView_of(v_stx_2694_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v___x_2696_; 
v___x_2696_ = ((lean_object*)(l_Lean_Doc_instInhabitedInlineView_default));
return v___x_2696_;
}
else
{
lean_object* v_val_2697_; 
v_val_2697_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v___x_2695_, 1);
return v_val_2697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoBlock_view(lean_object* v_stx_2698_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_Doc_BlockView_of(v_stx_2698_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v___x_2700_; 
v___x_2700_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlockView_default));
return v___x_2700_;
}
else
{
lean_object* v_val_2701_; 
v_val_2701_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_val_2701_);
lean_dec_ref_known(v___x_2699_, 1);
return v_val_2701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_migrateInlines(lean_object* v_xs_2702_){
_start:
{
lean_inc_ref(v_xs_2702_);
return v_xs_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_migrateInlines___boxed(lean_object* v_xs_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_Doc_migrateInlines(v_xs_2703_);
lean_dec_ref(v_xs_2703_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_migrateBlocks(lean_object* v_xs_2705_){
_start:
{
lean_inc_ref(v_xs_2705_);
return v_xs_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_migrateBlocks___boxed(lean_object* v_xs_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_Doc_migrateBlocks(v_xs_2706_);
lean_dec_ref(v_xs_2706_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit(lean_object* v_s_2708_){
_start:
{
lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = l_Lean_TSyntax_getString(v_s_2708_);
v___x_2710_ = 0;
v___x_2711_ = l_Lean_Doc_mkVersoCodeFrom(v_s_2708_, v___x_2709_, v___x_2710_);
lean_dec_ref(v___x_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit___boxed(lean_object* v_s_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_Doc_versoCodeOfStrLit(v_s_2712_);
lean_dec(v_s_2712_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit(lean_object* v_s_2714_){
_start:
{
lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = l_Lean_TSyntax_getString(v_s_2714_);
v___x_2716_ = 0;
v___x_2717_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_s_2714_, v___x_2715_, v___x_2716_);
lean_dec_ref(v___x_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit___boxed(lean_object* v_s_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Doc_versoCodeBlockOfStrLit(v_s_2718_);
lean_dec(v_s_2718_);
return v_res_2719_;
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
