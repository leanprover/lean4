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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
extern lean_object* l_Lean_Doc_versoRefKind;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_Doc_versoImageAltKind;
lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object*);
extern lean_object* l_Lean_Doc_versoLinkUrlKind;
lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object*);
lean_object* l_Lean_Doc_longestBacktickRun(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Doc_versoTextKind;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_TSyntax_getVersoCode(lean_object*);
lean_object* l_Lean_TSyntax_getVersoTextSource(lean_object*);
lean_object* l_Lean_TSyntax_getVersoDelimiter(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_TSyntax_getVersoImageAlt(lean_object*);
lean_object* l_Lean_TSyntax_getVersoText(lean_object*);
lean_object* l_Lean_TSyntax_getVersoLinkRefUrl(lean_object*);
lean_object* lean_string_length(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "codeDelimiter"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__0 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 116, 135, 82, 225, 37, 203, 104)}};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value;
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "codeBlockFence"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__0 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 154, 39, 84, 226, 168, 56, 199)}};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value;
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "```"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__2 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "directiveDelimiter"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__0 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 28, 38, 38, 72, 11, 173, 25)}};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value;
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ":::"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__2 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0_value),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2_value)}};
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asAtom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asAtom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asNode(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_argValToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Doc_argValToParser___closed__0 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__0_value;
static const lean_string_object l_Lean_Doc_argValToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "arg_ident"};
static const lean_object* l_Lean_Doc_argValToParser___closed__1 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__1_value;
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_argValToParser___closed__1_value),LEAN_SCALAR_PTR_LITERAL(73, 49, 249, 222, 84, 35, 6, 34)}};
static const lean_object* l_Lean_Doc_argValToParser___closed__2 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__2_value;
static const lean_string_object l_Lean_Doc_argValToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_num"};
static const lean_object* l_Lean_Doc_argValToParser___closed__3 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__3_value;
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_argValToParser___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 247, 226, 130, 46, 200, 13, 201)}};
static const lean_object* l_Lean_Doc_argValToParser___closed__4 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__4_value;
static const lean_string_object l_Lean_Doc_argValToParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_str"};
static const lean_object* l_Lean_Doc_argValToParser___closed__5 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__5_value;
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__6_value_aux_2),((lean_object*)&l_Lean_Doc_argValToParser___closed__5_value),LEAN_SCALAR_PTR_LITERAL(28, 110, 66, 227, 168, 59, 232, 226)}};
static const lean_object* l_Lean_Doc_argValToParser___closed__6 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Doc_argValToParser(lean_object*);
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(151, 30, 185, 65, 40, 8, 94, 56)}};
static const lean_object* l_Lean_Doc_docArgToParser___closed__0 = (const lean_object*)&l_Lean_Doc_docArgToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(240, 209, 4, 173, 176, 102, 100, 110)}};
static const lean_object* l_Lean_Doc_docArgToParser___closed__1 = (const lean_object*)&l_Lean_Doc_docArgToParser___closed__1_value;
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 78, 240, 214, 103, 62, 217, 25)}};
static const lean_object* l_Lean_Doc_docArgToParser___closed__2 = (const lean_object*)&l_Lean_Doc_docArgToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__7_value),LEAN_SCALAR_PTR_LITERAL(156, 222, 140, 123, 199, 224, 2, 54)}};
static const lean_object* l_Lean_Doc_docArgToParser___closed__3 = (const lean_object*)&l_Lean_Doc_docArgToParser___closed__3_value;
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__9_value),LEAN_SCALAR_PTR_LITERAL(29, 0, 37, 229, 12, 38, 20, 228)}};
static const lean_object* l_Lean_Doc_docArgToParser___closed__4 = (const lean_object*)&l_Lean_Doc_docArgToParser___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Doc_docArgToParser(lean_object*);
static const lean_string_object l_Lean_Doc_linkTargetToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "url"};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__0 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 109, 202, 165, 136, 148, 125, 206)}};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__1 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__1_value;
static const lean_string_object l_Lean_Doc_linkTargetToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ref"};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__2 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(157, 197, 143, 220, 44, 158, 31, 133)}};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__3 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__3_value;
static const lean_string_object l_Lean_Doc_linkTargetToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LinkTarget"};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__4 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__4_value;
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__5_value_aux_3),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 54, 241, 38, 78, 206, 156, 5)}};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__5 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__5_value;
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__6_value_aux_2),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__6_value_aux_3),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 222, 147, 211, 241, 202, 7, 251)}};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__6 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Doc_linkTargetToParser(lean_object*);
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__0 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 30, 73, 79, 76, 254, 8, 196)}};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_inlineToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__0 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 149, 124, 218, 116, 154, 240, 105)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__1 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__1_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "emph"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__2 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 183, 215, 94, 0, 242, 191, 239)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__3 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__3_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bold"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__4 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__4_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(217, 240, 207, 144, 35, 3, 119, 11)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__5 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__5_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__6_value_aux_2),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 95, 172, 118, 77, 213, 142, 126)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__6 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__6_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inline_math"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__7 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__7_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__8_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__8_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__8_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__7_value),LEAN_SCALAR_PTR_LITERAL(39, 58, 152, 4, 55, 96, 114, 182)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__8 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__8_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "display_math"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__9 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__9_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__10_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__10_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__10_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__9_value),LEAN_SCALAR_PTR_LITERAL(185, 134, 189, 58, 202, 192, 153, 244)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__10 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__10_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__11 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__11_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__12_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__12_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__12_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__11_value),LEAN_SCALAR_PTR_LITERAL(129, 184, 35, 28, 112, 167, 76, 80)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__12 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__12_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "image"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__13 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__13_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__14_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__14_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__14_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__13_value),LEAN_SCALAR_PTR_LITERAL(156, 113, 65, 80, 13, 110, 129, 61)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__14 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__14_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "footnote"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__15 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__15_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__16_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__16_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__16_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__15_value),LEAN_SCALAR_PTR_LITERAL(207, 87, 199, 0, 139, 133, 244, 123)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__16 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__16_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__17_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__17_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__17_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 183, 85, 224, 226, 177, 67, 207)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__17 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__17_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "role"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__18 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__18_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__19_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__19_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__19_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__18_value),LEAN_SCALAR_PTR_LITERAL(88, 39, 13, 65, 153, 69, 141, 111)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__19 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__19_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__20_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__20_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__20_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__20_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__18_value),LEAN_SCALAR_PTR_LITERAL(163, 233, 178, 241, 96, 238, 218, 92)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__20 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__20_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__21 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__21_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__22 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__22_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Doc_inlineToParser___closed__23 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__23_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__24 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__24_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__25_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__25_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__25_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__25_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__25_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__15_value),LEAN_SCALAR_PTR_LITERAL(44, 121, 147, 210, 143, 103, 0, 217)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__25 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__25_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__26 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__26_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__27_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__27_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__27_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__27_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__27_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__13_value),LEAN_SCALAR_PTR_LITERAL(63, 170, 102, 209, 119, 14, 254, 233)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__27 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__27_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l_Lean_Doc_inlineToParser___closed__28 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__28_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__29_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__29_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__29_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__29_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__11_value),LEAN_SCALAR_PTR_LITERAL(250, 237, 8, 103, 58, 149, 183, 251)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__29 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__29_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__30_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__30_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__30_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__30_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__30_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__9_value),LEAN_SCALAR_PTR_LITERAL(194, 39, 73, 53, 10, 24, 181, 77)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__30 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__30_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "displayMathMarker"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__31 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__31_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__32_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__32_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__32_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__31_value),LEAN_SCALAR_PTR_LITERAL(191, 18, 116, 40, 86, 165, 207, 150)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__32 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__32_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__33 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__33_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__34_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__34_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__34_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__34_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__34_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__7_value),LEAN_SCALAR_PTR_LITERAL(52, 236, 9, 179, 133, 206, 252, 7)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__34 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__34_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "inlineMathMarker"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__35 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__35_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__36_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__36_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__36_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__35_value),LEAN_SCALAR_PTR_LITERAL(102, 9, 108, 134, 130, 7, 90, 114)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__36 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__36_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__37 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__37_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__38_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__38_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__38_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__38_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__38_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 21, 54, 220, 135, 144, 211, 134)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__38 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__38_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "boldDelimiter"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__39 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__39_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__40_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__40_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__40_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__39_value),LEAN_SCALAR_PTR_LITERAL(187, 9, 73, 54, 22, 222, 115, 214)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__40 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__40_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__41 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__41_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__42_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__42_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__42_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__42_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__42_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 215, 18, 85, 144, 91, 153, 50)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__42 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__42_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "emphDelimiter"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__43 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__43_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__44_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__44_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__44_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__43_value),LEAN_SCALAR_PTR_LITERAL(14, 57, 61, 189, 31, 180, 10, 101)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__44 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__44_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__45 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__45_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__46_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__46_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__46_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__46_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__46_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 133, 107, 199, 31, 216, 160, 200)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__46 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__46_value;
LEAN_EXPORT lean_object* l_Lean_Doc_inlineToParser(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_blockToParser_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_blockToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "para"};
static const lean_object* l_Lean_Doc_blockToParser___closed__0 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 72, 198, 245, 142, 145, 171, 144)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__1 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__1_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "blockquote"};
static const lean_object* l_Lean_Doc_blockToParser___closed__2 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(154, 37, 74, 205, 107, 38, 107, 223)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__3 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__3_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ul"};
static const lean_object* l_Lean_Doc_blockToParser___closed__4 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__4_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(248, 90, 162, 51, 92, 30, 144, 89)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__5 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__5_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ol"};
static const lean_object* l_Lean_Doc_blockToParser___closed__6 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__6_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__7_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__7_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__7_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 73, 192, 118, 161, 88, 51, 173)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__7 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__7_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "dl"};
static const lean_object* l_Lean_Doc_blockToParser___closed__8 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__8_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__9_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__9_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__9_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__8_value),LEAN_SCALAR_PTR_LITERAL(13, 49, 30, 64, 139, 101, 177, 168)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__9 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__9_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "codeblock"};
static const lean_object* l_Lean_Doc_blockToParser___closed__10 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__10_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__11_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__11_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__11_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__10_value),LEAN_SCALAR_PTR_LITERAL(228, 242, 241, 127, 13, 6, 27, 177)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__11 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__11_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "directive"};
static const lean_object* l_Lean_Doc_blockToParser___closed__12 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__12_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__13_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__13_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__13_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__12_value),LEAN_SCALAR_PTR_LITERAL(59, 236, 126, 236, 245, 181, 4, 182)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__13 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__13_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Doc_blockToParser___closed__14 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__14_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__15_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__15_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__15_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__14_value),LEAN_SCALAR_PTR_LITERAL(163, 102, 246, 27, 44, 229, 232, 70)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__15 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__15_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Doc_blockToParser___closed__16 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__16_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__17_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__17_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__17_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__16_value),LEAN_SCALAR_PTR_LITERAL(138, 131, 27, 234, 140, 72, 2, 168)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__17 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__17_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "link_ref"};
static const lean_object* l_Lean_Doc_blockToParser___closed__18 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__18_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__19_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__19_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__19_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__18_value),LEAN_SCALAR_PTR_LITERAL(37, 122, 52, 169, 192, 153, 29, 165)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__19 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__19_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "footnote_ref"};
static const lean_object* l_Lean_Doc_blockToParser___closed__20 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__20_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__21_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__21_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__21_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__20_value),LEAN_SCALAR_PTR_LITERAL(249, 7, 163, 121, 208, 236, 208, 13)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__21 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__21_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "metadata_block"};
static const lean_object* l_Lean_Doc_blockToParser___closed__22 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__22_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__23_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__23_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__23_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 201, 5, 85, 129, 97, 253, 216)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__23 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__23_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lean_Doc_blockToParser___closed__25 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__25_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Doc_blockToParser___closed__24 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__24_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__26_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__26_value_aux_1),((lean_object*)&l_Lean_Doc_blockToParser___closed__24_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__26_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__25_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__26 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__26_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Block"};
static const lean_object* l_Lean_Doc_blockToParser___closed__27 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__27_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__28_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__28_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__28_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__28_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__28_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__22_value),LEAN_SCALAR_PTR_LITERAL(99, 125, 116, 48, 167, 45, 110, 42)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__28 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__28_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__29_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__29_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__29_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__29_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__20_value),LEAN_SCALAR_PTR_LITERAL(97, 53, 29, 246, 154, 171, 121, 154)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__29 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__29_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__30_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__30_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__30_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__30_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__30_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__18_value),LEAN_SCALAR_PTR_LITERAL(141, 199, 233, 128, 119, 237, 18, 215)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__30 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__30_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__31_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__31_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__31_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__31_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__31_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__16_value),LEAN_SCALAR_PTR_LITERAL(242, 176, 128, 73, 36, 235, 244, 141)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__31 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__31_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "headerMarker"};
static const lean_object* l_Lean_Doc_blockToParser___closed__32 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__32_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__33_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__33_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__33_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__32_value),LEAN_SCALAR_PTR_LITERAL(79, 163, 210, 90, 152, 248, 144, 166)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__33 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__33_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__34_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__34_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__34_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__34_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__34_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__14_value),LEAN_SCALAR_PTR_LITERAL(11, 232, 253, 29, 141, 75, 139, 21)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__34 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__34_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__35_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__35_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__35_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__35_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__35_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__12_value),LEAN_SCALAR_PTR_LITERAL(211, 234, 1, 42, 159, 198, 19, 176)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__35 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__35_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__36_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__36_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__36_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__36_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__36_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__10_value),LEAN_SCALAR_PTR_LITERAL(76, 32, 43, 99, 217, 167, 97, 87)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__36 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__36_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Doc_mkVersoCodeFrom___closed__1_value),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0_value)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__37 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__37_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__38_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__38_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__38_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__38_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__38_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__8_value),LEAN_SCALAR_PTR_LITERAL(165, 15, 76, 66, 114, 120, 124, 74)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__38 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__38_value;
static const lean_string_object l_Lean_Doc_descItemToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "desc"};
static const lean_object* l_Lean_Doc_descItemToParser___closed__0 = (const lean_object*)&l_Lean_Doc_descItemToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_descItemToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 44, 92, 80, 93, 40, 168, 47)}};
static const lean_object* l_Lean_Doc_descItemToParser___closed__1 = (const lean_object*)&l_Lean_Doc_descItemToParser___closed__1_value;
static const lean_string_object l_Lean_Doc_listItemToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "item"};
static const lean_object* l_Lean_Doc_listItemToParser___closed__3 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__3_value;
static const lean_string_object l_Lean_Doc_descItemToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DescItem"};
static const lean_object* l_Lean_Doc_descItemToParser___closed__2 = (const lean_object*)&l_Lean_Doc_descItemToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_descItemToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 70, 30, 3, 105, 156, 130, 115)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__3_value_aux_3),((lean_object*)&l_Lean_Doc_listItemToParser___closed__3_value),LEAN_SCALAR_PTR_LITERAL(37, 193, 144, 210, 183, 212, 114, 89)}};
static const lean_object* l_Lean_Doc_descItemToParser___closed__3 = (const lean_object*)&l_Lean_Doc_descItemToParser___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_descItemToParser(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3(size_t, size_t, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___closed__0_value;
static const lean_string_object l_Lean_Doc_listItemToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "li"};
static const lean_object* l_Lean_Doc_listItemToParser___closed__0 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_listItemToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 229, 0, 156, 136, 247, 163, 99)}};
static const lean_object* l_Lean_Doc_listItemToParser___closed__1 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__1_value;
static const lean_string_object l_Lean_Doc_listItemToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ListItem"};
static const lean_object* l_Lean_Doc_listItemToParser___closed__2 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_listItemToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(154, 153, 101, 209, 126, 16, 11, 208)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__4_value_aux_3),((lean_object*)&l_Lean_Doc_listItemToParser___closed__3_value),LEAN_SCALAR_PTR_LITERAL(200, 123, 16, 134, 76, 179, 171, 228)}};
static const lean_object* l_Lean_Doc_listItemToParser___closed__4 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__4_value;
static const lean_string_object l_Lean_Doc_listItemToParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "listMarker"};
static const lean_object* l_Lean_Doc_listItemToParser___closed__5 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__5_value;
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__6_value_aux_2),((lean_object*)&l_Lean_Doc_listItemToParser___closed__5_value),LEAN_SCALAR_PTR_LITERAL(220, 134, 18, 7, 181, 33, 85, 37)}};
static const lean_object* l_Lean_Doc_listItemToParser___closed__6 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Doc_listItemToParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__39_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__39_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__39_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__39_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__39_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__6_value),LEAN_SCALAR_PTR_LITERAL(222, 199, 227, 191, 40, 60, 185, 243)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__39 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__39_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__40_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__40_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__40_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__40_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__40_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(144, 45, 1, 212, 241, 159, 201, 84)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__40 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__40_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5(size_t, size_t, lean_object*);
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__41_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__41_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__41_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__41_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__41_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 145, 178, 243, 42, 6, 105, 104)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__41 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__41_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__42_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__42_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__42_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__42_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__42_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 167, 213, 66, 92, 160, 222, 146)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__42 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__42_value;
LEAN_EXPORT lean_object* l_Lean_Doc_blockToParser(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_argValToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_docArgToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_linkTargetToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__2 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_inlineToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_descItemToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean__1___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean__1___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_blockToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__2 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__3 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__4 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__5 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__6 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__0_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__7 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__7_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__2_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__3_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__4_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__8 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__8_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__9 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value)} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__1_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3___closed__0_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value)} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4___closed__0_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value)} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__2 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_migrateInlines(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_migrateBlocks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_LinkTargetView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "versoRef"};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__0 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 44, 27, 25, 170, 146, 153, 245)}};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__1 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_LinkTargetView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "versoLinkUrl"};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__2 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(142, 188, 54, 130, 131, 60, 251, 148)}};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__3 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_of(lean_object*);
static const lean_ctor_object l_Lean_Doc_instInhabitedTextView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instInhabitedTextView_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedTextView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedTextView_default = (const lean_object*)&l_Lean_Doc_instInhabitedTextView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedTextView = (const lean_object*)&l_Lean_Doc_instInhabitedTextView_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_TextView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoText"};
static const lean_object* l_Lean_Doc_TextView_of___closed__0 = (const lean_object*)&l_Lean_Doc_TextView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_TextView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 255, 240, 17, 75, 250, 253, 95)}};
static const lean_object* l_Lean_Doc_TextView_of___closed__1 = (const lean_object*)&l_Lean_Doc_TextView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_EmphView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BoldView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_CodeView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoCode"};
static const lean_object* l_Lean_Doc_CodeView_of___closed__0 = (const lean_object*)&l_Lean_Doc_CodeView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_CodeView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 134, 52, 97, 245, 192, 23, 73)}};
static const lean_object* l_Lean_Doc_CodeView_of___closed__1 = (const lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_ImageView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "versoImageAlt"};
static const lean_object* l_Lean_Doc_ImageView_of___closed__0 = (const lean_object*)&l_Lean_Doc_ImageView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ImageView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 180, 119, 241, 128, 95, 219, 17)}};
static const lean_object* l_Lean_Doc_ImageView_of___closed__1 = (const lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinebreakView_of(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_UnorderedListItemView_of___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_UnorderedListItemView_of___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__1;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_UnorderedListItemView_of___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_number(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DescItemView_of(lean_object*);
static const lean_array_object l_Lean_Doc_instInhabitedParaView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_instInhabitedParaView_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instInhabitedParaView_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__0_value)}};
static const lean_object* l_Lean_Doc_instInhabitedParaView_default___closed__1 = (const lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedParaView_default = (const lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedParaView = (const lean_object*)&l_Lean_Doc_instInhabitedParaView_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_ParaView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DescListView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockquoteView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_CodeBlockView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "versoCodeBlock"};
static const lean_object* l_Lean_Doc_CodeBlockView_of___closed__0 = (const lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 196, 91, 225, 102, 151, 154, 53)}};
static const lean_object* l_Lean_Doc_CodeBlockView_of___closed__1 = (const lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DirectiveView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CommandView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_HeaderView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_LinkRefView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "versoLinkRefUrl"};
static const lean_object* l_Lean_Doc_LinkRefView_of___closed__0 = (const lean_object*)&l_Lean_Doc_LinkRefView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 57, 106, 22, 121, 78, 15, 41)}};
static const lean_object* l_Lean_Doc_LinkRefView_of___closed__1 = (const lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(lean_object* v_kind_323_, lean_object* v_text_324_, lean_object* v_tok_325_){
_start:
{
lean_object* v_info_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_info_326_ = l_Lean_Syntax_getHeadInfo(v_tok_325_);
lean_inc(v_info_326_);
v___x_327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_327_, 0, v_info_326_);
lean_ctor_set(v___x_327_, 1, v_text_324_);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_mk_empty_array_with_capacity(v___x_328_);
v___x_330_ = lean_array_push(v___x_329_, v___x_327_);
v___x_331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_331_, 0, v_info_326_);
lean_ctor_set(v___x_331_, 1, v_kind_323_);
lean_ctor_set(v___x_331_, 2, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter___boxed(lean_object* v_kind_332_, lean_object* v_text_333_, lean_object* v_tok_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v_kind_332_, v_text_333_, v_tok_334_);
lean_dec(v_tok_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter_spec__0(lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
lean_object* v_zero_338_; uint8_t v_isZero_339_; 
v_zero_338_ = lean_unsigned_to_nat(0u);
v_isZero_339_ = lean_nat_dec_eq(v_x_336_, v_zero_338_);
if (v_isZero_339_ == 1)
{
lean_dec(v_x_336_);
return v_x_337_;
}
else
{
uint32_t v___x_340_; lean_object* v_one_341_; lean_object* v_n_342_; lean_object* v___x_343_; 
v___x_340_ = 96;
v_one_341_ = lean_unsigned_to_nat(1u);
v_n_342_ = lean_nat_sub(v_x_336_, v_one_341_);
lean_dec(v_x_336_);
v___x_343_ = lean_string_push(v_x_337_, v___x_340_);
v_x_336_ = v_n_342_;
v_x_337_ = v___x_343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter(lean_object* v_value_352_, lean_object* v_tok_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_354_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1));
v___x_355_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2));
v___x_356_ = l_Lean_Doc_longestBacktickRun(v_value_352_);
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_nat_add(v___x_356_, v___x_357_);
lean_dec(v___x_356_);
v___x_359_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter_spec__0(v___x_358_, v___x_355_);
v___x_360_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_354_, v___x_359_, v_tok_353_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___boxed(lean_object* v_value_361_, lean_object* v_tok_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter(v_value_361_, v_tok_362_);
lean_dec(v_tok_362_);
lean_dec_ref(v_value_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence(lean_object* v_tok_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1));
v___x_373_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__2));
v___x_374_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_372_, v___x_373_, v_tok_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence___boxed(lean_object* v_tok_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_DocString_View_0__Lean_Doc_asFence(v_tok_375_);
lean_dec(v_tok_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter(lean_object* v_tok_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1));
v___x_386_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__2));
v___x_387_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_385_, v___x_386_, v_tok_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___boxed(lean_object* v_tok_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter(v_tok_388_);
lean_dec(v_tok_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(lean_object* v_tok_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Syntax_getHeadInfo(v_tok_390_);
switch(lean_obj_tag(v___x_391_))
{
case 0:
{
lean_object* v_leading_392_; lean_object* v_trailing_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_427_; 
v_leading_392_ = lean_ctor_get(v___x_391_, 0);
v_trailing_393_ = lean_ctor_get(v___x_391_, 2);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; lean_object* v_unused_429_; 
v_unused_428_ = lean_ctor_get(v___x_391_, 3);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v___x_391_, 1);
lean_dec(v_unused_429_);
v___x_395_ = v___x_391_;
v_isShared_396_ = v_isSharedCheck_427_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_trailing_393_);
lean_inc(v_leading_392_);
lean_dec(v___x_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_427_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
uint8_t v___x_397_; lean_object* v___x_398_; 
v___x_397_ = 0;
v___x_398_ = l_Lean_Syntax_getPos_x3f(v_tok_390_, v___x_397_);
if (lean_obj_tag(v___x_398_) == 1)
{
lean_object* v_val_399_; lean_object* v___x_400_; 
v_val_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_val_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = l_Lean_Syntax_getTailPos_x3f(v_tok_390_, v___x_397_);
if (lean_obj_tag(v___x_400_) == 1)
{
lean_object* v_val_401_; lean_object* v_str_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_422_; 
v_val_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v___x_400_, 1);
v_str_402_ = lean_ctor_get(v_leading_392_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_leading_392_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; lean_object* v_unused_424_; 
v_unused_423_ = lean_ctor_get(v_leading_392_, 2);
lean_dec(v_unused_423_);
v_unused_424_ = lean_ctor_get(v_leading_392_, 1);
lean_dec(v_unused_424_);
v___x_404_ = v_leading_392_;
v_isShared_405_ = v_isSharedCheck_422_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_str_402_);
lean_dec(v_leading_392_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_422_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
lean_inc_n(v_val_399_, 2);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 2, v_val_399_);
lean_ctor_set(v___x_404_, 1, v_val_399_);
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_str_402_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_val_399_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_val_399_);
v___x_407_ = v_reuseFailAlloc_421_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v_str_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_418_; 
v_str_408_ = lean_ctor_get(v_trailing_393_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v_trailing_393_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; lean_object* v_unused_420_; 
v_unused_419_ = lean_ctor_get(v_trailing_393_, 2);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_trailing_393_, 1);
lean_dec(v_unused_420_);
v___x_410_ = v_trailing_393_;
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_str_408_);
lean_dec(v_trailing_393_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
lean_inc_n(v_val_401_, 2);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 2, v_val_401_);
lean_ctor_set(v___x_410_, 1, v_val_401_);
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_str_408_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_val_401_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_val_401_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_415_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 3, v_val_401_);
lean_ctor_set(v___x_395_, 2, v___x_413_);
lean_ctor_set(v___x_395_, 1, v_val_399_);
lean_ctor_set(v___x_395_, 0, v___x_407_);
v___x_415_ = v___x_395_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_val_399_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v_val_401_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
else
{
lean_object* v___x_425_; 
lean_dec(v___x_400_);
lean_dec(v_val_399_);
lean_del_object(v___x_395_);
lean_dec_ref(v_trailing_393_);
lean_dec_ref(v_leading_392_);
v___x_425_ = lean_box(2);
return v___x_425_;
}
}
else
{
lean_object* v___x_426_; 
lean_dec(v___x_398_);
lean_del_object(v___x_395_);
lean_dec_ref(v_trailing_393_);
lean_dec_ref(v_leading_392_);
v___x_426_ = lean_box(2);
return v___x_426_;
}
}
}
case 1:
{
uint8_t v_canonical_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_444_; 
v_canonical_430_ = lean_ctor_get_uint8(v___x_391_, sizeof(void*)*2);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_445_ = lean_ctor_get(v___x_391_, 1);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_446_);
v___x_432_ = v___x_391_;
v_isShared_433_ = v_isSharedCheck_444_;
goto v_resetjp_431_;
}
else
{
lean_dec(v___x_391_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_444_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint8_t v___x_434_; lean_object* v___x_435_; 
v___x_434_ = 0;
v___x_435_ = l_Lean_Syntax_getPos_x3f(v_tok_390_, v___x_434_);
if (lean_obj_tag(v___x_435_) == 1)
{
lean_object* v_val_436_; lean_object* v___x_437_; 
v_val_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = l_Lean_Syntax_getTailPos_x3f(v_tok_390_, v___x_434_);
if (lean_obj_tag(v___x_437_) == 1)
{
lean_object* v_val_438_; lean_object* v___x_440_; 
v_val_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v___x_437_, 1);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v_val_438_);
lean_ctor_set(v___x_432_, 0, v_val_436_);
v___x_440_ = v___x_432_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_val_436_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_val_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_441_, sizeof(void*)*2, v_canonical_430_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
else
{
lean_object* v___x_442_; 
lean_dec(v___x_437_);
lean_dec(v_val_436_);
lean_del_object(v___x_432_);
v___x_442_ = lean_box(2);
return v___x_442_;
}
}
else
{
lean_object* v___x_443_; 
lean_dec(v___x_435_);
lean_del_object(v___x_432_);
v___x_443_ = lean_box(2);
return v___x_443_;
}
}
}
default: 
{
lean_object* v___x_447_; 
lean_dec(v___x_391_);
v___x_447_ = lean_box(2);
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo___boxed(lean_object* v_tok_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(v_tok_448_);
lean_dec(v_tok_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_strLitOfContent(lean_object* v_value_450_, lean_object* v_tok_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(v_tok_451_);
v___x_453_ = l_Lean_Syntax_mkStrLit(v_value_450_, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_strLitOfContent___boxed(lean_object* v_value_454_, lean_object* v_tok_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Doc_strLitOfContent(v_value_454_, v_tok_455_);
lean_dec(v_tok_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(lean_object* v_tok_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Syntax_getHeadInfo(v_tok_457_);
switch(lean_obj_tag(v___x_458_))
{
case 0:
{
lean_object* v_leading_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_480_; 
v_leading_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; lean_object* v_unused_482_; lean_object* v_unused_483_; 
v_unused_481_ = lean_ctor_get(v___x_458_, 3);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v___x_458_, 2);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v___x_458_, 1);
lean_dec(v_unused_483_);
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_480_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_leading_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_480_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; lean_object* v___x_464_; 
v___x_463_ = 0;
v___x_464_ = l_Lean_Syntax_getPos_x3f(v_tok_457_, v___x_463_);
if (lean_obj_tag(v___x_464_) == 1)
{
lean_object* v_val_465_; lean_object* v_str_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_476_; 
v_val_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v___x_464_, 1);
v_str_466_ = lean_ctor_get(v_leading_459_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_leading_459_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_477_ = lean_ctor_get(v_leading_459_, 2);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_leading_459_, 1);
lean_dec(v_unused_478_);
v___x_468_ = v_leading_459_;
v_isShared_469_ = v_isSharedCheck_476_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_str_466_);
lean_dec(v_leading_459_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_476_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
lean_inc_n(v_val_465_, 2);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 2, v_val_465_);
lean_ctor_set(v___x_468_, 1, v_val_465_);
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_str_466_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_val_465_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_val_465_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
lean_inc(v_val_465_);
lean_inc_ref(v___x_471_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 3, v_val_465_);
lean_ctor_set(v___x_461_, 2, v___x_471_);
lean_ctor_set(v___x_461_, 1, v_val_465_);
lean_ctor_set(v___x_461_, 0, v___x_471_);
v___x_473_ = v___x_461_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_val_465_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_val_465_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v___x_479_; 
lean_dec(v___x_464_);
lean_del_object(v___x_461_);
lean_dec_ref(v_leading_459_);
v___x_479_ = lean_box(2);
return v___x_479_;
}
}
}
case 1:
{
uint8_t v_canonical_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_495_; 
v_canonical_484_ = lean_ctor_get_uint8(v___x_458_, sizeof(void*)*2);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_496_ = lean_ctor_get(v___x_458_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v___x_458_, 0);
lean_dec(v_unused_497_);
v___x_486_ = v___x_458_;
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
else
{
lean_dec(v___x_458_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint8_t v___x_488_; lean_object* v___x_489_; 
v___x_488_ = 0;
v___x_489_ = l_Lean_Syntax_getPos_x3f(v_tok_457_, v___x_488_);
if (lean_obj_tag(v___x_489_) == 1)
{
lean_object* v_val_490_; lean_object* v___x_492_; 
v_val_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc_n(v_val_490_, 2);
lean_dec_ref_known(v___x_489_, 1);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v_val_490_);
lean_ctor_set(v___x_486_, 0, v_val_490_);
v___x_492_ = v___x_486_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_val_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_val_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_493_, sizeof(void*)*2, v_canonical_484_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_object* v___x_494_; 
lean_dec(v___x_489_);
lean_del_object(v___x_486_);
v___x_494_ = lean_box(2);
return v___x_494_;
}
}
}
default: 
{
lean_object* v___x_498_; 
lean_dec(v___x_458_);
v___x_498_ = lean_box(2);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo___boxed(lean_object* v_tok_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v_tok_499_);
lean_dec(v_tok_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(lean_object* v___x_502_, lean_object* v_value_503_, lean_object* v_a_504_, lean_object* v_b_505_){
_start:
{
uint8_t v_decide_506_; 
v_decide_506_ = lean_nat_dec_eq(v_a_504_, v___x_502_);
if (v_decide_506_ == 0)
{
uint32_t v___x_507_; lean_object* v___x_508_; uint32_t v___x_509_; uint8_t v___x_510_; 
v___x_507_ = lean_string_utf8_get_fast(v_value_503_, v_a_504_);
v___x_508_ = lean_string_utf8_next_fast(v_value_503_, v_a_504_);
lean_dec(v_a_504_);
v___x_509_ = 92;
v___x_510_ = lean_uint32_dec_eq(v___x_507_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
v___x_511_ = lean_string_push(v_b_505_, v___x_507_);
v_a_504_ = v___x_508_;
v_b_505_ = v___x_511_;
goto _start;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0));
v___x_514_ = lean_string_append(v_b_505_, v___x_513_);
v_a_504_ = v___x_508_;
v_b_505_ = v___x_514_;
goto _start;
}
}
else
{
lean_dec(v_a_504_);
return v_b_505_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___boxed(lean_object* v___x_516_, lean_object* v_value_517_, lean_object* v_a_518_, lean_object* v_b_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_516_, v_value_517_, v_a_518_, v_b_519_);
lean_dec_ref(v_value_517_);
lean_dec(v___x_516_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(lean_object* v_value_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_522_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2));
v___x_523_ = lean_string_utf8_byte_size(v_value_521_);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_523_, v_value_521_, v___x_524_, v___x_522_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText___boxed(lean_object* v_value_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_526_);
lean_dec_ref(v_value_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v_value_530_, lean_object* v_inst_531_, lean_object* v_R_532_, lean_object* v_a_533_, lean_object* v_b_534_, lean_object* v_c_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_529_, v_value_530_, v_a_533_, v_b_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___boxed(lean_object* v___x_537_, lean_object* v___x_538_, lean_object* v_value_539_, lean_object* v_inst_540_, lean_object* v_R_541_, lean_object* v_a_542_, lean_object* v_b_543_, lean_object* v_c_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(v___x_537_, v___x_538_, v_value_539_, v_inst_540_, v_R_541_, v_a_542_, v_b_543_, v_c_544_);
lean_dec_ref(v_value_539_);
lean_dec(v___x_538_);
lean_dec_ref(v___x_537_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom(lean_object* v_src_546_, lean_object* v_value_547_, uint8_t v_canonical_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_549_ = l_Lean_Doc_versoTextKind;
v___x_550_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_547_);
v___x_551_ = l_Lean_SourceInfo_fromRef(v_src_546_, v_canonical_548_);
v___x_552_ = l_Lean_Syntax_mkLit(v___x_549_, v___x_550_, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom___boxed(lean_object* v_src_553_, lean_object* v_value_554_, lean_object* v_canonical_555_){
_start:
{
uint8_t v_canonical_boxed_556_; lean_object* v_res_557_; 
v_canonical_boxed_556_ = lean_unbox(v_canonical_555_);
v_res_557_ = l_Lean_Doc_mkVersoTextFrom(v_src_553_, v_value_554_, v_canonical_boxed_556_);
lean_dec_ref(v_value_554_);
lean_dec(v_src_553_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom(lean_object* v_src_558_, lean_object* v_value_559_, uint8_t v_canonical_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = l_Lean_Doc_versoRefKind;
v___x_562_ = l_Lean_SourceInfo_fromRef(v_src_558_, v_canonical_560_);
v___x_563_ = l_Lean_Syntax_mkLit(v___x_561_, v_value_559_, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom___boxed(lean_object* v_src_564_, lean_object* v_value_565_, lean_object* v_canonical_566_){
_start:
{
uint8_t v_canonical_boxed_567_; lean_object* v_res_568_; 
v_canonical_boxed_567_ = lean_unbox(v_canonical_566_);
v_res_568_ = l_Lean_Doc_mkVersoRefNameFrom(v_src_564_, v_value_565_, v_canonical_boxed_567_);
lean_dec(v_src_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom(lean_object* v_src_569_, lean_object* v_value_570_, uint8_t v_canonical_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_572_ = l_Lean_Doc_versoLinkUrlKind;
v___x_573_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_570_);
v___x_574_ = l_Lean_SourceInfo_fromRef(v_src_569_, v_canonical_571_);
v___x_575_ = l_Lean_Syntax_mkLit(v___x_572_, v___x_573_, v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom___boxed(lean_object* v_src_576_, lean_object* v_value_577_, lean_object* v_canonical_578_){
_start:
{
uint8_t v_canonical_boxed_579_; lean_object* v_res_580_; 
v_canonical_boxed_579_ = lean_unbox(v_canonical_578_);
v_res_580_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_src_576_, v_value_577_, v_canonical_boxed_579_);
lean_dec_ref(v_value_577_);
lean_dec(v_src_576_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom(lean_object* v_src_581_, lean_object* v_value_582_, uint8_t v_canonical_583_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_584_ = l_Lean_Doc_versoImageAltKind;
v___x_585_ = l_Lean_Doc_escapeVersoImageAlt(v_value_582_);
v___x_586_ = l_Lean_SourceInfo_fromRef(v_src_581_, v_canonical_583_);
v___x_587_ = l_Lean_Syntax_mkLit(v___x_584_, v___x_585_, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom___boxed(lean_object* v_src_588_, lean_object* v_value_589_, lean_object* v_canonical_590_){
_start:
{
uint8_t v_canonical_boxed_591_; lean_object* v_res_592_; 
v_canonical_boxed_591_ = lean_unbox(v_canonical_590_);
v_res_592_ = l_Lean_Doc_mkVersoImageAltFrom(v_src_588_, v_value_589_, v_canonical_boxed_591_);
lean_dec_ref(v_value_589_);
lean_dec(v_src_588_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom(lean_object* v_src_593_, lean_object* v_value_594_, uint8_t v_canonical_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = l_Lean_Doc_versoLinkRefUrlKind;
v___x_597_ = l_Lean_SourceInfo_fromRef(v_src_593_, v_canonical_595_);
v___x_598_ = l_Lean_Syntax_mkLit(v___x_596_, v_value_594_, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom___boxed(lean_object* v_src_599_, lean_object* v_value_600_, lean_object* v_canonical_601_){
_start:
{
uint8_t v_canonical_boxed_602_; lean_object* v_res_603_; 
v_canonical_boxed_602_ = lean_unbox(v_canonical_601_);
v_res_603_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_src_599_, v_value_600_, v_canonical_boxed_602_);
lean_dec(v_src_599_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(lean_object* v_info_604_, lean_object* v___x_605_, lean_object* v_value_606_, lean_object* v_a_607_, lean_object* v_b_608_){
_start:
{
uint8_t v_decide_609_; 
v_decide_609_ = lean_nat_dec_eq(v_a_607_, v___x_605_);
if (v_decide_609_ == 0)
{
lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_632_; 
v_fst_610_ = lean_ctor_get(v_b_608_, 0);
v_snd_611_ = lean_ctor_get(v_b_608_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_b_608_);
if (v_isSharedCheck_632_ == 0)
{
v___x_613_ = v_b_608_;
v_isShared_614_ = v_isSharedCheck_632_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snd_611_);
lean_inc(v_fst_610_);
lean_dec(v_b_608_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_632_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint32_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint32_t v___x_618_; uint8_t v___x_619_; 
v___x_615_ = lean_string_utf8_get_fast(v_value_606_, v_a_607_);
v___x_616_ = lean_string_utf8_next_fast(v_value_606_, v_a_607_);
lean_dec(v_a_607_);
v___x_617_ = lean_string_push(v_snd_611_, v___x_615_);
v___x_618_ = 10;
v___x_619_ = lean_uint32_dec_eq(v___x_615_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_621_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_617_);
v___x_621_ = v___x_613_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_fst_610_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v___x_617_);
v___x_621_ = v_reuseFailAlloc_623_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
v_a_607_ = v___x_616_;
v_b_608_ = v___x_621_;
goto _start;
}
}
else
{
lean_object* v_line_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v_line_624_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2));
v___x_625_ = l_Lean_Doc_versoCodeLineKind;
lean_inc(v_info_604_);
v___x_626_ = l_Lean_Syntax_mkLit(v___x_625_, v___x_617_, v_info_604_);
v___x_627_ = lean_array_push(v_fst_610_, v___x_626_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v_line_624_);
lean_ctor_set(v___x_613_, 0, v___x_627_);
v___x_629_ = v___x_613_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_line_624_);
v___x_629_ = v_reuseFailAlloc_631_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
v_a_607_ = v___x_616_;
v_b_608_ = v___x_629_;
goto _start;
}
}
}
}
else
{
lean_dec(v_a_607_);
lean_dec(v_info_604_);
return v_b_608_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg___boxed(lean_object* v_info_633_, lean_object* v___x_634_, lean_object* v_value_635_, lean_object* v_a_636_, lean_object* v_b_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_633_, v___x_634_, v_value_635_, v_a_636_, v_b_637_);
lean_dec_ref(v_value_635_);
lean_dec(v___x_634_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(lean_object* v_info_644_, lean_object* v_value_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__1));
v___x_648_ = lean_string_utf8_byte_size(v_value_645_);
lean_inc(v_info_644_);
v___x_649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_644_, v___x_648_, v_value_645_, v___x_646_, v___x_647_);
v_fst_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_fst_650_);
v_snd_651_ = lean_ctor_get(v___x_649_, 1);
lean_inc(v_snd_651_);
lean_dec_ref(v___x_649_);
v___x_656_ = lean_string_utf8_byte_size(v_snd_651_);
v___x_657_ = lean_nat_dec_eq(v___x_656_, v___x_646_);
if (v___x_657_ == 0)
{
goto v___jp_652_;
}
else
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_array_get_size(v_fst_650_);
v___x_659_ = lean_nat_dec_eq(v___x_658_, v___x_646_);
if (v___x_659_ == 0)
{
lean_dec(v_snd_651_);
lean_dec(v_info_644_);
return v_fst_650_;
}
else
{
goto v___jp_652_;
}
}
v___jp_652_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = l_Lean_Doc_versoCodeLineKind;
v___x_654_ = l_Lean_Syntax_mkLit(v___x_653_, v_snd_651_, v_info_644_);
v___x_655_ = lean_array_push(v_fst_650_, v___x_654_);
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___boxed(lean_object* v_info_660_, lean_object* v_value_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_660_, v_value_661_);
lean_dec_ref(v_value_661_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(lean_object* v_info_663_, lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v_value_666_, lean_object* v_inst_667_, lean_object* v_R_668_, lean_object* v_a_669_, lean_object* v_b_670_, lean_object* v_c_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___redArg(v_info_663_, v___x_665_, v_value_666_, v_a_669_, v_b_670_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0___boxed(lean_object* v_info_673_, lean_object* v___x_674_, lean_object* v___x_675_, lean_object* v_value_676_, lean_object* v_inst_677_, lean_object* v_R_678_, lean_object* v_a_679_, lean_object* v_b_680_, lean_object* v_c_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom_spec__0(v_info_673_, v___x_674_, v___x_675_, v_value_676_, v_inst_677_, v_R_678_, v_a_679_, v_b_680_, v_c_681_);
lean_dec_ref(v_value_676_);
lean_dec(v___x_675_);
lean_dec_ref(v___x_674_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom(lean_object* v_src_686_, lean_object* v_value_687_, uint8_t v_canonical_688_){
_start:
{
lean_object* v_info_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_info_689_ = l_Lean_SourceInfo_fromRef(v_src_686_, v_canonical_688_);
v___x_690_ = l_Lean_Doc_versoCodeKind;
lean_inc(v_info_689_);
v___x_691_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_689_, v_value_687_);
v___x_692_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_693_ = lean_box(2);
v___x_694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___x_692_);
lean_ctor_set(v___x_694_, 2, v___x_691_);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_mk_empty_array_with_capacity(v___x_695_);
v___x_697_ = lean_array_push(v___x_696_, v___x_694_);
v___x_698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_698_, 0, v_info_689_);
lean_ctor_set(v___x_698_, 1, v___x_690_);
lean_ctor_set(v___x_698_, 2, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom___boxed(lean_object* v_src_699_, lean_object* v_value_700_, lean_object* v_canonical_701_){
_start:
{
uint8_t v_canonical_boxed_702_; lean_object* v_res_703_; 
v_canonical_boxed_702_ = lean_unbox(v_canonical_701_);
v_res_703_ = l_Lean_Doc_mkVersoCodeFrom(v_src_699_, v_value_700_, v_canonical_boxed_702_);
lean_dec_ref(v_value_700_);
lean_dec(v_src_699_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom(lean_object* v_src_704_, lean_object* v_value_705_, uint8_t v_canonical_706_){
_start:
{
lean_object* v_info_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_info_707_ = l_Lean_SourceInfo_fromRef(v_src_704_, v_canonical_706_);
v___x_708_ = l_Lean_Doc_versoCodeBlockKind;
lean_inc(v_info_707_);
v___x_709_ = l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom(v_info_707_, v_value_705_);
v___x_710_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_711_ = lean_box(2);
v___x_712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_710_);
lean_ctor_set(v___x_712_, 2, v___x_709_);
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = lean_mk_empty_array_with_capacity(v___x_713_);
v___x_715_ = lean_array_push(v___x_714_, v___x_712_);
v___x_716_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_716_, 0, v_info_707_);
lean_ctor_set(v___x_716_, 1, v___x_708_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___boxed(lean_object* v_src_717_, lean_object* v_value_718_, lean_object* v_canonical_719_){
_start:
{
uint8_t v_canonical_boxed_720_; lean_object* v_res_721_; 
v_canonical_boxed_720_ = lean_unbox(v_canonical_719_);
v_res_721_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_src_717_, v_value_718_, v_canonical_boxed_720_);
lean_dec_ref(v_value_718_);
lean_dec(v_src_717_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom(lean_object* v_src_731_, uint8_t v_canonical_732_){
_start:
{
lean_object* v_info_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_info_733_ = l_Lean_SourceInfo_fromRef(v_src_731_, v_canonical_732_);
v___x_734_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
v___x_735_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__3));
lean_inc(v_info_733_);
v___x_736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_736_, 0, v_info_733_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_mk_empty_array_with_capacity(v___x_737_);
v___x_739_ = lean_array_push(v___x_738_, v___x_736_);
v___x_740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_740_, 0, v_info_733_);
lean_ctor_set(v___x_740_, 1, v___x_734_);
lean_ctor_set(v___x_740_, 2, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom___boxed(lean_object* v_src_741_, lean_object* v_canonical_742_){
_start:
{
uint8_t v_canonical_boxed_743_; lean_object* v_res_744_; 
v_canonical_boxed_743_ = lean_unbox(v_canonical_742_);
v_res_744_ = l_Lean_Doc_mkVersoLinebreakFrom(v_src_741_, v_canonical_boxed_743_);
lean_dec(v_src_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(uint8_t v_canonical_745_, lean_object* v_toPure_746_, lean_object* v_____do__lift_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = l_Lean_Doc_mkVersoLinebreakFrom(v_____do__lift_747_, v_canonical_745_);
v___x_749_ = lean_apply_2(v_toPure_746_, lean_box(0), v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed(lean_object* v_canonical_750_, lean_object* v_toPure_751_, lean_object* v_____do__lift_752_){
_start:
{
uint8_t v_canonical_boxed_753_; lean_object* v_res_754_; 
v_canonical_boxed_753_ = lean_unbox(v_canonical_750_);
v_res_754_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(v_canonical_boxed_753_, v_toPure_751_, v_____do__lift_752_);
lean_dec(v_____do__lift_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg(lean_object* v_inst_755_, lean_object* v_inst_756_, uint8_t v_canonical_757_){
_start:
{
lean_object* v_toApplicative_758_; lean_object* v_toBind_759_; lean_object* v_getRef_760_; lean_object* v_toPure_761_; lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___x_764_; 
v_toApplicative_758_ = lean_ctor_get(v_inst_755_, 0);
lean_inc_ref(v_toApplicative_758_);
v_toBind_759_ = lean_ctor_get(v_inst_755_, 1);
lean_inc(v_toBind_759_);
lean_dec_ref(v_inst_755_);
v_getRef_760_ = lean_ctor_get(v_inst_756_, 0);
lean_inc(v_getRef_760_);
lean_dec_ref(v_inst_756_);
v_toPure_761_ = lean_ctor_get(v_toApplicative_758_, 1);
lean_inc(v_toPure_761_);
lean_dec_ref(v_toApplicative_758_);
v___x_762_ = lean_box(v_canonical_757_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_763_, 0, v___x_762_);
lean_closure_set(v___f_763_, 1, v_toPure_761_);
v___x_764_ = lean_apply_4(v_toBind_759_, lean_box(0), lean_box(0), v_getRef_760_, v___f_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___boxed(lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_canonical_767_){
_start:
{
uint8_t v_canonical_boxed_768_; lean_object* v_res_769_; 
v_canonical_boxed_768_ = lean_unbox(v_canonical_767_);
v_res_769_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_765_, v_inst_766_, v_canonical_boxed_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef(lean_object* v_m_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, uint8_t v_canonical_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_771_, v_inst_772_, v_canonical_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___boxed(lean_object* v_m_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_canonical_778_){
_start:
{
uint8_t v_canonical_boxed_779_; lean_object* v_res_780_; 
v_canonical_boxed_779_ = lean_unbox(v_canonical_778_);
v_res_780_ = l_Lean_Doc_mkVersoLinebreakFromRef(v_m_775_, v_inst_776_, v_inst_777_, v_canonical_boxed_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(lean_object* v_value_781_, uint8_t v_canonical_782_, lean_object* v_toPure_783_, lean_object* v_____do__lift_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = l_Lean_Doc_mkVersoTextFrom(v_____do__lift_784_, v_value_781_, v_canonical_782_);
v___x_786_ = lean_apply_2(v_toPure_783_, lean_box(0), v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed(lean_object* v_value_787_, lean_object* v_canonical_788_, lean_object* v_toPure_789_, lean_object* v_____do__lift_790_){
_start:
{
uint8_t v_canonical_boxed_791_; lean_object* v_res_792_; 
v_canonical_boxed_791_ = lean_unbox(v_canonical_788_);
v_res_792_ = l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(v_value_787_, v_canonical_boxed_791_, v_toPure_789_, v_____do__lift_790_);
lean_dec(v_____do__lift_790_);
lean_dec_ref(v_value_787_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg(lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_value_795_, uint8_t v_canonical_796_){
_start:
{
lean_object* v_toApplicative_797_; lean_object* v_toBind_798_; lean_object* v_getRef_799_; lean_object* v_toPure_800_; lean_object* v___x_801_; lean_object* v___f_802_; lean_object* v___x_803_; 
v_toApplicative_797_ = lean_ctor_get(v_inst_793_, 0);
lean_inc_ref(v_toApplicative_797_);
v_toBind_798_ = lean_ctor_get(v_inst_793_, 1);
lean_inc(v_toBind_798_);
lean_dec_ref(v_inst_793_);
v_getRef_799_ = lean_ctor_get(v_inst_794_, 0);
lean_inc(v_getRef_799_);
lean_dec_ref(v_inst_794_);
v_toPure_800_ = lean_ctor_get(v_toApplicative_797_, 1);
lean_inc(v_toPure_800_);
lean_dec_ref(v_toApplicative_797_);
v___x_801_ = lean_box(v_canonical_796_);
v___f_802_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_802_, 0, v_value_795_);
lean_closure_set(v___f_802_, 1, v___x_801_);
lean_closure_set(v___f_802_, 2, v_toPure_800_);
v___x_803_ = lean_apply_4(v_toBind_798_, lean_box(0), lean_box(0), v_getRef_799_, v___f_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___boxed(lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_value_806_, lean_object* v_canonical_807_){
_start:
{
uint8_t v_canonical_boxed_808_; lean_object* v_res_809_; 
v_canonical_boxed_808_ = lean_unbox(v_canonical_807_);
v_res_809_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_804_, v_inst_805_, v_value_806_, v_canonical_boxed_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef(lean_object* v_m_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_value_813_, uint8_t v_canonical_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_811_, v_inst_812_, v_value_813_, v_canonical_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___boxed(lean_object* v_m_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_value_819_, lean_object* v_canonical_820_){
_start:
{
uint8_t v_canonical_boxed_821_; lean_object* v_res_822_; 
v_canonical_boxed_821_ = lean_unbox(v_canonical_820_);
v_res_822_ = l_Lean_Doc_mkVersoTextFromRef(v_m_816_, v_inst_817_, v_inst_818_, v_value_819_, v_canonical_boxed_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(lean_object* v_value_823_, uint8_t v_canonical_824_, lean_object* v_toPure_825_, lean_object* v_____do__lift_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = l_Lean_Doc_mkVersoRefNameFrom(v_____do__lift_826_, v_value_823_, v_canonical_824_);
v___x_828_ = lean_apply_2(v_toPure_825_, lean_box(0), v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed(lean_object* v_value_829_, lean_object* v_canonical_830_, lean_object* v_toPure_831_, lean_object* v_____do__lift_832_){
_start:
{
uint8_t v_canonical_boxed_833_; lean_object* v_res_834_; 
v_canonical_boxed_833_ = lean_unbox(v_canonical_830_);
v_res_834_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(v_value_829_, v_canonical_boxed_833_, v_toPure_831_, v_____do__lift_832_);
lean_dec(v_____do__lift_832_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg(lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_value_837_, uint8_t v_canonical_838_){
_start:
{
lean_object* v_toApplicative_839_; lean_object* v_toBind_840_; lean_object* v_getRef_841_; lean_object* v_toPure_842_; lean_object* v___x_843_; lean_object* v___f_844_; lean_object* v___x_845_; 
v_toApplicative_839_ = lean_ctor_get(v_inst_835_, 0);
lean_inc_ref(v_toApplicative_839_);
v_toBind_840_ = lean_ctor_get(v_inst_835_, 1);
lean_inc(v_toBind_840_);
lean_dec_ref(v_inst_835_);
v_getRef_841_ = lean_ctor_get(v_inst_836_, 0);
lean_inc(v_getRef_841_);
lean_dec_ref(v_inst_836_);
v_toPure_842_ = lean_ctor_get(v_toApplicative_839_, 1);
lean_inc(v_toPure_842_);
lean_dec_ref(v_toApplicative_839_);
v___x_843_ = lean_box(v_canonical_838_);
v___f_844_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_844_, 0, v_value_837_);
lean_closure_set(v___f_844_, 1, v___x_843_);
lean_closure_set(v___f_844_, 2, v_toPure_842_);
v___x_845_ = lean_apply_4(v_toBind_840_, lean_box(0), lean_box(0), v_getRef_841_, v___f_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___boxed(lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_value_848_, lean_object* v_canonical_849_){
_start:
{
uint8_t v_canonical_boxed_850_; lean_object* v_res_851_; 
v_canonical_boxed_850_ = lean_unbox(v_canonical_849_);
v_res_851_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_846_, v_inst_847_, v_value_848_, v_canonical_boxed_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef(lean_object* v_m_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_value_855_, uint8_t v_canonical_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_853_, v_inst_854_, v_value_855_, v_canonical_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___boxed(lean_object* v_m_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_value_861_, lean_object* v_canonical_862_){
_start:
{
uint8_t v_canonical_boxed_863_; lean_object* v_res_864_; 
v_canonical_boxed_863_ = lean_unbox(v_canonical_862_);
v_res_864_ = l_Lean_Doc_mkVersoRefNameFromRef(v_m_858_, v_inst_859_, v_inst_860_, v_value_861_, v_canonical_boxed_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(lean_object* v_value_865_, uint8_t v_canonical_866_, lean_object* v_toPure_867_, lean_object* v_____do__lift_868_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_____do__lift_868_, v_value_865_, v_canonical_866_);
v___x_870_ = lean_apply_2(v_toPure_867_, lean_box(0), v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_871_, lean_object* v_canonical_872_, lean_object* v_toPure_873_, lean_object* v_____do__lift_874_){
_start:
{
uint8_t v_canonical_boxed_875_; lean_object* v_res_876_; 
v_canonical_boxed_875_ = lean_unbox(v_canonical_872_);
v_res_876_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(v_value_871_, v_canonical_boxed_875_, v_toPure_873_, v_____do__lift_874_);
lean_dec(v_____do__lift_874_);
lean_dec_ref(v_value_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_value_879_, uint8_t v_canonical_880_){
_start:
{
lean_object* v_toApplicative_881_; lean_object* v_toBind_882_; lean_object* v_getRef_883_; lean_object* v_toPure_884_; lean_object* v___x_885_; lean_object* v___f_886_; lean_object* v___x_887_; 
v_toApplicative_881_ = lean_ctor_get(v_inst_877_, 0);
lean_inc_ref(v_toApplicative_881_);
v_toBind_882_ = lean_ctor_get(v_inst_877_, 1);
lean_inc(v_toBind_882_);
lean_dec_ref(v_inst_877_);
v_getRef_883_ = lean_ctor_get(v_inst_878_, 0);
lean_inc(v_getRef_883_);
lean_dec_ref(v_inst_878_);
v_toPure_884_ = lean_ctor_get(v_toApplicative_881_, 1);
lean_inc(v_toPure_884_);
lean_dec_ref(v_toApplicative_881_);
v___x_885_ = lean_box(v_canonical_880_);
v___f_886_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_886_, 0, v_value_879_);
lean_closure_set(v___f_886_, 1, v___x_885_);
lean_closure_set(v___f_886_, 2, v_toPure_884_);
v___x_887_ = lean_apply_4(v_toBind_882_, lean_box(0), lean_box(0), v_getRef_883_, v___f_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___boxed(lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_value_890_, lean_object* v_canonical_891_){
_start:
{
uint8_t v_canonical_boxed_892_; lean_object* v_res_893_; 
v_canonical_boxed_892_ = lean_unbox(v_canonical_891_);
v_res_893_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_888_, v_inst_889_, v_value_890_, v_canonical_boxed_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef(lean_object* v_m_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_value_897_, uint8_t v_canonical_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_895_, v_inst_896_, v_value_897_, v_canonical_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___boxed(lean_object* v_m_900_, lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v_value_903_, lean_object* v_canonical_904_){
_start:
{
uint8_t v_canonical_boxed_905_; lean_object* v_res_906_; 
v_canonical_boxed_905_ = lean_unbox(v_canonical_904_);
v_res_906_ = l_Lean_Doc_mkVersoLinkUrlFromRef(v_m_900_, v_inst_901_, v_inst_902_, v_value_903_, v_canonical_boxed_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(lean_object* v_value_907_, uint8_t v_canonical_908_, lean_object* v_toPure_909_, lean_object* v_____do__lift_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = l_Lean_Doc_mkVersoImageAltFrom(v_____do__lift_910_, v_value_907_, v_canonical_908_);
v___x_912_ = lean_apply_2(v_toPure_909_, lean_box(0), v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed(lean_object* v_value_913_, lean_object* v_canonical_914_, lean_object* v_toPure_915_, lean_object* v_____do__lift_916_){
_start:
{
uint8_t v_canonical_boxed_917_; lean_object* v_res_918_; 
v_canonical_boxed_917_ = lean_unbox(v_canonical_914_);
v_res_918_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(v_value_913_, v_canonical_boxed_917_, v_toPure_915_, v_____do__lift_916_);
lean_dec(v_____do__lift_916_);
lean_dec_ref(v_value_913_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg(lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_value_921_, uint8_t v_canonical_922_){
_start:
{
lean_object* v_toApplicative_923_; lean_object* v_toBind_924_; lean_object* v_getRef_925_; lean_object* v_toPure_926_; lean_object* v___x_927_; lean_object* v___f_928_; lean_object* v___x_929_; 
v_toApplicative_923_ = lean_ctor_get(v_inst_919_, 0);
lean_inc_ref(v_toApplicative_923_);
v_toBind_924_ = lean_ctor_get(v_inst_919_, 1);
lean_inc(v_toBind_924_);
lean_dec_ref(v_inst_919_);
v_getRef_925_ = lean_ctor_get(v_inst_920_, 0);
lean_inc(v_getRef_925_);
lean_dec_ref(v_inst_920_);
v_toPure_926_ = lean_ctor_get(v_toApplicative_923_, 1);
lean_inc(v_toPure_926_);
lean_dec_ref(v_toApplicative_923_);
v___x_927_ = lean_box(v_canonical_922_);
v___f_928_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_928_, 0, v_value_921_);
lean_closure_set(v___f_928_, 1, v___x_927_);
lean_closure_set(v___f_928_, 2, v_toPure_926_);
v___x_929_ = lean_apply_4(v_toBind_924_, lean_box(0), lean_box(0), v_getRef_925_, v___f_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___boxed(lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_value_932_, lean_object* v_canonical_933_){
_start:
{
uint8_t v_canonical_boxed_934_; lean_object* v_res_935_; 
v_canonical_boxed_934_ = lean_unbox(v_canonical_933_);
v_res_935_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_930_, v_inst_931_, v_value_932_, v_canonical_boxed_934_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef(lean_object* v_m_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_value_939_, uint8_t v_canonical_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_937_, v_inst_938_, v_value_939_, v_canonical_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___boxed(lean_object* v_m_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_value_945_, lean_object* v_canonical_946_){
_start:
{
uint8_t v_canonical_boxed_947_; lean_object* v_res_948_; 
v_canonical_boxed_947_ = lean_unbox(v_canonical_946_);
v_res_948_ = l_Lean_Doc_mkVersoImageAltFromRef(v_m_942_, v_inst_943_, v_inst_944_, v_value_945_, v_canonical_boxed_947_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(lean_object* v_value_949_, uint8_t v_canonical_950_, lean_object* v_toPure_951_, lean_object* v_____do__lift_952_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_____do__lift_952_, v_value_949_, v_canonical_950_);
v___x_954_ = lean_apply_2(v_toPure_951_, lean_box(0), v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_955_, lean_object* v_canonical_956_, lean_object* v_toPure_957_, lean_object* v_____do__lift_958_){
_start:
{
uint8_t v_canonical_boxed_959_; lean_object* v_res_960_; 
v_canonical_boxed_959_ = lean_unbox(v_canonical_956_);
v_res_960_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(v_value_955_, v_canonical_boxed_959_, v_toPure_957_, v_____do__lift_958_);
lean_dec(v_____do__lift_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_value_963_, uint8_t v_canonical_964_){
_start:
{
lean_object* v_toApplicative_965_; lean_object* v_toBind_966_; lean_object* v_getRef_967_; lean_object* v_toPure_968_; lean_object* v___x_969_; lean_object* v___f_970_; lean_object* v___x_971_; 
v_toApplicative_965_ = lean_ctor_get(v_inst_961_, 0);
lean_inc_ref(v_toApplicative_965_);
v_toBind_966_ = lean_ctor_get(v_inst_961_, 1);
lean_inc(v_toBind_966_);
lean_dec_ref(v_inst_961_);
v_getRef_967_ = lean_ctor_get(v_inst_962_, 0);
lean_inc(v_getRef_967_);
lean_dec_ref(v_inst_962_);
v_toPure_968_ = lean_ctor_get(v_toApplicative_965_, 1);
lean_inc(v_toPure_968_);
lean_dec_ref(v_toApplicative_965_);
v___x_969_ = lean_box(v_canonical_964_);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_970_, 0, v_value_963_);
lean_closure_set(v___f_970_, 1, v___x_969_);
lean_closure_set(v___f_970_, 2, v_toPure_968_);
v___x_971_ = lean_apply_4(v_toBind_966_, lean_box(0), lean_box(0), v_getRef_967_, v___f_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___boxed(lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_value_974_, lean_object* v_canonical_975_){
_start:
{
uint8_t v_canonical_boxed_976_; lean_object* v_res_977_; 
v_canonical_boxed_976_ = lean_unbox(v_canonical_975_);
v_res_977_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_972_, v_inst_973_, v_value_974_, v_canonical_boxed_976_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef(lean_object* v_m_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_value_981_, uint8_t v_canonical_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_979_, v_inst_980_, v_value_981_, v_canonical_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___boxed(lean_object* v_m_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_value_987_, lean_object* v_canonical_988_){
_start:
{
uint8_t v_canonical_boxed_989_; lean_object* v_res_990_; 
v_canonical_boxed_989_ = lean_unbox(v_canonical_988_);
v_res_990_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef(v_m_984_, v_inst_985_, v_inst_986_, v_value_987_, v_canonical_boxed_989_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(lean_object* v_value_991_, uint8_t v_canonical_992_, lean_object* v_toPure_993_, lean_object* v_____do__lift_994_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = l_Lean_Doc_mkVersoCodeFrom(v_____do__lift_994_, v_value_991_, v_canonical_992_);
v___x_996_ = lean_apply_2(v_toPure_993_, lean_box(0), v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed(lean_object* v_value_997_, lean_object* v_canonical_998_, lean_object* v_toPure_999_, lean_object* v_____do__lift_1000_){
_start:
{
uint8_t v_canonical_boxed_1001_; lean_object* v_res_1002_; 
v_canonical_boxed_1001_ = lean_unbox(v_canonical_998_);
v_res_1002_ = l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(v_value_997_, v_canonical_boxed_1001_, v_toPure_999_, v_____do__lift_1000_);
lean_dec(v_____do__lift_1000_);
lean_dec_ref(v_value_997_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg(lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_value_1005_, uint8_t v_canonical_1006_){
_start:
{
lean_object* v_toApplicative_1007_; lean_object* v_toBind_1008_; lean_object* v_getRef_1009_; lean_object* v_toPure_1010_; lean_object* v___x_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; 
v_toApplicative_1007_ = lean_ctor_get(v_inst_1003_, 0);
lean_inc_ref(v_toApplicative_1007_);
v_toBind_1008_ = lean_ctor_get(v_inst_1003_, 1);
lean_inc(v_toBind_1008_);
lean_dec_ref(v_inst_1003_);
v_getRef_1009_ = lean_ctor_get(v_inst_1004_, 0);
lean_inc(v_getRef_1009_);
lean_dec_ref(v_inst_1004_);
v_toPure_1010_ = lean_ctor_get(v_toApplicative_1007_, 1);
lean_inc(v_toPure_1010_);
lean_dec_ref(v_toApplicative_1007_);
v___x_1011_ = lean_box(v_canonical_1006_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1012_, 0, v_value_1005_);
lean_closure_set(v___f_1012_, 1, v___x_1011_);
lean_closure_set(v___f_1012_, 2, v_toPure_1010_);
v___x_1013_ = lean_apply_4(v_toBind_1008_, lean_box(0), lean_box(0), v_getRef_1009_, v___f_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___boxed(lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_value_1016_, lean_object* v_canonical_1017_){
_start:
{
uint8_t v_canonical_boxed_1018_; lean_object* v_res_1019_; 
v_canonical_boxed_1018_ = lean_unbox(v_canonical_1017_);
v_res_1019_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_1014_, v_inst_1015_, v_value_1016_, v_canonical_boxed_1018_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef(lean_object* v_m_1020_, lean_object* v_inst_1021_, lean_object* v_inst_1022_, lean_object* v_value_1023_, uint8_t v_canonical_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_1021_, v_inst_1022_, v_value_1023_, v_canonical_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___boxed(lean_object* v_m_1026_, lean_object* v_inst_1027_, lean_object* v_inst_1028_, lean_object* v_value_1029_, lean_object* v_canonical_1030_){
_start:
{
uint8_t v_canonical_boxed_1031_; lean_object* v_res_1032_; 
v_canonical_boxed_1031_ = lean_unbox(v_canonical_1030_);
v_res_1032_ = l_Lean_Doc_mkVersoCodeFromRef(v_m_1026_, v_inst_1027_, v_inst_1028_, v_value_1029_, v_canonical_boxed_1031_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(lean_object* v_value_1033_, uint8_t v_canonical_1034_, lean_object* v_toPure_1035_, lean_object* v_____do__lift_1036_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_____do__lift_1036_, v_value_1033_, v_canonical_1034_);
v___x_1038_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed(lean_object* v_value_1039_, lean_object* v_canonical_1040_, lean_object* v_toPure_1041_, lean_object* v_____do__lift_1042_){
_start:
{
uint8_t v_canonical_boxed_1043_; lean_object* v_res_1044_; 
v_canonical_boxed_1043_ = lean_unbox(v_canonical_1040_);
v_res_1044_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(v_value_1039_, v_canonical_boxed_1043_, v_toPure_1041_, v_____do__lift_1042_);
lean_dec(v_____do__lift_1042_);
lean_dec_ref(v_value_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(lean_object* v_inst_1045_, lean_object* v_inst_1046_, lean_object* v_value_1047_, uint8_t v_canonical_1048_){
_start:
{
lean_object* v_toApplicative_1049_; lean_object* v_toBind_1050_; lean_object* v_getRef_1051_; lean_object* v_toPure_1052_; lean_object* v___x_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; 
v_toApplicative_1049_ = lean_ctor_get(v_inst_1045_, 0);
lean_inc_ref(v_toApplicative_1049_);
v_toBind_1050_ = lean_ctor_get(v_inst_1045_, 1);
lean_inc(v_toBind_1050_);
lean_dec_ref(v_inst_1045_);
v_getRef_1051_ = lean_ctor_get(v_inst_1046_, 0);
lean_inc(v_getRef_1051_);
lean_dec_ref(v_inst_1046_);
v_toPure_1052_ = lean_ctor_get(v_toApplicative_1049_, 1);
lean_inc(v_toPure_1052_);
lean_dec_ref(v_toApplicative_1049_);
v___x_1053_ = lean_box(v_canonical_1048_);
v___f_1054_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1054_, 0, v_value_1047_);
lean_closure_set(v___f_1054_, 1, v___x_1053_);
lean_closure_set(v___f_1054_, 2, v_toPure_1052_);
v___x_1055_ = lean_apply_4(v_toBind_1050_, lean_box(0), lean_box(0), v_getRef_1051_, v___f_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___boxed(lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_value_1058_, lean_object* v_canonical_1059_){
_start:
{
uint8_t v_canonical_boxed_1060_; lean_object* v_res_1061_; 
v_canonical_boxed_1060_ = lean_unbox(v_canonical_1059_);
v_res_1061_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_1056_, v_inst_1057_, v_value_1058_, v_canonical_boxed_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef(lean_object* v_m_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_value_1065_, uint8_t v_canonical_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_1063_, v_inst_1064_, v_value_1065_, v_canonical_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___boxed(lean_object* v_m_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_value_1071_, lean_object* v_canonical_1072_){
_start:
{
uint8_t v_canonical_boxed_1073_; lean_object* v_res_1074_; 
v_canonical_boxed_1073_ = lean_unbox(v_canonical_1072_);
v_res_1074_ = l_Lean_Doc_mkVersoCodeBlockFromRef(v_m_1068_, v_inst_1069_, v_inst_1070_, v_value_1071_, v_canonical_boxed_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asAtom(lean_object* v_text_1075_, lean_object* v_tok_1076_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = l_Lean_Syntax_getHeadInfo(v_tok_1076_);
v___x_1078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v_text_1075_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asAtom___boxed(lean_object* v_text_1079_, lean_object* v_tok_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v_text_1079_, v_tok_1080_);
lean_dec(v_tok_1080_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asNode(lean_object* v_kind_1082_, lean_object* v_args_1083_){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_box(2);
v___x_1085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_kind_1082_);
lean_ctor_set(v___x_1085_, 2, v_args_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_argValToParser(lean_object* v_stx_1105_){
_start:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_Doc_argValToParser___closed__2));
lean_inc(v_stx_1105_);
v___x_1107_ = l_Lean_Syntax_isOfKind(v_stx_1105_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_Doc_argValToParser___closed__4));
lean_inc(v_stx_1105_);
v___x_1109_ = l_Lean_Syntax_isOfKind(v_stx_1105_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_Lean_Doc_argValToParser___closed__6));
lean_inc(v_stx_1105_);
v___x_1111_ = l_Lean_Syntax_isOfKind(v_stx_1105_, v___x_1110_);
if (v___x_1111_ == 0)
{
return v_stx_1105_;
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = l_Lean_Syntax_getArg(v_stx_1105_, v___x_1112_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__10));
lean_inc(v___x_1113_);
v___x_1121_ = l_Lean_Syntax_isOfKind(v___x_1113_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_dec(v___x_1113_);
return v_stx_1105_;
}
else
{
lean_dec(v_stx_1105_);
goto v___jp_1114_;
}
}
else
{
lean_dec(v_stx_1105_);
goto v___jp_1114_;
}
v___jp_1114_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1115_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__9));
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_mk_empty_array_with_capacity(v___x_1116_);
v___x_1118_ = lean_array_push(v___x_1117_, v___x_1113_);
v___x_1119_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1115_, v___x_1118_);
return v___x_1119_;
}
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = l_Lean_Syntax_getArg(v_stx_1105_, v___x_1122_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__11));
lean_inc(v___x_1123_);
v___x_1131_ = l_Lean_Syntax_isOfKind(v___x_1123_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_dec(v___x_1123_);
return v_stx_1105_;
}
else
{
lean_dec(v_stx_1105_);
goto v___jp_1124_;
}
}
else
{
lean_dec(v_stx_1105_);
goto v___jp_1124_;
}
v___jp_1124_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1125_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__7));
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_mk_empty_array_with_capacity(v___x_1126_);
v___x_1128_ = lean_array_push(v___x_1127_, v___x_1123_);
v___x_1129_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1125_, v___x_1128_);
return v___x_1129_;
}
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = l_Lean_Syntax_getArg(v_stx_1105_, v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v___x_1133_);
v___x_1135_ = l_Lean_Syntax_isOfKind(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_dec(v___x_1133_);
return v_stx_1105_;
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec(v_stx_1105_);
v___x_1136_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__5));
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_mk_empty_array_with_capacity(v___x_1137_);
v___x_1139_ = lean_array_push(v___x_1138_, v___x_1133_);
v___x_1140_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1136_, v___x_1139_);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_docArgToParser(lean_object* v_stx_1166_){
_start:
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = ((lean_object*)(l_Lean_Doc_docArgToParser___closed__0));
lean_inc(v_stx_1166_);
v___x_1168_ = l_Lean_Syntax_isOfKind(v_stx_1166_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Doc_docArgToParser___closed__1));
lean_inc(v_stx_1166_);
v___x_1170_ = l_Lean_Syntax_isOfKind(v_stx_1166_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = ((lean_object*)(l_Lean_Doc_docArgToParser___closed__2));
lean_inc(v_stx_1166_);
v___x_1172_ = l_Lean_Syntax_isOfKind(v_stx_1166_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = ((lean_object*)(l_Lean_Doc_docArgToParser___closed__3));
lean_inc(v_stx_1166_);
v___x_1174_ = l_Lean_Syntax_isOfKind(v_stx_1166_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_Doc_docArgToParser___closed__4));
lean_inc(v_stx_1166_);
v___x_1176_ = l_Lean_Syntax_isOfKind(v_stx_1166_, v___x_1175_);
if (v___x_1176_ == 0)
{
return v_stx_1166_;
}
else
{
lean_object* v___x_1177_; lean_object* v_tk_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1177_ = lean_unsigned_to_nat(0u);
v_tk_1178_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1177_);
v___x_1179_ = lean_unsigned_to_nat(1u);
v___x_1180_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1179_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v___x_1180_);
v___x_1189_ = l_Lean_Syntax_isOfKind(v___x_1180_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_dec(v___x_1180_);
lean_dec(v_tk_1178_);
return v_stx_1166_;
}
else
{
lean_dec(v_stx_1166_);
goto v___jp_1181_;
}
}
else
{
lean_dec(v_stx_1166_);
goto v___jp_1181_;
}
v___jp_1181_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1182_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__10));
v___x_1183_ = lean_unsigned_to_nat(2u);
v___x_1184_ = lean_mk_empty_array_with_capacity(v___x_1183_);
v___x_1185_ = lean_array_push(v___x_1184_, v_tk_1178_);
v___x_1186_ = lean_array_push(v___x_1185_, v___x_1180_);
v___x_1187_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1182_, v___x_1186_);
return v___x_1187_;
}
}
}
else
{
lean_object* v___x_1190_; lean_object* v_tk_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1190_ = lean_unsigned_to_nat(0u);
v_tk_1191_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1190_);
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1192_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v___x_1193_);
v___x_1202_ = l_Lean_Syntax_isOfKind(v___x_1193_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_dec(v___x_1193_);
lean_dec(v_tk_1191_);
return v_stx_1166_;
}
else
{
lean_dec(v_stx_1166_);
goto v___jp_1194_;
}
}
else
{
lean_dec(v_stx_1166_);
goto v___jp_1194_;
}
v___jp_1194_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1195_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__8));
v___x_1196_ = lean_unsigned_to_nat(2u);
v___x_1197_ = lean_mk_empty_array_with_capacity(v___x_1196_);
v___x_1198_ = lean_array_push(v___x_1197_, v_tk_1191_);
v___x_1199_ = lean_array_push(v___x_1198_, v___x_1193_);
v___x_1200_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1195_, v___x_1199_);
return v___x_1200_;
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1203_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v___x_1204_);
v___x_1219_ = l_Lean_Syntax_isOfKind(v___x_1204_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_dec(v___x_1204_);
return v_stx_1166_;
}
else
{
goto v___jp_1205_;
}
}
else
{
goto v___jp_1205_;
}
v___jp_1205_:
{
lean_object* v___x_1206_; lean_object* v_eq_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
v_eq_1207_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1206_);
v___x_1208_ = lean_unsigned_to_nat(2u);
v___x_1209_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1208_);
lean_dec(v_stx_1166_);
v___x_1210_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__6));
v___x_1211_ = l_Lean_Doc_argValToParser(v___x_1209_);
v___x_1212_ = lean_unsigned_to_nat(3u);
v___x_1213_ = lean_mk_empty_array_with_capacity(v___x_1212_);
v___x_1214_ = lean_array_push(v___x_1213_, v___x_1204_);
v___x_1215_ = lean_array_push(v___x_1214_, v_eq_1207_);
v___x_1216_ = lean_array_push(v___x_1215_, v___x_1211_);
v___x_1217_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1210_, v___x_1216_);
return v___x_1217_;
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v_po_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1220_ = lean_unsigned_to_nat(0u);
v_po_1221_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1220_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1222_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v___x_1223_);
v___x_1242_ = l_Lean_Syntax_isOfKind(v___x_1223_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec(v___x_1223_);
lean_dec(v_po_1221_);
return v_stx_1166_;
}
else
{
goto v___jp_1224_;
}
}
else
{
goto v___jp_1224_;
}
v___jp_1224_:
{
lean_object* v___x_1225_; lean_object* v_eq_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v_pc_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1225_ = lean_unsigned_to_nat(2u);
v_eq_1226_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1225_);
v___x_1227_ = lean_unsigned_to_nat(3u);
v___x_1228_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1227_);
v___x_1229_ = lean_unsigned_to_nat(4u);
v_pc_1230_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1229_);
lean_dec(v_stx_1166_);
v___x_1231_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__4));
v___x_1232_ = l_Lean_Doc_argValToParser(v___x_1228_);
v___x_1233_ = lean_unsigned_to_nat(5u);
v___x_1234_ = lean_mk_empty_array_with_capacity(v___x_1233_);
v___x_1235_ = lean_array_push(v___x_1234_, v_po_1221_);
v___x_1236_ = lean_array_push(v___x_1235_, v___x_1223_);
v___x_1237_ = lean_array_push(v___x_1236_, v_eq_1226_);
v___x_1238_ = lean_array_push(v___x_1237_, v___x_1232_);
v___x_1239_ = lean_array_push(v___x_1238_, v_pc_1230_);
v___x_1240_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1231_, v___x_1239_);
return v___x_1240_;
}
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = l_Lean_Syntax_getArg(v_stx_1166_, v___x_1243_);
lean_dec(v_stx_1166_);
v___x_1245_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__2));
v___x_1246_ = l_Lean_Doc_argValToParser(v___x_1244_);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_mk_empty_array_with_capacity(v___x_1247_);
v___x_1249_ = lean_array_push(v___x_1248_, v___x_1246_);
v___x_1250_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1245_, v___x_1249_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_linkTargetToParser(lean_object* v_stx_1276_){
_start:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__1));
lean_inc(v_stx_1276_);
v___x_1278_ = l_Lean_Syntax_isOfKind(v_stx_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__3));
lean_inc(v_stx_1276_);
v___x_1280_ = l_Lean_Syntax_isOfKind(v_stx_1276_, v___x_1279_);
if (v___x_1280_ == 0)
{
return v_stx_1276_;
}
else
{
lean_object* v___x_1281_; lean_object* v_o_1282_; lean_object* v___x_1283_; lean_object* v_name_1284_; lean_object* v___x_1285_; lean_object* v_c_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1281_ = lean_unsigned_to_nat(0u);
v_o_1282_ = l_Lean_Syntax_getArg(v_stx_1276_, v___x_1281_);
v___x_1283_ = lean_unsigned_to_nat(1u);
v_name_1284_ = l_Lean_Syntax_getArg(v_stx_1276_, v___x_1283_);
v___x_1285_ = lean_unsigned_to_nat(2u);
v_c_1286_ = l_Lean_Syntax_getArg(v_stx_1276_, v___x_1285_);
lean_dec(v_stx_1276_);
v___x_1287_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__5));
v___x_1288_ = l_Lean_TSyntax_getString(v_name_1284_);
v___x_1289_ = l_Lean_Doc_mkVersoRefNameFrom(v_name_1284_, v___x_1288_, v___x_1278_);
lean_dec(v_name_1284_);
v___x_1290_ = lean_unsigned_to_nat(3u);
v___x_1291_ = lean_mk_empty_array_with_capacity(v___x_1290_);
v___x_1292_ = lean_array_push(v___x_1291_, v_o_1282_);
v___x_1293_ = lean_array_push(v___x_1292_, v___x_1289_);
v___x_1294_ = lean_array_push(v___x_1293_, v_c_1286_);
v___x_1295_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1287_, v___x_1294_);
return v___x_1295_;
}
}
else
{
lean_object* v___x_1296_; lean_object* v_o_1297_; lean_object* v___x_1298_; lean_object* v_url_1299_; lean_object* v___x_1300_; lean_object* v_c_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v_o_1297_ = l_Lean_Syntax_getArg(v_stx_1276_, v___x_1296_);
v___x_1298_ = lean_unsigned_to_nat(1u);
v_url_1299_ = l_Lean_Syntax_getArg(v_stx_1276_, v___x_1298_);
v___x_1300_ = lean_unsigned_to_nat(2u);
v_c_1301_ = l_Lean_Syntax_getArg(v_stx_1276_, v___x_1300_);
lean_dec(v_stx_1276_);
v___x_1302_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__6));
v___x_1303_ = l_Lean_TSyntax_getString(v_url_1299_);
v___x_1304_ = 0;
v___x_1305_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_url_1299_, v___x_1303_, v___x_1304_);
lean_dec_ref(v___x_1303_);
lean_dec(v_url_1299_);
v___x_1306_ = lean_unsigned_to_nat(3u);
v___x_1307_ = lean_mk_empty_array_with_capacity(v___x_1306_);
v___x_1308_ = lean_array_push(v___x_1307_, v_o_1297_);
v___x_1309_ = lean_array_push(v___x_1308_, v___x_1305_);
v___x_1310_ = lean_array_push(v___x_1309_, v_c_1301_);
v___x_1311_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1302_, v___x_1310_);
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(lean_object* v_o_1319_, lean_object* v_s_1320_, lean_object* v_c_1321_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1322_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1));
v___x_1323_ = l_Lean_TSyntax_getString(v_s_1320_);
v___x_1324_ = l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter(v___x_1323_, v_o_1319_);
v___x_1325_ = 0;
v___x_1326_ = l_Lean_Doc_mkVersoCodeFrom(v_s_1320_, v___x_1323_, v___x_1325_);
v___x_1327_ = l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter(v___x_1323_, v_c_1321_);
lean_dec_ref(v___x_1323_);
v___x_1328_ = lean_unsigned_to_nat(3u);
v___x_1329_ = lean_mk_empty_array_with_capacity(v___x_1328_);
v___x_1330_ = lean_array_push(v___x_1329_, v___x_1324_);
v___x_1331_ = lean_array_push(v___x_1330_, v___x_1326_);
v___x_1332_ = lean_array_push(v___x_1331_, v___x_1327_);
v___x_1333_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1322_, v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___boxed(lean_object* v_o_1334_, lean_object* v_s_1335_, lean_object* v_c_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(v_o_1334_, v_s_1335_, v_c_1336_);
lean_dec(v_c_1336_);
lean_dec(v_s_1335_);
lean_dec(v_o_1334_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_bs_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1341_ == 0)
{
return v_bs_1340_;
}
else
{
lean_object* v_v_1342_; lean_object* v___x_1343_; lean_object* v_bs_x27_1344_; lean_object* v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v_v_1342_ = lean_array_uget(v_bs_1340_, v_i_1339_);
v___x_1343_ = lean_unsigned_to_nat(0u);
v_bs_x27_1344_ = lean_array_uset(v_bs_1340_, v_i_1339_, v___x_1343_);
v___x_1345_ = l_Lean_Doc_docArgToParser(v_v_1342_);
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_add(v_i_1339_, v___x_1346_);
v___x_1348_ = lean_array_uset(v_bs_x27_1344_, v_i_1339_, v___x_1345_);
v_i_1339_ = v___x_1347_;
v_bs_1340_ = v___x_1348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0___boxed(lean_object* v_sz_1350_, lean_object* v_i_1351_, lean_object* v_bs_1352_){
_start:
{
size_t v_sz_boxed_1353_; size_t v_i_boxed_1354_; lean_object* v_res_1355_; 
v_sz_boxed_1353_ = lean_unbox_usize(v_sz_1350_);
lean_dec(v_sz_1350_);
v_i_boxed_1354_ = lean_unbox_usize(v_i_1351_);
lean_dec(v_i_1351_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(v_sz_boxed_1353_, v_i_boxed_1354_, v_bs_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_inlineToParser(lean_object* v_stx_1508_){
_start:
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__1));
lean_inc(v_stx_1508_);
v___x_1510_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__3));
lean_inc(v_stx_1508_);
v___x_1512_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__5));
lean_inc(v_stx_1508_);
v___x_1514_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__6));
lean_inc(v_stx_1508_);
v___x_1516_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__8));
lean_inc(v_stx_1508_);
v___x_1518_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__10));
lean_inc(v_stx_1508_);
v___x_1520_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__12));
lean_inc(v_stx_1508_);
v___x_1522_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__14));
lean_inc(v_stx_1508_);
v___x_1524_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__16));
lean_inc(v_stx_1508_);
v___x_1526_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__17));
lean_inc(v_stx_1508_);
v___x_1528_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__19));
lean_inc(v_stx_1508_);
v___x_1530_ = l_Lean_Syntax_isOfKind(v_stx_1508_, v___x_1529_);
if (v___x_1530_ == 0)
{
return v_stx_1508_;
}
else
{
lean_object* v___x_1531_; lean_object* v_bo_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_bc_1538_; lean_object* v___x_1539_; lean_object* v_so_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_sc_1544_; lean_object* v_inl_1545_; lean_object* v_args_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; size_t v_sz_1550_; size_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1531_ = lean_unsigned_to_nat(0u);
v_bo_1532_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1531_);
v___x_1533_ = lean_unsigned_to_nat(1u);
v___x_1534_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1533_);
v___x_1535_ = lean_unsigned_to_nat(2u);
v___x_1536_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1535_);
v___x_1537_ = lean_unsigned_to_nat(3u);
v_bc_1538_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1537_);
v___x_1539_ = lean_unsigned_to_nat(4u);
v_so_1540_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1539_);
v___x_1541_ = lean_unsigned_to_nat(5u);
v___x_1542_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1541_);
v___x_1543_ = lean_unsigned_to_nat(6u);
v_sc_1544_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1543_);
lean_dec(v_stx_1508_);
v_inl_1545_ = l_Lean_Syntax_getArgs(v___x_1542_);
lean_dec(v___x_1542_);
v_args_1546_ = l_Lean_Syntax_getArgs(v___x_1536_);
lean_dec(v___x_1536_);
v___x_1547_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__20));
v___x_1548_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__21));
v___x_1549_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1548_, v_bo_1532_);
lean_dec(v_bo_1532_);
v_sz_1550_ = lean_array_size(v_args_1546_);
v___x_1551_ = ((size_t)0ULL);
v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(v_sz_1550_, v___x_1551_, v_args_1546_);
v___x_1553_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_1554_ = lean_box(2);
v___x_1555_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1553_);
lean_ctor_set(v___x_1555_, 2, v___x_1552_);
v___x_1556_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__22));
v___x_1557_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1556_, v_bc_1538_);
lean_dec(v_bc_1538_);
v___x_1558_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__23));
v___x_1559_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1558_, v_so_1540_);
lean_dec(v_so_1540_);
v___x_1560_ = lean_mk_empty_array_with_capacity(v___x_1533_);
lean_inc_ref(v___x_1560_);
v___x_1561_ = lean_array_push(v___x_1560_, v___x_1559_);
v___x_1562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1554_);
lean_ctor_set(v___x_1562_, 1, v___x_1553_);
lean_ctor_set(v___x_1562_, 2, v___x_1561_);
v___x_1563_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(v_inl_1545_);
v___x_1564_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__24));
v___x_1565_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1564_, v_sc_1544_);
lean_dec(v_sc_1544_);
v___x_1566_ = lean_array_push(v___x_1560_, v___x_1565_);
v___x_1567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1554_);
lean_ctor_set(v___x_1567_, 1, v___x_1553_);
lean_ctor_set(v___x_1567_, 2, v___x_1566_);
v___x_1568_ = lean_unsigned_to_nat(7u);
v___x_1569_ = lean_mk_empty_array_with_capacity(v___x_1568_);
v___x_1570_ = lean_array_push(v___x_1569_, v___x_1549_);
v___x_1571_ = lean_array_push(v___x_1570_, v___x_1534_);
v___x_1572_ = lean_array_push(v___x_1571_, v___x_1555_);
v___x_1573_ = lean_array_push(v___x_1572_, v___x_1557_);
v___x_1574_ = lean_array_push(v___x_1573_, v___x_1562_);
v___x_1575_ = lean_array_push(v___x_1574_, v___x_1563_);
v___x_1576_ = lean_array_push(v___x_1575_, v___x_1567_);
v___x_1577_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1547_, v___x_1576_);
return v___x_1577_;
}
}
else
{
lean_object* v___x_1578_; lean_object* v_s_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1578_ = lean_unsigned_to_nat(1u);
v_s_1579_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1578_);
lean_dec(v_stx_1508_);
v___x_1580_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
v___x_1581_ = l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(v_s_1579_);
v___x_1582_ = l_Lean_TSyntax_getString(v_s_1579_);
lean_dec(v_s_1579_);
v___x_1583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = lean_mk_empty_array_with_capacity(v___x_1578_);
v___x_1585_ = lean_array_push(v___x_1584_, v___x_1583_);
v___x_1586_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1580_, v___x_1585_);
return v___x_1586_;
}
}
else
{
lean_object* v___x_1587_; lean_object* v_o_1588_; lean_object* v___x_1589_; lean_object* v_name_1590_; lean_object* v___x_1591_; lean_object* v_c_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1587_ = lean_unsigned_to_nat(0u);
v_o_1588_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1587_);
v___x_1589_ = lean_unsigned_to_nat(1u);
v_name_1590_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1589_);
v___x_1591_ = lean_unsigned_to_nat(2u);
v_c_1592_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1591_);
lean_dec(v_stx_1508_);
v___x_1593_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__25));
v___x_1594_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__26));
v___x_1595_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1594_, v_o_1588_);
lean_dec(v_o_1588_);
v___x_1596_ = l_Lean_TSyntax_getString(v_name_1590_);
v___x_1597_ = l_Lean_Doc_mkVersoRefNameFrom(v_name_1590_, v___x_1596_, v___x_1524_);
lean_dec(v_name_1590_);
v___x_1598_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__24));
v___x_1599_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1598_, v_c_1592_);
lean_dec(v_c_1592_);
v___x_1600_ = lean_unsigned_to_nat(3u);
v___x_1601_ = lean_mk_empty_array_with_capacity(v___x_1600_);
v___x_1602_ = lean_array_push(v___x_1601_, v___x_1595_);
v___x_1603_ = lean_array_push(v___x_1602_, v___x_1597_);
v___x_1604_ = lean_array_push(v___x_1603_, v___x_1599_);
v___x_1605_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1593_, v___x_1604_);
return v___x_1605_;
}
}
else
{
lean_object* v___x_1606_; lean_object* v_o_1607_; lean_object* v___x_1608_; lean_object* v_alt_1609_; lean_object* v___x_1610_; lean_object* v_c_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1606_ = lean_unsigned_to_nat(0u);
v_o_1607_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1606_);
v___x_1608_ = lean_unsigned_to_nat(1u);
v_alt_1609_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1608_);
v___x_1610_ = lean_unsigned_to_nat(2u);
v_c_1611_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1610_);
v___x_1612_ = lean_unsigned_to_nat(3u);
v___x_1613_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1612_);
lean_dec(v_stx_1508_);
v___x_1614_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__27));
v___x_1615_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__28));
v___x_1616_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1615_, v_o_1607_);
lean_dec(v_o_1607_);
v___x_1617_ = l_Lean_TSyntax_getString(v_alt_1609_);
v___x_1618_ = l_Lean_Doc_mkVersoImageAltFrom(v_alt_1609_, v___x_1617_, v___x_1522_);
lean_dec_ref(v___x_1617_);
lean_dec(v_alt_1609_);
v___x_1619_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__24));
v___x_1620_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1619_, v_c_1611_);
lean_dec(v_c_1611_);
v___x_1621_ = l_Lean_Doc_linkTargetToParser(v___x_1613_);
v___x_1622_ = lean_unsigned_to_nat(4u);
v___x_1623_ = lean_mk_empty_array_with_capacity(v___x_1622_);
v___x_1624_ = lean_array_push(v___x_1623_, v___x_1616_);
v___x_1625_ = lean_array_push(v___x_1624_, v___x_1618_);
v___x_1626_ = lean_array_push(v___x_1625_, v___x_1620_);
v___x_1627_ = lean_array_push(v___x_1626_, v___x_1621_);
v___x_1628_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1614_, v___x_1627_);
return v___x_1628_;
}
}
else
{
lean_object* v___x_1629_; lean_object* v_o_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v_c_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_inl_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1629_ = lean_unsigned_to_nat(0u);
v_o_1630_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1629_);
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1631_);
v___x_1633_ = lean_unsigned_to_nat(2u);
v_c_1634_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1633_);
v___x_1635_ = lean_unsigned_to_nat(3u);
v___x_1636_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1635_);
lean_dec(v_stx_1508_);
v_inl_1637_ = l_Lean_Syntax_getArgs(v___x_1632_);
lean_dec(v___x_1632_);
v___x_1638_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__29));
v___x_1639_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__23));
v___x_1640_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1639_, v_o_1630_);
lean_dec(v_o_1630_);
v___x_1641_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(v_inl_1637_);
v___x_1642_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__24));
v___x_1643_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1642_, v_c_1634_);
lean_dec(v_c_1634_);
v___x_1644_ = l_Lean_Doc_linkTargetToParser(v___x_1636_);
v___x_1645_ = lean_unsigned_to_nat(4u);
v___x_1646_ = lean_mk_empty_array_with_capacity(v___x_1645_);
v___x_1647_ = lean_array_push(v___x_1646_, v___x_1640_);
v___x_1648_ = lean_array_push(v___x_1647_, v___x_1641_);
v___x_1649_ = lean_array_push(v___x_1648_, v___x_1643_);
v___x_1650_ = lean_array_push(v___x_1649_, v___x_1644_);
v___x_1651_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1638_, v___x_1650_);
return v___x_1651_;
}
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1652_ = lean_unsigned_to_nat(1u);
v___x_1653_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1652_);
lean_inc(v___x_1653_);
v___x_1654_ = l_Lean_Syntax_isOfKind(v___x_1653_, v___x_1515_);
if (v___x_1654_ == 0)
{
lean_dec(v___x_1653_);
return v_stx_1508_;
}
else
{
lean_object* v___x_1655_; lean_object* v_m_1656_; lean_object* v_o_1657_; lean_object* v_s_1658_; lean_object* v___x_1659_; lean_object* v_c_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1655_ = lean_unsigned_to_nat(0u);
v_m_1656_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1655_);
lean_dec(v_stx_1508_);
v_o_1657_ = l_Lean_Syntax_getArg(v___x_1653_, v___x_1655_);
v_s_1658_ = l_Lean_Syntax_getArg(v___x_1653_, v___x_1652_);
v___x_1659_ = lean_unsigned_to_nat(2u);
v_c_1660_ = l_Lean_Syntax_getArg(v___x_1653_, v___x_1659_);
lean_dec(v___x_1653_);
v___x_1661_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__30));
v___x_1662_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__32));
v___x_1663_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__33));
v___x_1664_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1662_, v___x_1663_, v_m_1656_);
lean_dec(v_m_1656_);
v___x_1665_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(v_o_1657_, v_s_1658_, v_c_1660_);
lean_dec(v_c_1660_);
lean_dec(v_s_1658_);
lean_dec(v_o_1657_);
v___x_1666_ = lean_mk_empty_array_with_capacity(v___x_1659_);
v___x_1667_ = lean_array_push(v___x_1666_, v___x_1664_);
v___x_1668_ = lean_array_push(v___x_1667_, v___x_1665_);
v___x_1669_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1661_, v___x_1668_);
return v___x_1669_;
}
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1670_);
lean_inc(v___x_1671_);
v___x_1672_ = l_Lean_Syntax_isOfKind(v___x_1671_, v___x_1515_);
if (v___x_1672_ == 0)
{
lean_dec(v___x_1671_);
return v_stx_1508_;
}
else
{
lean_object* v___x_1673_; lean_object* v_m_1674_; lean_object* v_o_1675_; lean_object* v_s_1676_; lean_object* v___x_1677_; lean_object* v_c_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1673_ = lean_unsigned_to_nat(0u);
v_m_1674_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1673_);
lean_dec(v_stx_1508_);
v_o_1675_ = l_Lean_Syntax_getArg(v___x_1671_, v___x_1673_);
v_s_1676_ = l_Lean_Syntax_getArg(v___x_1671_, v___x_1670_);
v___x_1677_ = lean_unsigned_to_nat(2u);
v_c_1678_ = l_Lean_Syntax_getArg(v___x_1671_, v___x_1677_);
lean_dec(v___x_1671_);
v___x_1679_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__34));
v___x_1680_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__36));
v___x_1681_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__37));
v___x_1682_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1680_, v___x_1681_, v_m_1674_);
lean_dec(v_m_1674_);
v___x_1683_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(v_o_1675_, v_s_1676_, v_c_1678_);
lean_dec(v_c_1678_);
lean_dec(v_s_1676_);
lean_dec(v_o_1675_);
v___x_1684_ = lean_mk_empty_array_with_capacity(v___x_1677_);
v___x_1685_ = lean_array_push(v___x_1684_, v___x_1682_);
v___x_1686_ = lean_array_push(v___x_1685_, v___x_1683_);
v___x_1687_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1679_, v___x_1686_);
return v___x_1687_;
}
}
}
else
{
lean_object* v___x_1688_; lean_object* v_o_1689_; lean_object* v___x_1690_; lean_object* v_s_1691_; lean_object* v___x_1692_; lean_object* v_c_1693_; lean_object* v___x_1694_; 
v___x_1688_ = lean_unsigned_to_nat(0u);
v_o_1689_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1688_);
v___x_1690_ = lean_unsigned_to_nat(1u);
v_s_1691_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1690_);
v___x_1692_ = lean_unsigned_to_nat(2u);
v_c_1693_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1692_);
lean_dec(v_stx_1508_);
v___x_1694_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(v_o_1689_, v_s_1691_, v_c_1693_);
lean_dec(v_c_1693_);
lean_dec(v_s_1691_);
lean_dec(v_o_1689_);
return v___x_1694_;
}
}
else
{
lean_object* v___x_1695_; lean_object* v_o_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_c_1700_; lean_object* v_inl_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
v_o_1696_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1695_);
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1697_);
v___x_1699_ = lean_unsigned_to_nat(2u);
v_c_1700_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1699_);
lean_dec(v_stx_1508_);
v_inl_1701_ = l_Lean_Syntax_getArgs(v___x_1698_);
lean_dec(v___x_1698_);
v___x_1702_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__38));
v___x_1703_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__40));
v___x_1704_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__41));
v___x_1705_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1703_, v___x_1704_, v_o_1696_);
lean_dec(v_o_1696_);
v___x_1706_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(v_inl_1701_);
v___x_1707_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1703_, v___x_1704_, v_c_1700_);
lean_dec(v_c_1700_);
v___x_1708_ = lean_unsigned_to_nat(3u);
v___x_1709_ = lean_mk_empty_array_with_capacity(v___x_1708_);
v___x_1710_ = lean_array_push(v___x_1709_, v___x_1705_);
v___x_1711_ = lean_array_push(v___x_1710_, v___x_1706_);
v___x_1712_ = lean_array_push(v___x_1711_, v___x_1707_);
v___x_1713_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1702_, v___x_1712_);
return v___x_1713_;
}
}
else
{
lean_object* v___x_1714_; lean_object* v_o_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v_c_1719_; lean_object* v_inl_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1714_ = lean_unsigned_to_nat(0u);
v_o_1715_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1714_);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1716_);
v___x_1718_ = lean_unsigned_to_nat(2u);
v_c_1719_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1718_);
lean_dec(v_stx_1508_);
v_inl_1720_ = l_Lean_Syntax_getArgs(v___x_1717_);
lean_dec(v___x_1717_);
v___x_1721_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__42));
v___x_1722_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__44));
v___x_1723_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__45));
v___x_1724_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1722_, v___x_1723_, v_o_1715_);
lean_dec(v_o_1715_);
v___x_1725_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(v_inl_1720_);
v___x_1726_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1722_, v___x_1723_, v_c_1719_);
lean_dec(v_c_1719_);
v___x_1727_ = lean_unsigned_to_nat(3u);
v___x_1728_ = lean_mk_empty_array_with_capacity(v___x_1727_);
v___x_1729_ = lean_array_push(v___x_1728_, v___x_1724_);
v___x_1730_ = lean_array_push(v___x_1729_, v___x_1725_);
v___x_1731_ = lean_array_push(v___x_1730_, v___x_1726_);
v___x_1732_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1721_, v___x_1731_);
return v___x_1732_;
}
}
else
{
lean_object* v___x_1733_; lean_object* v_s_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1733_ = lean_unsigned_to_nat(0u);
v_s_1734_ = l_Lean_Syntax_getArg(v_stx_1508_, v___x_1733_);
v___x_1735_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__10));
lean_inc(v_s_1734_);
v___x_1736_ = l_Lean_Syntax_isOfKind(v_s_1734_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_dec(v_s_1734_);
return v_stx_1508_;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v_stx_1508_);
v___x_1737_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__46));
v___x_1738_ = l_Lean_TSyntax_getString(v_s_1734_);
v___x_1739_ = 0;
v___x_1740_ = l_Lean_Doc_mkVersoTextFrom(v_s_1734_, v___x_1738_, v___x_1739_);
lean_dec_ref(v___x_1738_);
lean_dec(v_s_1734_);
v___x_1741_ = lean_unsigned_to_nat(1u);
v___x_1742_ = lean_mk_empty_array_with_capacity(v___x_1741_);
v___x_1743_ = lean_array_push(v___x_1742_, v___x_1740_);
v___x_1744_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1737_, v___x_1743_);
return v___x_1744_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(size_t v_sz_1745_, size_t v_i_1746_, lean_object* v_bs_1747_){
_start:
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_usize_dec_lt(v_i_1746_, v_sz_1745_);
if (v___x_1748_ == 0)
{
return v_bs_1747_;
}
else
{
lean_object* v_v_1749_; lean_object* v___x_1750_; lean_object* v_bs_x27_1751_; lean_object* v___x_1752_; size_t v___x_1753_; size_t v___x_1754_; lean_object* v___x_1755_; 
v_v_1749_ = lean_array_uget(v_bs_1747_, v_i_1746_);
v___x_1750_ = lean_unsigned_to_nat(0u);
v_bs_x27_1751_ = lean_array_uset(v_bs_1747_, v_i_1746_, v___x_1750_);
v___x_1752_ = l_Lean_Doc_inlineToParser(v_v_1749_);
v___x_1753_ = ((size_t)1ULL);
v___x_1754_ = lean_usize_add(v_i_1746_, v___x_1753_);
v___x_1755_ = lean_array_uset(v_bs_x27_1751_, v_i_1746_, v___x_1752_);
v_i_1746_ = v___x_1754_;
v_bs_1747_ = v___x_1755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(lean_object* v_inl_1757_){
_start:
{
size_t v_sz_1758_; size_t v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_sz_1758_ = lean_array_size(v_inl_1757_);
v___x_1759_ = ((size_t)0ULL);
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_1758_, v___x_1759_, v_inl_1757_);
v___x_1761_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_1762_ = lean_box(2);
v___x_1763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___x_1761_);
lean_ctor_set(v___x_1763_, 2, v___x_1760_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2___boxed(lean_object* v_sz_1764_, lean_object* v_i_1765_, lean_object* v_bs_1766_){
_start:
{
size_t v_sz_boxed_1767_; size_t v_i_boxed_1768_; lean_object* v_res_1769_; 
v_sz_boxed_1767_ = lean_unbox_usize(v_sz_1764_);
lean_dec(v_sz_1764_);
v_i_boxed_1768_ = lean_unbox_usize(v_i_1765_);
lean_dec(v_i_1765_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_boxed_1767_, v_i_boxed_1768_, v_bs_1766_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_blockToParser_spec__2(lean_object* v_x_1770_, lean_object* v_x_1771_){
_start:
{
lean_object* v_zero_1772_; uint8_t v_isZero_1773_; 
v_zero_1772_ = lean_unsigned_to_nat(0u);
v_isZero_1773_ = lean_nat_dec_eq(v_x_1770_, v_zero_1772_);
if (v_isZero_1773_ == 1)
{
lean_dec(v_x_1770_);
return v_x_1771_;
}
else
{
uint32_t v___x_1774_; lean_object* v_one_1775_; lean_object* v_n_1776_; lean_object* v___x_1777_; 
v___x_1774_ = 35;
v_one_1775_ = lean_unsigned_to_nat(1u);
v_n_1776_ = lean_nat_sub(v_x_1770_, v_one_1775_);
lean_dec(v_x_1770_);
v___x_1777_ = lean_string_push(v_x_1771_, v___x_1774_);
v_x_1770_ = v_n_1776_;
v_x_1771_ = v___x_1777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_descItemToParser(lean_object* v_stx_1931_){
_start:
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = ((lean_object*)(l_Lean_Doc_descItemToParser___closed__1));
lean_inc(v_stx_1931_);
v___x_1933_ = l_Lean_Syntax_isOfKind(v_stx_1931_, v___x_1932_);
if (v___x_1933_ == 0)
{
return v_stx_1931_;
}
else
{
lean_object* v___x_1934_; lean_object* v_marker_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v_desc_1940_; lean_object* v_term_1941_; lean_object* v___x_1942_; size_t v_sz_1943_; size_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; size_t v_sz_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1934_ = lean_unsigned_to_nat(0u);
v_marker_1935_ = l_Lean_Syntax_getArg(v_stx_1931_, v___x_1934_);
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = l_Lean_Syntax_getArg(v_stx_1931_, v___x_1936_);
v___x_1938_ = lean_unsigned_to_nat(3u);
v___x_1939_ = l_Lean_Syntax_getArg(v_stx_1931_, v___x_1938_);
lean_dec(v_stx_1931_);
v_desc_1940_ = l_Lean_Syntax_getArgs(v___x_1939_);
lean_dec(v___x_1939_);
v_term_1941_ = l_Lean_Syntax_getArgs(v___x_1937_);
lean_dec(v___x_1937_);
v___x_1942_ = ((lean_object*)(l_Lean_Doc_descItemToParser___closed__3));
v_sz_1943_ = lean_array_size(v_term_1941_);
v___x_1944_ = ((size_t)0ULL);
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_1943_, v___x_1944_, v_term_1941_);
v___x_1946_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_1947_ = lean_box(2);
v___x_1948_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1946_);
lean_ctor_set(v___x_1948_, 2, v___x_1945_);
v_sz_1949_ = lean_array_size(v_desc_1940_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(v_sz_1949_, v___x_1944_, v_desc_1940_);
v___x_1951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1947_);
lean_ctor_set(v___x_1951_, 1, v___x_1946_);
lean_ctor_set(v___x_1951_, 2, v___x_1950_);
v___x_1952_ = lean_mk_empty_array_with_capacity(v___x_1938_);
v___x_1953_ = lean_array_push(v___x_1952_, v_marker_1935_);
v___x_1954_ = lean_array_push(v___x_1953_, v___x_1948_);
v___x_1955_ = lean_array_push(v___x_1954_, v___x_1951_);
v___x_1956_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1942_, v___x_1955_);
return v___x_1956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3(size_t v_sz_1957_, size_t v_i_1958_, lean_object* v_bs_1959_){
_start:
{
uint8_t v___x_1960_; 
v___x_1960_ = lean_usize_dec_lt(v_i_1958_, v_sz_1957_);
if (v___x_1960_ == 0)
{
return v_bs_1959_;
}
else
{
lean_object* v_v_1961_; lean_object* v___x_1962_; lean_object* v_bs_x27_1963_; lean_object* v___x_1964_; size_t v___x_1965_; size_t v___x_1966_; lean_object* v___x_1967_; 
v_v_1961_ = lean_array_uget(v_bs_1959_, v_i_1958_);
v___x_1962_ = lean_unsigned_to_nat(0u);
v_bs_x27_1963_ = lean_array_uset(v_bs_1959_, v_i_1958_, v___x_1962_);
v___x_1964_ = l_Lean_Doc_descItemToParser(v_v_1961_);
v___x_1965_ = ((size_t)1ULL);
v___x_1966_ = lean_usize_add(v_i_1958_, v___x_1965_);
v___x_1967_ = lean_array_uset(v_bs_x27_1963_, v_i_1958_, v___x_1964_);
v_i_1958_ = v___x_1966_;
v_bs_1959_ = v___x_1967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_listItemToParser(lean_object* v_marker_1989_, lean_object* v_stx_1990_){
_start:
{
lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1991_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__1));
lean_inc(v_stx_1990_);
v___x_1992_ = l_Lean_Syntax_isOfKind(v_stx_1990_, v___x_1991_);
if (v___x_1992_ == 0)
{
lean_dec_ref(v_marker_1989_);
return v_stx_1990_;
}
else
{
lean_object* v___x_1993_; lean_object* v_m_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v_bs_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; size_t v_sz_2001_; size_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_1993_ = lean_unsigned_to_nat(0u);
v_m_1994_ = l_Lean_Syntax_getArg(v_stx_1990_, v___x_1993_);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = l_Lean_Syntax_getArg(v_stx_1990_, v___x_1995_);
lean_dec(v_stx_1990_);
v_bs_1997_ = l_Lean_Syntax_getArgs(v___x_1996_);
lean_dec(v___x_1996_);
v___x_1998_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__4));
v___x_1999_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__6));
v___x_2000_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1999_, v_marker_1989_, v_m_1994_);
lean_dec(v_m_1994_);
v_sz_2001_ = lean_array_size(v_bs_1997_);
v___x_2002_ = ((size_t)0ULL);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(v_sz_2001_, v___x_2002_, v_bs_1997_);
v___x_2004_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2005_ = lean_box(2);
v___x_2006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v___x_2004_);
lean_ctor_set(v___x_2006_, 2, v___x_2003_);
v___x_2007_ = lean_unsigned_to_nat(2u);
v___x_2008_ = lean_mk_empty_array_with_capacity(v___x_2007_);
v___x_2009_ = lean_array_push(v___x_2008_, v___x_2000_);
v___x_2010_ = lean_array_push(v___x_2009_, v___x_2006_);
v___x_2011_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1998_, v___x_2010_);
return v___x_2011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg(lean_object* v_n_2012_, size_t v_sz_2013_, size_t v_i_2014_, lean_object* v_bs_2015_){
_start:
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_usize_dec_lt(v_i_2014_, v_sz_2013_);
if (v___x_2016_ == 0)
{
return v_bs_2015_;
}
else
{
lean_object* v_v_2017_; lean_object* v___x_2018_; lean_object* v_bs_x27_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v_v_2017_ = lean_array_uget(v_bs_2015_, v_i_2014_);
v___x_2018_ = lean_unsigned_to_nat(0u);
v_bs_x27_2019_ = lean_array_uset(v_bs_2015_, v_i_2014_, v___x_2018_);
v___x_2020_ = lean_usize_to_nat(v_i_2014_);
v___x_2021_ = l_Lean_TSyntax_getNat(v_n_2012_);
v___x_2022_ = lean_nat_add(v___x_2021_, v___x_2020_);
lean_dec(v___x_2020_);
lean_dec(v___x_2021_);
v___x_2023_ = l_Nat_reprFast(v___x_2022_);
v___x_2024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___closed__0));
v___x_2025_ = lean_string_append(v___x_2023_, v___x_2024_);
v___x_2026_ = l_Lean_Doc_listItemToParser(v___x_2025_, v_v_2017_);
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_2014_, v___x_2027_);
v___x_2029_ = lean_array_uset(v_bs_x27_2019_, v_i_2014_, v___x_2026_);
v_i_2014_ = v___x_2028_;
v_bs_2015_ = v___x_2029_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5(size_t v_sz_2043_, size_t v_i_2044_, lean_object* v_bs_2045_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_usize_dec_lt(v_i_2044_, v_sz_2043_);
if (v___x_2046_ == 0)
{
return v_bs_2045_;
}
else
{
lean_object* v_v_2047_; lean_object* v___x_2048_; lean_object* v_bs_x27_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; lean_object* v___x_2054_; 
v_v_2047_ = lean_array_uget(v_bs_2045_, v_i_2044_);
v___x_2048_ = lean_unsigned_to_nat(0u);
v_bs_x27_2049_ = lean_array_uset(v_bs_2045_, v_i_2044_, v___x_2048_);
v___x_2050_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__41));
v___x_2051_ = l_Lean_Doc_listItemToParser(v___x_2050_, v_v_2047_);
v___x_2052_ = ((size_t)1ULL);
v___x_2053_ = lean_usize_add(v_i_2044_, v___x_2052_);
v___x_2054_ = lean_array_uset(v_bs_x27_2049_, v_i_2044_, v___x_2051_);
v_i_2044_ = v___x_2053_;
v_bs_2045_ = v___x_2054_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_blockToParser(lean_object* v_stx_2068_){
_start:
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__1));
lean_inc(v_stx_2068_);
v___x_2070_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__3));
lean_inc(v_stx_2068_);
v___x_2072_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__5));
lean_inc(v_stx_2068_);
v___x_2074_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__7));
lean_inc(v_stx_2068_);
v___x_2076_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__9));
lean_inc(v_stx_2068_);
v___x_2078_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__11));
lean_inc(v_stx_2068_);
v___x_2080_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2081_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__13));
lean_inc(v_stx_2068_);
v___x_2082_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__15));
lean_inc(v_stx_2068_);
v___x_2084_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__17));
lean_inc(v_stx_2068_);
v___x_2086_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__19));
lean_inc(v_stx_2068_);
v___x_2088_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__21));
lean_inc(v_stx_2068_);
v___x_2090_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__23));
lean_inc(v_stx_2068_);
v___x_2092_ = l_Lean_Syntax_isOfKind(v_stx_2068_, v___x_2091_);
if (v___x_2092_ == 0)
{
return v_stx_2068_;
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__26));
lean_inc(v___x_2094_);
v___x_2096_ = l_Lean_Syntax_isOfKind(v___x_2094_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_dec(v___x_2094_);
return v_stx_2068_;
}
else
{
lean_object* v___x_2097_; lean_object* v_o_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v_c_2101_; lean_object* v_contents_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2097_ = lean_unsigned_to_nat(0u);
v_o_2098_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2097_);
v___x_2099_ = l_Lean_Syntax_getArg(v___x_2094_, v___x_2097_);
lean_dec(v___x_2094_);
v___x_2100_ = lean_unsigned_to_nat(2u);
v_c_2101_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2100_);
lean_dec(v_stx_2068_);
v_contents_2102_ = l_Lean_Syntax_getArgs(v___x_2099_);
lean_dec(v___x_2099_);
v___x_2103_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__28));
v___x_2104_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_contents_2102_);
lean_dec_ref(v_contents_2102_);
v___x_2105_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2106_ = lean_box(2);
v___x_2107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2105_);
lean_ctor_set(v___x_2107_, 2, v___x_2104_);
v___x_2108_ = lean_mk_empty_array_with_capacity(v___x_2093_);
v___x_2109_ = lean_array_push(v___x_2108_, v___x_2107_);
v___x_2110_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2095_, v___x_2109_);
v___x_2111_ = lean_unsigned_to_nat(3u);
v___x_2112_ = lean_mk_empty_array_with_capacity(v___x_2111_);
v___x_2113_ = lean_array_push(v___x_2112_, v_o_2098_);
v___x_2114_ = lean_array_push(v___x_2113_, v___x_2110_);
v___x_2115_ = lean_array_push(v___x_2114_, v_c_2101_);
v___x_2116_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2103_, v___x_2115_);
return v___x_2116_;
}
}
}
else
{
lean_object* v___x_2117_; lean_object* v_o_2118_; lean_object* v___x_2119_; lean_object* v_name_2120_; lean_object* v___x_2121_; lean_object* v_closer_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v_inls_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; size_t v_sz_2129_; size_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2117_ = lean_unsigned_to_nat(0u);
v_o_2118_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2117_);
v___x_2119_ = lean_unsigned_to_nat(1u);
v_name_2120_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2119_);
v___x_2121_ = lean_unsigned_to_nat(2u);
v_closer_2122_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2121_);
v___x_2123_ = lean_unsigned_to_nat(3u);
v___x_2124_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2123_);
lean_dec(v_stx_2068_);
v_inls_2125_ = l_Lean_Syntax_getArgs(v___x_2124_);
lean_dec(v___x_2124_);
v___x_2126_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__29));
v___x_2127_ = l_Lean_TSyntax_getString(v_name_2120_);
v___x_2128_ = l_Lean_Doc_mkVersoRefNameFrom(v_name_2120_, v___x_2127_, v___x_2088_);
lean_dec(v_name_2120_);
v_sz_2129_ = lean_array_size(v_inls_2125_);
v___x_2130_ = ((size_t)0ULL);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_2129_, v___x_2130_, v_inls_2125_);
v___x_2132_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2133_ = lean_box(2);
v___x_2134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set(v___x_2134_, 1, v___x_2132_);
lean_ctor_set(v___x_2134_, 2, v___x_2131_);
v___x_2135_ = lean_unsigned_to_nat(4u);
v___x_2136_ = lean_mk_empty_array_with_capacity(v___x_2135_);
v___x_2137_ = lean_array_push(v___x_2136_, v_o_2118_);
v___x_2138_ = lean_array_push(v___x_2137_, v___x_2128_);
v___x_2139_ = lean_array_push(v___x_2138_, v_closer_2122_);
v___x_2140_ = lean_array_push(v___x_2139_, v___x_2134_);
v___x_2141_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2126_, v___x_2140_);
return v___x_2141_;
}
}
else
{
lean_object* v___x_2142_; lean_object* v_o_2143_; lean_object* v___x_2144_; lean_object* v_name_2145_; lean_object* v___x_2146_; lean_object* v_closer_2147_; lean_object* v___x_2148_; lean_object* v_url_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2142_ = lean_unsigned_to_nat(0u);
v_o_2143_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2142_);
v___x_2144_ = lean_unsigned_to_nat(1u);
v_name_2145_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2144_);
v___x_2146_ = lean_unsigned_to_nat(2u);
v_closer_2147_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2146_);
v___x_2148_ = lean_unsigned_to_nat(3u);
v_url_2149_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2148_);
lean_dec(v_stx_2068_);
v___x_2150_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__30));
v___x_2151_ = l_Lean_TSyntax_getString(v_name_2145_);
v___x_2152_ = l_Lean_Doc_mkVersoRefNameFrom(v_name_2145_, v___x_2151_, v___x_2086_);
lean_dec(v_name_2145_);
v___x_2153_ = l_Lean_TSyntax_getString(v_url_2149_);
v___x_2154_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_url_2149_, v___x_2153_, v___x_2086_);
lean_dec(v_url_2149_);
v___x_2155_ = lean_unsigned_to_nat(4u);
v___x_2156_ = lean_mk_empty_array_with_capacity(v___x_2155_);
v___x_2157_ = lean_array_push(v___x_2156_, v_o_2143_);
v___x_2158_ = lean_array_push(v___x_2157_, v___x_2152_);
v___x_2159_ = lean_array_push(v___x_2158_, v_closer_2147_);
v___x_2160_ = lean_array_push(v___x_2159_, v___x_2154_);
v___x_2161_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2150_, v___x_2160_);
return v___x_2161_;
}
}
else
{
lean_object* v___x_2162_; lean_object* v_tok_2163_; lean_object* v___x_2164_; lean_object* v_n_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_inls_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; size_t v_sz_2176_; size_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2162_ = lean_unsigned_to_nat(0u);
v_tok_2163_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2162_);
v___x_2164_ = lean_unsigned_to_nat(1u);
v_n_2165_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2164_);
v___x_2166_ = lean_unsigned_to_nat(4u);
v___x_2167_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2166_);
lean_dec(v_stx_2068_);
v_inls_2168_ = l_Lean_Syntax_getArgs(v___x_2167_);
lean_dec(v___x_2167_);
v___x_2169_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__31));
v___x_2170_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__33));
v___x_2171_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2));
v___x_2172_ = l_Lean_TSyntax_getNat(v_n_2165_);
lean_dec(v_n_2165_);
v___x_2173_ = lean_nat_add(v___x_2172_, v___x_2164_);
lean_dec(v___x_2172_);
v___x_2174_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_blockToParser_spec__2(v___x_2173_, v___x_2171_);
v___x_2175_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_2170_, v___x_2174_, v_tok_2163_);
lean_dec(v_tok_2163_);
v_sz_2176_ = lean_array_size(v_inls_2168_);
v___x_2177_ = ((size_t)0ULL);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_2176_, v___x_2177_, v_inls_2168_);
v___x_2179_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2180_ = lean_box(2);
v___x_2181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v___x_2179_);
lean_ctor_set(v___x_2181_, 2, v___x_2178_);
v___x_2182_ = lean_unsigned_to_nat(2u);
v___x_2183_ = lean_mk_empty_array_with_capacity(v___x_2182_);
v___x_2184_ = lean_array_push(v___x_2183_, v___x_2175_);
v___x_2185_ = lean_array_push(v___x_2184_, v___x_2181_);
v___x_2186_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2169_, v___x_2185_);
return v___x_2186_;
}
}
else
{
lean_object* v___x_2187_; lean_object* v_bo_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v_bc_2194_; lean_object* v_args_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; size_t v_sz_2199_; size_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2187_ = lean_unsigned_to_nat(0u);
v_bo_2188_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2187_);
v___x_2189_ = lean_unsigned_to_nat(1u);
v___x_2190_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2189_);
v___x_2191_ = lean_unsigned_to_nat(2u);
v___x_2192_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2191_);
v___x_2193_ = lean_unsigned_to_nat(3u);
v_bc_2194_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2193_);
lean_dec(v_stx_2068_);
v_args_2195_ = l_Lean_Syntax_getArgs(v___x_2192_);
lean_dec(v___x_2192_);
v___x_2196_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__34));
v___x_2197_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__21));
v___x_2198_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_2197_, v_bo_2188_);
lean_dec(v_bo_2188_);
v_sz_2199_ = lean_array_size(v_args_2195_);
v___x_2200_ = ((size_t)0ULL);
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(v_sz_2199_, v___x_2200_, v_args_2195_);
v___x_2202_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2203_ = lean_box(2);
v___x_2204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v___x_2202_);
lean_ctor_set(v___x_2204_, 2, v___x_2201_);
v___x_2205_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__22));
v___x_2206_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_2205_, v_bc_2194_);
lean_dec(v_bc_2194_);
v___x_2207_ = lean_unsigned_to_nat(4u);
v___x_2208_ = lean_mk_empty_array_with_capacity(v___x_2207_);
v___x_2209_ = lean_array_push(v___x_2208_, v___x_2198_);
v___x_2210_ = lean_array_push(v___x_2209_, v___x_2190_);
v___x_2211_ = lean_array_push(v___x_2210_, v___x_2204_);
v___x_2212_ = lean_array_push(v___x_2211_, v___x_2206_);
v___x_2213_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2196_, v___x_2212_);
return v___x_2213_;
}
}
else
{
lean_object* v___x_2214_; lean_object* v_o_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v_c_2223_; lean_object* v_bs_2224_; lean_object* v_args_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; size_t v_sz_2228_; size_t v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2214_ = lean_unsigned_to_nat(0u);
v_o_2215_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2214_);
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2216_);
v___x_2218_ = lean_unsigned_to_nat(2u);
v___x_2219_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2218_);
v___x_2220_ = lean_unsigned_to_nat(4u);
v___x_2221_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2220_);
v___x_2222_ = lean_unsigned_to_nat(5u);
v_c_2223_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2222_);
lean_dec(v_stx_2068_);
v_bs_2224_ = l_Lean_Syntax_getArgs(v___x_2221_);
lean_dec(v___x_2221_);
v_args_2225_ = l_Lean_Syntax_getArgs(v___x_2219_);
lean_dec(v___x_2219_);
v___x_2226_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__35));
v___x_2227_ = l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter(v_o_2215_);
lean_dec(v_o_2215_);
v_sz_2228_ = lean_array_size(v_args_2225_);
v___x_2229_ = ((size_t)0ULL);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(v_sz_2228_, v___x_2229_, v_args_2225_);
v___x_2231_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2232_ = lean_box(2);
v___x_2233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
lean_ctor_set(v___x_2233_, 1, v___x_2231_);
lean_ctor_set(v___x_2233_, 2, v___x_2230_);
v___x_2234_ = l___private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks(v_bs_2224_);
v___x_2235_ = l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter(v_c_2223_);
lean_dec(v_c_2223_);
v___x_2236_ = lean_mk_empty_array_with_capacity(v___x_2222_);
v___x_2237_ = lean_array_push(v___x_2236_, v___x_2227_);
v___x_2238_ = lean_array_push(v___x_2237_, v___x_2217_);
v___x_2239_ = lean_array_push(v___x_2238_, v___x_2233_);
v___x_2240_ = lean_array_push(v___x_2239_, v___x_2234_);
v___x_2241_ = lean_array_push(v___x_2240_, v___x_2235_);
v___x_2242_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2226_, v___x_2241_);
return v___x_2242_;
}
}
else
{
lean_object* v___x_2243_; lean_object* v_o_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v___x_2243_ = lean_unsigned_to_nat(0u);
v_o_2244_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2243_);
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2245_);
lean_inc(v___x_2246_);
v___x_2247_ = l_Lean_Syntax_matchesNull(v___x_2246_, v___x_2243_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2248_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2246_);
v___x_2249_ = l_Lean_Syntax_matchesNull(v___x_2246_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_dec(v___x_2246_);
lean_dec(v_o_2244_);
return v_stx_2068_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v_s_2253_; lean_object* v___x_2254_; lean_object* v_c_2255_; lean_object* v_args_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; size_t v_sz_2259_; size_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2250_ = l_Lean_Syntax_getArg(v___x_2246_, v___x_2243_);
v___x_2251_ = l_Lean_Syntax_getArg(v___x_2246_, v___x_2245_);
lean_dec(v___x_2246_);
v___x_2252_ = lean_unsigned_to_nat(3u);
v_s_2253_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2252_);
v___x_2254_ = lean_unsigned_to_nat(4u);
v_c_2255_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2254_);
lean_dec(v_stx_2068_);
v_args_2256_ = l_Lean_Syntax_getArgs(v___x_2251_);
lean_dec(v___x_2251_);
v___x_2257_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__36));
v___x_2258_ = l___private_Lean_DocString_View_0__Lean_Doc_asFence(v_o_2244_);
lean_dec(v_o_2244_);
v_sz_2259_ = lean_array_size(v_args_2256_);
v___x_2260_ = ((size_t)0ULL);
v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(v_sz_2259_, v___x_2260_, v_args_2256_);
v___x_2262_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2263_ = lean_box(2);
v___x_2264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v___x_2262_);
lean_ctor_set(v___x_2264_, 2, v___x_2261_);
v___x_2265_ = lean_mk_empty_array_with_capacity(v___x_2248_);
v___x_2266_ = lean_array_push(v___x_2265_, v___x_2250_);
v___x_2267_ = lean_array_push(v___x_2266_, v___x_2264_);
v___x_2268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2263_);
lean_ctor_set(v___x_2268_, 1, v___x_2262_);
lean_ctor_set(v___x_2268_, 2, v___x_2267_);
v___x_2269_ = l_Lean_TSyntax_getString(v_s_2253_);
v___x_2270_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_s_2253_, v___x_2269_, v___x_2247_);
lean_dec_ref(v___x_2269_);
lean_dec(v_s_2253_);
v___x_2271_ = l___private_Lean_DocString_View_0__Lean_Doc_asFence(v_c_2255_);
lean_dec(v_c_2255_);
v___x_2272_ = lean_mk_empty_array_with_capacity(v___x_2254_);
v___x_2273_ = lean_array_push(v___x_2272_, v___x_2258_);
v___x_2274_ = lean_array_push(v___x_2273_, v___x_2268_);
v___x_2275_ = lean_array_push(v___x_2274_, v___x_2270_);
v___x_2276_ = lean_array_push(v___x_2275_, v___x_2271_);
v___x_2277_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2257_, v___x_2276_);
return v___x_2277_;
}
}
else
{
lean_object* v___x_2278_; lean_object* v_s_2279_; lean_object* v___x_2280_; lean_object* v_c_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec(v___x_2246_);
v___x_2278_ = lean_unsigned_to_nat(3u);
v_s_2279_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2278_);
v___x_2280_ = lean_unsigned_to_nat(4u);
v_c_2281_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2280_);
lean_dec(v_stx_2068_);
v___x_2282_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__36));
v___x_2283_ = l___private_Lean_DocString_View_0__Lean_Doc_asFence(v_o_2244_);
lean_dec(v_o_2244_);
v___x_2284_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__37));
v___x_2285_ = l_Lean_TSyntax_getString(v_s_2279_);
v___x_2286_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_s_2279_, v___x_2285_, v___x_2078_);
lean_dec_ref(v___x_2285_);
lean_dec(v_s_2279_);
v___x_2287_ = l___private_Lean_DocString_View_0__Lean_Doc_asFence(v_c_2281_);
lean_dec(v_c_2281_);
v___x_2288_ = lean_mk_empty_array_with_capacity(v___x_2280_);
v___x_2289_ = lean_array_push(v___x_2288_, v___x_2283_);
v___x_2290_ = lean_array_push(v___x_2289_, v___x_2284_);
v___x_2291_ = lean_array_push(v___x_2290_, v___x_2286_);
v___x_2292_ = lean_array_push(v___x_2291_, v___x_2287_);
v___x_2293_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2282_, v___x_2292_);
return v___x_2293_;
}
}
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v_items_2296_; lean_object* v___x_2297_; size_t v_sz_2298_; size_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2294_ = lean_unsigned_to_nat(1u);
v___x_2295_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2294_);
lean_dec(v_stx_2068_);
v_items_2296_ = l_Lean_Syntax_getArgs(v___x_2295_);
lean_dec(v___x_2295_);
v___x_2297_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__38));
v_sz_2298_ = lean_array_size(v_items_2296_);
v___x_2299_ = ((size_t)0ULL);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3(v_sz_2298_, v___x_2299_, v_items_2296_);
v___x_2301_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2302_ = lean_box(2);
v___x_2303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v___x_2301_);
lean_ctor_set(v___x_2303_, 2, v___x_2300_);
v___x_2304_ = lean_mk_empty_array_with_capacity(v___x_2294_);
v___x_2305_ = lean_array_push(v___x_2304_, v___x_2303_);
v___x_2306_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2297_, v___x_2305_);
return v___x_2306_;
}
}
else
{
lean_object* v___x_2307_; lean_object* v_n_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_items_2311_; size_t v_sz_2312_; size_t v___x_2313_; lean_object* v_numbered_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2307_ = lean_unsigned_to_nat(1u);
v_n_2308_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2307_);
v___x_2309_ = lean_unsigned_to_nat(4u);
v___x_2310_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2309_);
lean_dec(v_stx_2068_);
v_items_2311_ = l_Lean_Syntax_getArgs(v___x_2310_);
lean_dec(v___x_2310_);
v_sz_2312_ = lean_array_size(v_items_2311_);
v___x_2313_ = ((size_t)0ULL);
v_numbered_2314_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg(v_n_2308_, v_sz_2312_, v___x_2313_, v_items_2311_);
lean_dec(v_n_2308_);
v___x_2315_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__39));
v___x_2316_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2317_ = lean_box(2);
v___x_2318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v___x_2316_);
lean_ctor_set(v___x_2318_, 2, v_numbered_2314_);
v___x_2319_ = lean_mk_empty_array_with_capacity(v___x_2307_);
v___x_2320_ = lean_array_push(v___x_2319_, v___x_2318_);
v___x_2321_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2315_, v___x_2320_);
return v___x_2321_;
}
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_items_2324_; lean_object* v___x_2325_; size_t v_sz_2326_; size_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2322_ = lean_unsigned_to_nat(1u);
v___x_2323_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2322_);
lean_dec(v_stx_2068_);
v_items_2324_ = l_Lean_Syntax_getArgs(v___x_2323_);
lean_dec(v___x_2323_);
v___x_2325_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__40));
v_sz_2326_ = lean_array_size(v_items_2324_);
v___x_2327_ = ((size_t)0ULL);
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5(v_sz_2326_, v___x_2327_, v_items_2324_);
v___x_2329_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2330_ = lean_box(2);
v___x_2331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v___x_2329_);
lean_ctor_set(v___x_2331_, 2, v___x_2328_);
v___x_2332_ = lean_mk_empty_array_with_capacity(v___x_2322_);
v___x_2333_ = lean_array_push(v___x_2332_, v___x_2331_);
v___x_2334_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2325_, v___x_2333_);
return v___x_2334_;
}
}
else
{
lean_object* v___x_2335_; lean_object* v_gt_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v_bs_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2335_ = lean_unsigned_to_nat(0u);
v_gt_2336_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2335_);
v___x_2337_ = lean_unsigned_to_nat(1u);
v___x_2338_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2337_);
lean_dec(v_stx_2068_);
v_bs_2339_ = l_Lean_Syntax_getArgs(v___x_2338_);
lean_dec(v___x_2338_);
v___x_2340_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__41));
v___x_2341_ = l___private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks(v_bs_2339_);
v___x_2342_ = lean_unsigned_to_nat(2u);
v___x_2343_ = lean_mk_empty_array_with_capacity(v___x_2342_);
v___x_2344_ = lean_array_push(v___x_2343_, v_gt_2336_);
v___x_2345_ = lean_array_push(v___x_2344_, v___x_2341_);
v___x_2346_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2340_, v___x_2345_);
return v___x_2346_;
}
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v_inls_2349_; lean_object* v___x_2350_; size_t v_sz_2351_; size_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2347_ = lean_unsigned_to_nat(1u);
v___x_2348_ = l_Lean_Syntax_getArg(v_stx_2068_, v___x_2347_);
lean_dec(v_stx_2068_);
v_inls_2349_ = l_Lean_Syntax_getArgs(v___x_2348_);
lean_dec(v___x_2348_);
v___x_2350_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__42));
v_sz_2351_ = lean_array_size(v_inls_2349_);
v___x_2352_ = ((size_t)0ULL);
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_2351_, v___x_2352_, v_inls_2349_);
v___x_2354_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2355_ = lean_box(2);
v___x_2356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v___x_2354_);
lean_ctor_set(v___x_2356_, 2, v___x_2353_);
v___x_2357_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___x_2358_ = lean_array_push(v___x_2357_, v___x_2356_);
v___x_2359_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2350_, v___x_2358_);
return v___x_2359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(size_t v_sz_2360_, size_t v_i_2361_, lean_object* v_bs_2362_){
_start:
{
uint8_t v___x_2363_; 
v___x_2363_ = lean_usize_dec_lt(v_i_2361_, v_sz_2360_);
if (v___x_2363_ == 0)
{
return v_bs_2362_;
}
else
{
lean_object* v_v_2364_; lean_object* v___x_2365_; lean_object* v_bs_x27_2366_; lean_object* v___x_2367_; size_t v___x_2368_; size_t v___x_2369_; lean_object* v___x_2370_; 
v_v_2364_ = lean_array_uget(v_bs_2362_, v_i_2361_);
v___x_2365_ = lean_unsigned_to_nat(0u);
v_bs_x27_2366_ = lean_array_uset(v_bs_2362_, v_i_2361_, v___x_2365_);
v___x_2367_ = l_Lean_Doc_blockToParser(v_v_2364_);
v___x_2368_ = ((size_t)1ULL);
v___x_2369_ = lean_usize_add(v_i_2361_, v___x_2368_);
v___x_2370_ = lean_array_uset(v_bs_x27_2366_, v_i_2361_, v___x_2367_);
v_i_2361_ = v___x_2369_;
v_bs_2362_ = v___x_2370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks(lean_object* v_bs_2372_){
_start:
{
size_t v_sz_2373_; size_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_sz_2373_ = lean_array_size(v_bs_2372_);
v___x_2374_ = ((size_t)0ULL);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(v_sz_2373_, v___x_2374_, v_bs_2372_);
v___x_2376_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__1));
v___x_2377_ = lean_box(2);
v___x_2378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
lean_ctor_set(v___x_2378_, 1, v___x_2376_);
lean_ctor_set(v___x_2378_, 2, v___x_2375_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3___boxed(lean_object* v_sz_2379_, lean_object* v_i_2380_, lean_object* v_bs_2381_){
_start:
{
size_t v_sz_boxed_2382_; size_t v_i_boxed_2383_; lean_object* v_res_2384_; 
v_sz_boxed_2382_ = lean_unbox_usize(v_sz_2379_);
lean_dec(v_sz_2379_);
v_i_boxed_2383_ = lean_unbox_usize(v_i_2380_);
lean_dec(v_i_2380_);
v_res_2384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3(v_sz_boxed_2382_, v_i_boxed_2383_, v_bs_2381_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0___boxed(lean_object* v_sz_2385_, lean_object* v_i_2386_, lean_object* v_bs_2387_){
_start:
{
size_t v_sz_boxed_2388_; size_t v_i_boxed_2389_; lean_object* v_res_2390_; 
v_sz_boxed_2388_ = lean_unbox_usize(v_sz_2385_);
lean_dec(v_sz_2385_);
v_i_boxed_2389_ = lean_unbox_usize(v_i_2386_);
lean_dec(v_i_2386_);
v_res_2390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(v_sz_boxed_2388_, v_i_boxed_2389_, v_bs_2387_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5___boxed(lean_object* v_sz_2391_, lean_object* v_i_2392_, lean_object* v_bs_2393_){
_start:
{
size_t v_sz_boxed_2394_; size_t v_i_boxed_2395_; lean_object* v_res_2396_; 
v_sz_boxed_2394_ = lean_unbox_usize(v_sz_2391_);
lean_dec(v_sz_2391_);
v_i_boxed_2395_ = lean_unbox_usize(v_i_2392_);
lean_dec(v_i_2392_);
v_res_2396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5(v_sz_boxed_2394_, v_i_boxed_2395_, v_bs_2393_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___boxed(lean_object* v_n_2397_, lean_object* v_sz_2398_, lean_object* v_i_2399_, lean_object* v_bs_2400_){
_start:
{
size_t v_sz_boxed_2401_; size_t v_i_boxed_2402_; lean_object* v_res_2403_; 
v_sz_boxed_2401_ = lean_unbox_usize(v_sz_2398_);
lean_dec(v_sz_2398_);
v_i_boxed_2402_ = lean_unbox_usize(v_i_2399_);
lean_dec(v_i_2399_);
v_res_2403_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg(v_n_2397_, v_sz_boxed_2401_, v_i_boxed_2402_, v_bs_2400_);
lean_dec(v_n_2397_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4(lean_object* v_n_2404_, lean_object* v_as_2405_, size_t v_sz_2406_, size_t v_i_2407_, lean_object* v_bs_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg(v_n_2404_, v_sz_2406_, v_i_2407_, v_bs_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___boxed(lean_object* v_n_2410_, lean_object* v_as_2411_, lean_object* v_sz_2412_, lean_object* v_i_2413_, lean_object* v_bs_2414_){
_start:
{
size_t v_sz_boxed_2415_; size_t v_i_boxed_2416_; lean_object* v_res_2417_; 
v_sz_boxed_2415_ = lean_unbox_usize(v_sz_2412_);
lean_dec(v_sz_2412_);
v_i_boxed_2416_ = lean_unbox_usize(v_i_2413_);
lean_dec(v_i_2413_);
v_res_2417_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4(v_n_2410_, v_as_2411_, v_sz_boxed_2415_, v_i_boxed_2416_, v_bs_2414_);
lean_dec_ref(v_as_2411_);
lean_dec(v_n_2410_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___lam__0(lean_object* v_s_2426_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__41));
v___x_2428_ = l_Lean_Doc_listItemToParser(v___x_2427_, v_s_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0(lean_object* v_x_2435_){
_start:
{
lean_inc(v_x_2435_);
return v_x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___boxed(lean_object* v_x_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0(v_x_2436_);
lean_dec(v_x_2436_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1(lean_object* v___f_2457_, lean_object* v___f_2458_, lean_object* v_xs_2459_){
_start:
{
lean_object* v___x_2460_; size_t v_sz_2461_; size_t v___x_2462_; lean_object* v___x_2463_; size_t v_sz_2464_; lean_object* v___x_2465_; 
v___x_2460_ = ((lean_object*)(l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__9));
v_sz_2461_ = lean_array_size(v_xs_2459_);
v___x_2462_ = ((size_t)0ULL);
v___x_2463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2460_, v___f_2457_, v_sz_2461_, v___x_2462_, v_xs_2459_);
v_sz_2464_ = lean_array_size(v___x_2463_);
v___x_2465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2460_, v___f_2458_, v_sz_2464_, v___x_2462_, v___x_2463_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0(size_t v_sz_2479_, size_t v_i_2480_, lean_object* v_bs_2481_){
_start:
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_usize_dec_lt(v_i_2480_, v_sz_2479_);
if (v___x_2482_ == 0)
{
return v_bs_2481_;
}
else
{
lean_object* v_v_2483_; lean_object* v___x_2484_; lean_object* v_bs_x27_2485_; lean_object* v___x_2486_; size_t v___x_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
v_v_2483_ = lean_array_uget(v_bs_2481_, v_i_2480_);
v___x_2484_ = lean_unsigned_to_nat(0u);
v_bs_x27_2485_ = lean_array_uset(v_bs_2481_, v_i_2480_, v___x_2484_);
v___x_2486_ = l_Lean_Doc_inlineToParser(v_v_2483_);
v___x_2487_ = ((size_t)1ULL);
v___x_2488_ = lean_usize_add(v_i_2480_, v___x_2487_);
v___x_2489_ = lean_array_uset(v_bs_x27_2485_, v_i_2480_, v___x_2486_);
v_i_2480_ = v___x_2488_;
v_bs_2481_ = v___x_2489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0___boxed(lean_object* v_sz_2491_, lean_object* v_i_2492_, lean_object* v_bs_2493_){
_start:
{
size_t v_sz_boxed_2494_; size_t v_i_boxed_2495_; lean_object* v_res_2496_; 
v_sz_boxed_2494_ = lean_unbox_usize(v_sz_2491_);
lean_dec(v_sz_2491_);
v_i_boxed_2495_ = lean_unbox_usize(v_i_2492_);
lean_dec(v_i_2492_);
v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0(v_sz_boxed_2494_, v_i_boxed_2495_, v_bs_2493_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1(size_t v_sz_2497_, size_t v_i_2498_, lean_object* v_bs_2499_){
_start:
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_usize_dec_lt(v_i_2498_, v_sz_2497_);
if (v___x_2500_ == 0)
{
return v_bs_2499_;
}
else
{
lean_object* v_v_2501_; lean_object* v___x_2502_; lean_object* v_bs_x27_2503_; size_t v___x_2504_; size_t v___x_2505_; lean_object* v___x_2506_; 
v_v_2501_ = lean_array_uget(v_bs_2499_, v_i_2498_);
v___x_2502_ = lean_unsigned_to_nat(0u);
v_bs_x27_2503_ = lean_array_uset(v_bs_2499_, v_i_2498_, v___x_2502_);
v___x_2504_ = ((size_t)1ULL);
v___x_2505_ = lean_usize_add(v_i_2498_, v___x_2504_);
v___x_2506_ = lean_array_uset(v_bs_x27_2503_, v_i_2498_, v_v_2501_);
v_i_2498_ = v___x_2505_;
v_bs_2499_ = v___x_2506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1___boxed(lean_object* v_sz_2508_, lean_object* v_i_2509_, lean_object* v_bs_2510_){
_start:
{
size_t v_sz_boxed_2511_; size_t v_i_boxed_2512_; lean_object* v_res_2513_; 
v_sz_boxed_2511_ = lean_unbox_usize(v_sz_2508_);
lean_dec(v_sz_2508_);
v_i_boxed_2512_ = lean_unbox_usize(v_i_2509_);
lean_dec(v_i_2509_);
v_res_2513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1(v_sz_boxed_2511_, v_i_boxed_2512_, v_bs_2510_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_migrateInlines(lean_object* v_xs_2514_){
_start:
{
size_t v_sz_2515_; size_t v___x_2516_; lean_object* v___x_2517_; size_t v_sz_2518_; lean_object* v___x_2519_; 
v_sz_2515_ = lean_array_size(v_xs_2514_);
v___x_2516_ = ((size_t)0ULL);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0(v_sz_2515_, v___x_2516_, v_xs_2514_);
v_sz_2518_ = lean_array_size(v___x_2517_);
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1(v_sz_2518_, v___x_2516_, v___x_2517_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0(size_t v_sz_2520_, size_t v_i_2521_, lean_object* v_bs_2522_){
_start:
{
uint8_t v___x_2523_; 
v___x_2523_ = lean_usize_dec_lt(v_i_2521_, v_sz_2520_);
if (v___x_2523_ == 0)
{
return v_bs_2522_;
}
else
{
lean_object* v_v_2524_; lean_object* v___x_2525_; lean_object* v_bs_x27_2526_; lean_object* v___x_2527_; size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v_v_2524_ = lean_array_uget(v_bs_2522_, v_i_2521_);
v___x_2525_ = lean_unsigned_to_nat(0u);
v_bs_x27_2526_ = lean_array_uset(v_bs_2522_, v_i_2521_, v___x_2525_);
v___x_2527_ = l_Lean_Doc_blockToParser(v_v_2524_);
v___x_2528_ = ((size_t)1ULL);
v___x_2529_ = lean_usize_add(v_i_2521_, v___x_2528_);
v___x_2530_ = lean_array_uset(v_bs_x27_2526_, v_i_2521_, v___x_2527_);
v_i_2521_ = v___x_2529_;
v_bs_2522_ = v___x_2530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0___boxed(lean_object* v_sz_2532_, lean_object* v_i_2533_, lean_object* v_bs_2534_){
_start:
{
size_t v_sz_boxed_2535_; size_t v_i_boxed_2536_; lean_object* v_res_2537_; 
v_sz_boxed_2535_ = lean_unbox_usize(v_sz_2532_);
lean_dec(v_sz_2532_);
v_i_boxed_2536_ = lean_unbox_usize(v_i_2533_);
lean_dec(v_i_2533_);
v_res_2537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0(v_sz_boxed_2535_, v_i_boxed_2536_, v_bs_2534_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_migrateBlocks(lean_object* v_xs_2538_){
_start:
{
size_t v_sz_2539_; size_t v___x_2540_; lean_object* v___x_2541_; size_t v_sz_2542_; lean_object* v___x_2543_; 
v_sz_2539_ = lean_array_size(v_xs_2538_);
v___x_2540_ = ((size_t)0ULL);
v___x_2541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0(v_sz_2539_, v___x_2540_, v_xs_2538_);
v_sz_2542_ = lean_array_size(v___x_2541_);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1(v_sz_2542_, v___x_2540_, v___x_2541_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit(lean_object* v_s_2544_){
_start:
{
lean_object* v___x_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = l_Lean_TSyntax_getString(v_s_2544_);
v___x_2546_ = 0;
v___x_2547_ = l_Lean_Doc_mkVersoCodeFrom(v_s_2544_, v___x_2545_, v___x_2546_);
lean_dec_ref(v___x_2545_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit___boxed(lean_object* v_s_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_Doc_versoCodeOfStrLit(v_s_2548_);
lean_dec(v_s_2548_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit(lean_object* v_s_2550_){
_start:
{
lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = l_Lean_TSyntax_getString(v_s_2550_);
v___x_2552_ = 0;
v___x_2553_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_s_2550_, v___x_2551_, v___x_2552_);
lean_dec_ref(v___x_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit___boxed(lean_object* v_s_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Doc_versoCodeBlockOfStrLit(v_s_2554_);
lean_dec(v_s_2554_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_of(lean_object* v_stx_2568_){
_start:
{
lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2569_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__6));
lean_inc(v_stx_2568_);
v___x_2570_ = l_Lean_Syntax_isOfKind(v_stx_2568_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__5));
lean_inc(v_stx_2568_);
v___x_2572_ = l_Lean_Syntax_isOfKind(v_stx_2568_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
lean_dec(v_stx_2568_);
v___x_2573_ = lean_box(0);
return v___x_2573_;
}
else
{
lean_object* v___x_2574_; lean_object* v_o_2575_; lean_object* v___x_2576_; lean_object* v_name_2577_; 
v___x_2574_ = lean_unsigned_to_nat(0u);
v_o_2575_ = l_Lean_Syntax_getArg(v_stx_2568_, v___x_2574_);
v___x_2576_ = lean_unsigned_to_nat(1u);
v_name_2577_ = l_Lean_Syntax_getArg(v_stx_2568_, v___x_2576_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2583_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__1));
lean_inc(v_name_2577_);
v___x_2584_ = l_Lean_Syntax_isOfKind(v_name_2577_, v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
lean_dec(v_name_2577_);
lean_dec(v_o_2575_);
lean_dec(v_stx_2568_);
v___x_2585_ = lean_box(0);
return v___x_2585_;
}
else
{
goto v___jp_2578_;
}
}
else
{
goto v___jp_2578_;
}
v___jp_2578_:
{
lean_object* v___x_2579_; lean_object* v_c_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2579_ = lean_unsigned_to_nat(2u);
v_c_2580_ = l_Lean_Syntax_getArg(v_stx_2568_, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2581_, 0, v_stx_2568_);
lean_ctor_set(v___x_2581_, 1, v_o_2575_);
lean_ctor_set(v___x_2581_, 2, v_name_2577_);
lean_ctor_set(v___x_2581_, 3, v_c_2580_);
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
return v___x_2582_;
}
}
}
else
{
lean_object* v___x_2586_; lean_object* v_url_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2586_ = lean_unsigned_to_nat(1u);
v_url_2587_ = l_Lean_Syntax_getArg(v_stx_2568_, v___x_2586_);
v___x_2588_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__3));
lean_inc(v_url_2587_);
v___x_2589_ = l_Lean_Syntax_isOfKind(v_url_2587_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; 
lean_dec(v_url_2587_);
lean_dec(v_stx_2568_);
v___x_2590_ = lean_box(0);
return v___x_2590_;
}
else
{
lean_object* v___x_2591_; lean_object* v_o_2592_; lean_object* v___x_2593_; lean_object* v_c_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2591_ = lean_unsigned_to_nat(0u);
v_o_2592_ = l_Lean_Syntax_getArg(v_stx_2568_, v___x_2591_);
v___x_2593_ = lean_unsigned_to_nat(2u);
v_c_2594_ = l_Lean_Syntax_getArg(v_stx_2568_, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2595_, 0, v_stx_2568_);
lean_ctor_set(v___x_2595_, 1, v_o_2592_);
lean_ctor_set(v___x_2595_, 2, v_url_2587_);
lean_ctor_set(v___x_2595_, 3, v_c_2594_);
v___x_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText(lean_object* v_v_2601_){
_start:
{
lean_object* v_content_2602_; lean_object* v___x_2603_; 
v_content_2602_ = lean_ctor_get(v_v_2601_, 1);
v___x_2603_ = l_Lean_TSyntax_getVersoText(v_content_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText___boxed(lean_object* v_v_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_Doc_TextView_getVersoText(v_v_2604_);
lean_dec_ref(v_v_2604_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object* v_v_2606_){
_start:
{
lean_object* v_content_2607_; lean_object* v___x_2608_; 
v_content_2607_ = lean_ctor_get(v_v_2606_, 1);
v___x_2608_ = l_Lean_TSyntax_getVersoTextSource(v_content_2607_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource___boxed(lean_object* v_v_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_Doc_TextView_getVersoTextSource(v_v_2609_);
lean_dec_ref(v_v_2609_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_of(lean_object* v_stx_2617_){
_start:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__46));
lean_inc(v_stx_2617_);
v___x_2619_ = l_Lean_Syntax_isOfKind(v_stx_2617_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; 
lean_dec(v_stx_2617_);
v___x_2620_ = lean_box(0);
return v___x_2620_;
}
else
{
lean_object* v___x_2621_; lean_object* v_s_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2621_ = lean_unsigned_to_nat(0u);
v_s_2622_ = l_Lean_Syntax_getArg(v_stx_2617_, v___x_2621_);
v___x_2623_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__1));
lean_inc(v_s_2622_);
v___x_2624_ = l_Lean_Syntax_isOfKind(v_s_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; 
lean_dec(v_s_2622_);
lean_dec(v_stx_2617_);
v___x_2625_ = lean_box(0);
return v___x_2625_;
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v_stx_2617_);
lean_ctor_set(v___x_2626_, 1, v_s_2622_);
v___x_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
return v___x_2627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_EmphView_of(lean_object* v_stx_2628_){
_start:
{
lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__42));
lean_inc(v_stx_2628_);
v___x_2630_ = l_Lean_Syntax_isOfKind(v_stx_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
lean_dec(v_stx_2628_);
v___x_2631_ = lean_box(0);
return v___x_2631_;
}
else
{
lean_object* v___x_2632_; lean_object* v_o_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2632_ = lean_unsigned_to_nat(0u);
v_o_2633_ = l_Lean_Syntax_getArg(v_stx_2628_, v___x_2632_);
v___x_2634_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__44));
lean_inc(v_o_2633_);
v___x_2635_ = l_Lean_Syntax_isOfKind(v_o_2633_, v___x_2634_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; 
lean_dec(v_o_2633_);
lean_dec(v_stx_2628_);
v___x_2636_ = lean_box(0);
return v___x_2636_;
}
else
{
lean_object* v___x_2637_; lean_object* v_c_2638_; uint8_t v___x_2639_; 
v___x_2637_ = lean_unsigned_to_nat(2u);
v_c_2638_ = l_Lean_Syntax_getArg(v_stx_2628_, v___x_2637_);
lean_inc(v_c_2638_);
v___x_2639_ = l_Lean_Syntax_isOfKind(v_c_2638_, v___x_2634_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; 
lean_dec(v_c_2638_);
lean_dec(v_o_2633_);
lean_dec(v_stx_2628_);
v___x_2640_ = lean_box(0);
return v___x_2640_;
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v_inl_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2641_ = lean_unsigned_to_nat(1u);
v___x_2642_ = l_Lean_Syntax_getArg(v_stx_2628_, v___x_2641_);
v_inl_2643_ = l_Lean_Syntax_getArgs(v___x_2642_);
lean_dec(v___x_2642_);
v___x_2644_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2644_, 0, v_stx_2628_);
lean_ctor_set(v___x_2644_, 1, v_o_2633_);
lean_ctor_set(v___x_2644_, 2, v_inl_2643_);
lean_ctor_set(v___x_2644_, 3, v_c_2638_);
v___x_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
return v___x_2645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BoldView_of(lean_object* v_stx_2646_){
_start:
{
lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2647_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__38));
lean_inc(v_stx_2646_);
v___x_2648_ = l_Lean_Syntax_isOfKind(v_stx_2646_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; 
lean_dec(v_stx_2646_);
v___x_2649_ = lean_box(0);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; lean_object* v_o_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2650_ = lean_unsigned_to_nat(0u);
v_o_2651_ = l_Lean_Syntax_getArg(v_stx_2646_, v___x_2650_);
v___x_2652_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__40));
lean_inc(v_o_2651_);
v___x_2653_ = l_Lean_Syntax_isOfKind(v_o_2651_, v___x_2652_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; 
lean_dec(v_o_2651_);
lean_dec(v_stx_2646_);
v___x_2654_ = lean_box(0);
return v___x_2654_;
}
else
{
lean_object* v___x_2655_; lean_object* v_c_2656_; uint8_t v___x_2657_; 
v___x_2655_ = lean_unsigned_to_nat(2u);
v_c_2656_ = l_Lean_Syntax_getArg(v_stx_2646_, v___x_2655_);
lean_inc(v_c_2656_);
v___x_2657_ = l_Lean_Syntax_isOfKind(v_c_2656_, v___x_2652_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; 
lean_dec(v_c_2656_);
lean_dec(v_o_2651_);
lean_dec(v_stx_2646_);
v___x_2658_ = lean_box(0);
return v___x_2658_;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v_inl_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2659_ = lean_unsigned_to_nat(1u);
v___x_2660_ = l_Lean_Syntax_getArg(v_stx_2646_, v___x_2659_);
v_inl_2661_ = l_Lean_Syntax_getArgs(v___x_2660_);
lean_dec(v___x_2660_);
v___x_2662_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2662_, 0, v_stx_2646_);
lean_ctor_set(v___x_2662_, 1, v_o_2651_);
lean_ctor_set(v___x_2662_, 2, v_inl_2661_);
lean_ctor_set(v___x_2662_, 3, v_c_2656_);
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
return v___x_2663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object* v_v_2664_){
_start:
{
lean_object* v_content_2665_; lean_object* v___x_2666_; 
v_content_2665_ = lean_ctor_get(v_v_2664_, 2);
v___x_2666_ = l_Lean_TSyntax_getVersoCode(v_content_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode___boxed(lean_object* v_v_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_Doc_CodeView_getVersoCode(v_v_2667_);
lean_dec_ref(v_v_2667_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_of(lean_object* v_stx_2675_){
_start:
{
lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1));
lean_inc(v_stx_2675_);
v___x_2677_ = l_Lean_Syntax_isOfKind(v_stx_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; 
lean_dec(v_stx_2675_);
v___x_2678_ = lean_box(0);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; lean_object* v_o_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2679_ = lean_unsigned_to_nat(0u);
v_o_2680_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2679_);
v___x_2681_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1));
lean_inc(v_o_2680_);
v___x_2682_ = l_Lean_Syntax_isOfKind(v_o_2680_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
lean_dec(v_o_2680_);
lean_dec(v_stx_2675_);
v___x_2683_ = lean_box(0);
return v___x_2683_;
}
else
{
lean_object* v___x_2684_; lean_object* v_s_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2684_ = lean_unsigned_to_nat(1u);
v_s_2685_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2684_);
v___x_2686_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v_s_2685_);
v___x_2687_ = l_Lean_Syntax_isOfKind(v_s_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_dec(v_s_2685_);
lean_dec(v_o_2680_);
lean_dec(v_stx_2675_);
v___x_2688_ = lean_box(0);
return v___x_2688_;
}
else
{
lean_object* v___x_2689_; lean_object* v_c_2690_; uint8_t v___x_2691_; 
v___x_2689_ = lean_unsigned_to_nat(2u);
v_c_2690_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2689_);
lean_inc(v_c_2690_);
v___x_2691_ = l_Lean_Syntax_isOfKind(v_c_2690_, v___x_2681_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; 
lean_dec(v_c_2690_);
lean_dec(v_s_2685_);
lean_dec(v_o_2680_);
lean_dec(v_stx_2675_);
v___x_2692_ = lean_box(0);
return v___x_2692_;
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2693_, 0, v_stx_2675_);
lean_ctor_set(v___x_2693_, 1, v_o_2680_);
lean_ctor_set(v___x_2693_, 2, v_s_2685_);
lean_ctor_set(v___x_2693_, 3, v_c_2690_);
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
return v___x_2694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object* v_v_2695_){
_start:
{
lean_object* v_code_2696_; lean_object* v___x_2697_; 
v_code_2696_ = lean_ctor_get(v_v_2695_, 2);
v___x_2697_ = l_Lean_Doc_CodeView_getVersoCode(v_code_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode___boxed(lean_object* v_v_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Doc_MathView_getVersoCode(v_v_2698_);
lean_dec_ref(v_v_2698_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_of(lean_object* v_stx_2700_){
_start:
{
lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2701_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__34));
lean_inc(v_stx_2700_);
v___x_2702_ = l_Lean_Syntax_isOfKind(v_stx_2700_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__30));
lean_inc(v_stx_2700_);
v___x_2704_ = l_Lean_Syntax_isOfKind(v_stx_2700_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; 
lean_dec(v_stx_2700_);
v___x_2705_ = lean_box(0);
return v___x_2705_;
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___y_2709_; 
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = l_Lean_Syntax_getArg(v_stx_2700_, v___x_2706_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__32));
lean_inc(v___x_2707_);
v___x_2729_ = l_Lean_Syntax_isOfKind(v___x_2707_, v___x_2728_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; 
lean_dec(v___x_2707_);
lean_dec(v_stx_2700_);
v___x_2730_ = lean_box(0);
return v___x_2730_;
}
else
{
goto v___jp_2722_;
}
}
else
{
goto v___jp_2722_;
}
v___jp_2708_:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_Doc_CodeView_of(v___y_2709_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v___x_2711_; 
lean_dec(v___x_2707_);
lean_dec(v_stx_2700_);
v___x_2711_ = lean_box(0);
return v___x_2711_;
}
else
{
lean_object* v_val_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2721_; 
v_val_2712_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2714_ = v___x_2710_;
v_isShared_2715_ = v_isSharedCheck_2721_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_val_2712_);
lean_dec(v___x_2710_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2721_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2716_ = 1;
v___x_2717_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2717_, 0, v_stx_2700_);
lean_ctor_set(v___x_2717_, 1, v___x_2707_);
lean_ctor_set(v___x_2717_, 2, v_val_2712_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*3, v___x_2716_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2717_);
v___x_2719_ = v___x_2714_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
v___jp_2722_:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_unsigned_to_nat(1u);
v___x_2724_ = l_Lean_Syntax_getArg(v_stx_2700_, v___x_2723_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1));
lean_inc(v___x_2724_);
v___x_2726_ = l_Lean_Syntax_isOfKind(v___x_2724_, v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; 
lean_dec(v___x_2724_);
lean_dec(v___x_2707_);
lean_dec(v_stx_2700_);
v___x_2727_ = lean_box(0);
return v___x_2727_;
}
else
{
v___y_2709_ = v___x_2724_;
goto v___jp_2708_;
}
}
else
{
v___y_2709_ = v___x_2724_;
goto v___jp_2708_;
}
}
}
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = l_Lean_Syntax_getArg(v_stx_2700_, v___x_2731_);
v___x_2733_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__36));
lean_inc(v___x_2732_);
v___x_2734_ = l_Lean_Syntax_isOfKind(v___x_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; 
lean_dec(v___x_2732_);
lean_dec(v_stx_2700_);
v___x_2735_ = lean_box(0);
return v___x_2735_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2736_ = lean_unsigned_to_nat(1u);
v___x_2737_ = l_Lean_Syntax_getArg(v_stx_2700_, v___x_2736_);
v___x_2738_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1));
lean_inc(v___x_2737_);
v___x_2739_ = l_Lean_Syntax_isOfKind(v___x_2737_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; 
lean_dec(v___x_2737_);
lean_dec(v___x_2732_);
lean_dec(v_stx_2700_);
v___x_2740_ = lean_box(0);
return v___x_2740_;
}
else
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_Doc_CodeView_of(v___x_2737_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; 
lean_dec(v___x_2732_);
lean_dec(v_stx_2700_);
v___x_2742_ = lean_box(0);
return v___x_2742_;
}
else
{
lean_object* v_val_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2752_; 
v_val_2743_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2745_ = v___x_2741_;
v_isShared_2746_ = v_isSharedCheck_2752_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_val_2743_);
lean_dec(v___x_2741_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2752_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
uint8_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2747_ = 0;
v___x_2748_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2748_, 0, v_stx_2700_);
lean_ctor_set(v___x_2748_, 1, v___x_2732_);
lean_ctor_set(v___x_2748_, 2, v_val_2743_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*3, v___x_2747_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2748_);
v___x_2750_ = v___x_2745_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkView_of(lean_object* v_stx_2753_){
_start:
{
lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2754_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__29));
lean_inc(v_stx_2753_);
v___x_2755_ = l_Lean_Syntax_isOfKind(v_stx_2753_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; 
lean_dec(v_stx_2753_);
v___x_2756_ = lean_box(0);
return v___x_2756_;
}
else
{
lean_object* v___x_2757_; lean_object* v_tgt_2758_; lean_object* v___x_2759_; 
v___x_2757_ = lean_unsigned_to_nat(3u);
v_tgt_2758_ = l_Lean_Syntax_getArg(v_stx_2753_, v___x_2757_);
v___x_2759_ = l_Lean_Doc_LinkTargetView_of(v_tgt_2758_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v___x_2760_; 
lean_dec(v_stx_2753_);
v___x_2760_ = lean_box(0);
return v___x_2760_;
}
else
{
lean_object* v_val_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2776_; 
v_val_2761_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2763_ = v___x_2759_;
v_isShared_2764_ = v_isSharedCheck_2776_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_val_2761_);
lean_dec(v___x_2759_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2776_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; lean_object* v_o_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v_c_2770_; lean_object* v_inl_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2765_ = lean_unsigned_to_nat(0u);
v_o_2766_ = l_Lean_Syntax_getArg(v_stx_2753_, v___x_2765_);
v___x_2767_ = lean_unsigned_to_nat(1u);
v___x_2768_ = l_Lean_Syntax_getArg(v_stx_2753_, v___x_2767_);
v___x_2769_ = lean_unsigned_to_nat(2u);
v_c_2770_ = l_Lean_Syntax_getArg(v_stx_2753_, v___x_2769_);
v_inl_2771_ = l_Lean_Syntax_getArgs(v___x_2768_);
lean_dec(v___x_2768_);
v___x_2772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2772_, 0, v_stx_2753_);
lean_ctor_set(v___x_2772_, 1, v_o_2766_);
lean_ctor_set(v___x_2772_, 2, v_inl_2771_);
lean_ctor_set(v___x_2772_, 3, v_c_2770_);
lean_ctor_set(v___x_2772_, 4, v_val_2761_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2772_);
v___x_2774_ = v___x_2763_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt(lean_object* v_v_2777_){
_start:
{
lean_object* v_alt_2778_; lean_object* v___x_2779_; 
v_alt_2778_ = lean_ctor_get(v_v_2777_, 2);
v___x_2779_ = l_Lean_TSyntax_getVersoImageAlt(v_alt_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt___boxed(lean_object* v_v_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lean_Doc_ImageView_getAlt(v_v_2780_);
lean_dec_ref(v_v_2780_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_of(lean_object* v_stx_2788_){
_start:
{
lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2789_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__27));
lean_inc(v_stx_2788_);
v___x_2790_ = l_Lean_Syntax_isOfKind(v_stx_2788_, v___x_2789_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; 
lean_dec(v_stx_2788_);
v___x_2791_ = lean_box(0);
return v___x_2791_;
}
else
{
lean_object* v___x_2792_; lean_object* v_alt_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2792_ = lean_unsigned_to_nat(1u);
v_alt_2793_ = l_Lean_Syntax_getArg(v_stx_2788_, v___x_2792_);
v___x_2794_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__1));
lean_inc(v_alt_2793_);
v___x_2795_ = l_Lean_Syntax_isOfKind(v_alt_2793_, v___x_2794_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; 
lean_dec(v_alt_2793_);
lean_dec(v_stx_2788_);
v___x_2796_ = lean_box(0);
return v___x_2796_;
}
else
{
lean_object* v___x_2797_; lean_object* v_tgt_2798_; lean_object* v___x_2799_; 
v___x_2797_ = lean_unsigned_to_nat(3u);
v_tgt_2798_ = l_Lean_Syntax_getArg(v_stx_2788_, v___x_2797_);
v___x_2799_ = l_Lean_Doc_LinkTargetView_of(v_tgt_2798_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v___x_2800_; 
lean_dec(v_alt_2793_);
lean_dec(v_stx_2788_);
v___x_2800_ = lean_box(0);
return v___x_2800_;
}
else
{
lean_object* v_val_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2813_; 
v_val_2801_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2803_ = v___x_2799_;
v_isShared_2804_ = v_isSharedCheck_2813_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_val_2801_);
lean_dec(v___x_2799_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2813_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v_o_2806_; lean_object* v___x_2807_; lean_object* v_c_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2805_ = lean_unsigned_to_nat(0u);
v_o_2806_ = l_Lean_Syntax_getArg(v_stx_2788_, v___x_2805_);
v___x_2807_ = lean_unsigned_to_nat(2u);
v_c_2808_ = l_Lean_Syntax_getArg(v_stx_2788_, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2809_, 0, v_stx_2788_);
lean_ctor_set(v___x_2809_, 1, v_o_2806_);
lean_ctor_set(v___x_2809_, 2, v_alt_2793_);
lean_ctor_set(v___x_2809_, 3, v_c_2808_);
lean_ctor_set(v___x_2809_, 4, v_val_2801_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2809_);
v___x_2811_ = v___x_2803_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName(lean_object* v_v_2814_){
_start:
{
lean_object* v_name_2815_; lean_object* v___x_2816_; 
v_name_2815_ = lean_ctor_get(v_v_2814_, 2);
v___x_2816_ = l_Lean_TSyntax_getVersoRefName(v_name_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName___boxed(lean_object* v_v_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_Doc_FootnoteView_getName(v_v_2817_);
lean_dec_ref(v_v_2817_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_of(lean_object* v_stx_2819_){
_start:
{
lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2820_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__25));
lean_inc(v_stx_2819_);
v___x_2821_ = l_Lean_Syntax_isOfKind(v_stx_2819_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; 
lean_dec(v_stx_2819_);
v___x_2822_ = lean_box(0);
return v___x_2822_;
}
else
{
lean_object* v___x_2823_; lean_object* v_name_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2823_ = lean_unsigned_to_nat(1u);
v_name_2824_ = l_Lean_Syntax_getArg(v_stx_2819_, v___x_2823_);
v___x_2825_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__1));
lean_inc(v_name_2824_);
v___x_2826_ = l_Lean_Syntax_isOfKind(v_name_2824_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
lean_dec(v_name_2824_);
lean_dec(v_stx_2819_);
v___x_2827_ = lean_box(0);
return v___x_2827_;
}
else
{
lean_object* v___x_2828_; lean_object* v_o_2829_; lean_object* v___x_2830_; lean_object* v_c_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2828_ = lean_unsigned_to_nat(0u);
v_o_2829_ = l_Lean_Syntax_getArg(v_stx_2819_, v___x_2828_);
v___x_2830_ = lean_unsigned_to_nat(2u);
v_c_2831_ = l_Lean_Syntax_getArg(v_stx_2819_, v___x_2830_);
v___x_2832_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2832_, 0, v_stx_2819_);
lean_ctor_set(v___x_2832_, 1, v_o_2829_);
lean_ctor_set(v___x_2832_, 2, v_name_2824_);
lean_ctor_set(v___x_2832_, 3, v_c_2831_);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinebreakView_of(lean_object* v_stx_2834_){
_start:
{
lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
lean_inc(v_stx_2834_);
v___x_2836_ = l_Lean_Syntax_isOfKind(v_stx_2834_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; 
lean_dec(v_stx_2834_);
v___x_2837_ = lean_box(0);
return v___x_2837_;
}
else
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2838_ = lean_unsigned_to_nat(0u);
v___x_2839_ = l_Lean_Syntax_getArg(v_stx_2834_, v___x_2838_);
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v_stx_2834_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_RoleView_of(lean_object* v_stx_2842_){
_start:
{
lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2843_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__20));
lean_inc(v_stx_2842_);
v___x_2844_ = l_Lean_Syntax_isOfKind(v_stx_2842_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; 
lean_dec(v_stx_2842_);
v___x_2845_ = lean_box(0);
return v___x_2845_;
}
else
{
lean_object* v___x_2846_; lean_object* v_name_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2846_ = lean_unsigned_to_nat(1u);
v_name_2847_ = l_Lean_Syntax_getArg(v_stx_2842_, v___x_2846_);
v___x_2848_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2847_);
v___x_2849_ = l_Lean_Syntax_isOfKind(v_name_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; 
lean_dec(v_name_2847_);
lean_dec(v_stx_2842_);
v___x_2850_ = lean_box(0);
return v___x_2850_;
}
else
{
lean_object* v___x_2851_; lean_object* v_bo_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v_bc_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2851_ = lean_unsigned_to_nat(0u);
v_bo_2852_ = l_Lean_Syntax_getArg(v_stx_2842_, v___x_2851_);
v___x_2853_ = lean_unsigned_to_nat(2u);
v___x_2854_ = l_Lean_Syntax_getArg(v_stx_2842_, v___x_2853_);
v___x_2855_ = lean_unsigned_to_nat(3u);
v_bc_2856_ = l_Lean_Syntax_getArg(v_stx_2842_, v___x_2855_);
v___x_2857_ = lean_unsigned_to_nat(4u);
v___x_2858_ = l_Lean_Syntax_getArg(v_stx_2842_, v___x_2857_);
lean_inc(v___x_2858_);
v___x_2859_ = l_Lean_Syntax_matchesNull(v___x_2858_, v___x_2846_);
if (v___x_2859_ == 0)
{
uint8_t v___x_2860_; 
v___x_2860_ = l_Lean_Syntax_matchesNull(v___x_2858_, v___x_2851_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; 
lean_dec(v_bc_2856_);
lean_dec(v___x_2854_);
lean_dec(v_bo_2852_);
lean_dec(v_name_2847_);
lean_dec(v_stx_2842_);
v___x_2861_ = lean_box(0);
return v___x_2861_;
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2862_ = lean_unsigned_to_nat(6u);
v___x_2863_ = l_Lean_Syntax_getArg(v_stx_2842_, v___x_2862_);
v___x_2864_ = l_Lean_Syntax_matchesNull(v___x_2863_, v___x_2851_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; 
lean_dec(v_bc_2856_);
lean_dec(v___x_2854_);
lean_dec(v_bo_2852_);
lean_dec(v_name_2847_);
lean_dec(v_stx_2842_);
v___x_2865_ = lean_box(0);
return v___x_2865_;
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v_inl_2868_; lean_object* v_args_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2866_ = lean_unsigned_to_nat(5u);
v___x_2867_ = l_Lean_Syntax_getArg(v_stx_2842_, v___x_2866_);
v_inl_2868_ = l_Lean_Syntax_getArgs(v___x_2867_);
lean_dec(v___x_2867_);
v_args_2869_ = l_Lean_Syntax_getArgs(v___x_2854_);
lean_dec(v___x_2854_);
v___x_2870_ = lean_box(0);
v___x_2871_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2871_, 0, v_stx_2842_);
lean_ctor_set(v___x_2871_, 1, v_bo_2852_);
lean_ctor_set(v___x_2871_, 2, v_name_2847_);
lean_ctor_set(v___x_2871_, 3, v_args_2869_);
lean_ctor_set(v___x_2871_, 4, v_bc_2856_);
lean_ctor_set(v___x_2871_, 5, v___x_2870_);
lean_ctor_set(v___x_2871_, 6, v_inl_2868_);
v___x_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2873_ = lean_unsigned_to_nat(6u);
v___x_2874_ = l_Lean_Syntax_getArg(v_stx_2842_, v___x_2873_);
lean_inc(v___x_2874_);
v___x_2875_ = l_Lean_Syntax_matchesNull(v___x_2874_, v___x_2846_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; 
lean_dec(v___x_2874_);
lean_dec(v___x_2858_);
lean_dec(v_bc_2856_);
lean_dec(v___x_2854_);
lean_dec(v_bo_2852_);
lean_dec(v_name_2847_);
lean_dec(v_stx_2842_);
v___x_2876_ = lean_box(0);
return v___x_2876_;
}
else
{
lean_object* v_so_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v_sc_2880_; lean_object* v_inl_2881_; lean_object* v_args_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_so_2877_ = l_Lean_Syntax_getArg(v___x_2858_, v___x_2851_);
lean_dec(v___x_2858_);
v___x_2878_ = lean_unsigned_to_nat(5u);
v___x_2879_ = l_Lean_Syntax_getArg(v_stx_2842_, v___x_2878_);
v_sc_2880_ = l_Lean_Syntax_getArg(v___x_2874_, v___x_2851_);
lean_dec(v___x_2874_);
v_inl_2881_ = l_Lean_Syntax_getArgs(v___x_2879_);
lean_dec(v___x_2879_);
v_args_2882_ = l_Lean_Syntax_getArgs(v___x_2854_);
lean_dec(v___x_2854_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_so_2877_);
lean_ctor_set(v___x_2883_, 1, v_sc_2880_);
v___x_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
v___x_2885_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2885_, 0, v_stx_2842_);
lean_ctor_set(v___x_2885_, 1, v_bo_2852_);
lean_ctor_set(v___x_2885_, 2, v_name_2847_);
lean_ctor_set(v___x_2885_, 3, v_args_2882_);
lean_ctor_set(v___x_2885_, 4, v_bc_2856_);
lean_ctor_set(v___x_2885_, 5, v___x_2884_);
lean_ctor_set(v___x_2885_, 6, v_inl_2881_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
return v___x_2886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx(lean_object* v_x_2887_){
_start:
{
switch(lean_obj_tag(v_x_2887_))
{
case 0:
{
lean_object* v___x_2888_; 
v___x_2888_ = lean_unsigned_to_nat(0u);
return v___x_2888_;
}
case 1:
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_unsigned_to_nat(1u);
return v___x_2889_;
}
case 2:
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_unsigned_to_nat(2u);
return v___x_2890_;
}
case 3:
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_unsigned_to_nat(3u);
return v___x_2891_;
}
case 4:
{
lean_object* v___x_2892_; 
v___x_2892_ = lean_unsigned_to_nat(4u);
return v___x_2892_;
}
case 5:
{
lean_object* v___x_2893_; 
v___x_2893_ = lean_unsigned_to_nat(5u);
return v___x_2893_;
}
case 6:
{
lean_object* v___x_2894_; 
v___x_2894_ = lean_unsigned_to_nat(6u);
return v___x_2894_;
}
case 7:
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_unsigned_to_nat(7u);
return v___x_2895_;
}
case 8:
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_unsigned_to_nat(8u);
return v___x_2896_;
}
default: 
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_unsigned_to_nat(9u);
return v___x_2897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___boxed(lean_object* v_x_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_Doc_InlineView_ctorIdx(v_x_2898_);
lean_dec_ref(v_x_2898_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___redArg(lean_object* v_t_2900_, lean_object* v_k_2901_){
_start:
{
lean_object* v_view_2902_; lean_object* v___x_2903_; 
v_view_2902_ = lean_ctor_get(v_t_2900_, 0);
lean_inc_ref(v_view_2902_);
lean_dec_ref(v_t_2900_);
v___x_2903_ = lean_apply_1(v_k_2901_, v_view_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim(lean_object* v_motive_2904_, lean_object* v_ctorIdx_2905_, lean_object* v_t_2906_, lean_object* v_h_2907_, lean_object* v_k_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2906_, v_k_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___boxed(lean_object* v_motive_2910_, lean_object* v_ctorIdx_2911_, lean_object* v_t_2912_, lean_object* v_h_2913_, lean_object* v_k_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_Doc_InlineView_ctorElim(v_motive_2910_, v_ctorIdx_2911_, v_t_2912_, v_h_2913_, v_k_2914_);
lean_dec(v_ctorIdx_2911_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim___redArg(lean_object* v_t_2916_, lean_object* v_text_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2916_, v_text_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim(lean_object* v_motive_2919_, lean_object* v_t_2920_, lean_object* v_h_2921_, lean_object* v_text_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2920_, v_text_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim___redArg(lean_object* v_t_2924_, lean_object* v_emph_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2924_, v_emph_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim(lean_object* v_motive_2927_, lean_object* v_t_2928_, lean_object* v_h_2929_, lean_object* v_emph_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2928_, v_emph_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim___redArg(lean_object* v_t_2932_, lean_object* v_bold_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2932_, v_bold_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim(lean_object* v_motive_2935_, lean_object* v_t_2936_, lean_object* v_h_2937_, lean_object* v_bold_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2936_, v_bold_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim___redArg(lean_object* v_t_2940_, lean_object* v_code_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2940_, v_code_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim(lean_object* v_motive_2943_, lean_object* v_t_2944_, lean_object* v_h_2945_, lean_object* v_code_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2944_, v_code_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim___redArg(lean_object* v_t_2948_, lean_object* v_math_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2948_, v_math_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim(lean_object* v_motive_2951_, lean_object* v_t_2952_, lean_object* v_h_2953_, lean_object* v_math_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2952_, v_math_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim___redArg(lean_object* v_t_2956_, lean_object* v_link_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2956_, v_link_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim(lean_object* v_motive_2959_, lean_object* v_t_2960_, lean_object* v_h_2961_, lean_object* v_link_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2960_, v_link_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim___redArg(lean_object* v_t_2964_, lean_object* v_image_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2964_, v_image_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim(lean_object* v_motive_2967_, lean_object* v_t_2968_, lean_object* v_h_2969_, lean_object* v_image_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2968_, v_image_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim___redArg(lean_object* v_t_2972_, lean_object* v_footnote_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2972_, v_footnote_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim(lean_object* v_motive_2975_, lean_object* v_t_2976_, lean_object* v_h_2977_, lean_object* v_footnote_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2976_, v_footnote_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim___redArg(lean_object* v_t_2980_, lean_object* v_linebreak_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2980_, v_linebreak_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim(lean_object* v_motive_2983_, lean_object* v_t_2984_, lean_object* v_h_2985_, lean_object* v_linebreak_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2984_, v_linebreak_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim___redArg(lean_object* v_t_2988_, lean_object* v_role_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2988_, v_role_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim(lean_object* v_motive_2991_, lean_object* v_t_2992_, lean_object* v_h_2993_, lean_object* v_role_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2992_, v_role_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTextViewInlineView___lam__0(lean_object* v_view_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_view_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeEmphViewInlineView___lam__0(lean_object* v_view_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3005_, 0, v_view_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBoldViewInlineView___lam__0(lean_object* v_view_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_view_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeViewInlineView___lam__0(lean_object* v_view_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3013_, 0, v_view_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMathViewInlineView___lam__0(lean_object* v_view_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_view_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkViewInlineView___lam__0(lean_object* v_view_3020_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_view_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeImageViewInlineView___lam__0(lean_object* v_view_3024_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_view_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0(lean_object* v_view_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_view_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0(lean_object* v_view_3032_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_view_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeRoleViewInlineView___lam__0(lean_object* v_view_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3037_, 0, v_view_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx(lean_object* v_x_3040_){
_start:
{
lean_object* v_view_3041_; lean_object* v_stx_3042_; 
v_view_3041_ = lean_ctor_get(v_x_3040_, 0);
v_stx_3042_ = lean_ctor_get(v_view_3041_, 0);
lean_inc(v_stx_3042_);
return v_stx_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx___boxed(lean_object* v_x_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Doc_InlineView_stx(v_x_3043_);
lean_dec_ref(v_x_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_of(lean_object* v_stx_3045_){
_start:
{
lean_object* v___x_3046_; 
lean_inc(v_stx_3045_);
v___x_3046_ = l_Lean_Doc_TextView_of(v_stx_3045_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v___x_3047_; 
lean_inc(v_stx_3045_);
v___x_3047_ = l_Lean_Doc_EmphView_of(v_stx_3045_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v___x_3048_; 
lean_inc(v_stx_3045_);
v___x_3048_ = l_Lean_Doc_BoldView_of(v_stx_3045_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3049_; 
lean_inc(v_stx_3045_);
v___x_3049_ = l_Lean_Doc_CodeView_of(v_stx_3045_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v___x_3050_; 
lean_inc(v_stx_3045_);
v___x_3050_ = l_Lean_Doc_MathView_of(v_stx_3045_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v___x_3051_; 
lean_inc(v_stx_3045_);
v___x_3051_ = l_Lean_Doc_LinkView_of(v_stx_3045_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v___x_3052_; 
lean_inc(v_stx_3045_);
v___x_3052_ = l_Lean_Doc_ImageView_of(v_stx_3045_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3053_; 
lean_inc(v_stx_3045_);
v___x_3053_ = l_Lean_Doc_FootnoteView_of(v_stx_3045_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v___x_3054_; 
lean_inc(v_stx_3045_);
v___x_3054_ = l_Lean_Doc_LinebreakView_of(v_stx_3045_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Lean_Doc_RoleView_of(v_stx_3045_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_box(0);
return v___x_3056_;
}
else
{
lean_object* v_val_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3065_; 
v_val_3057_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3059_ = v___x_3055_;
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_val_3057_);
lean_dec(v___x_3055_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3061_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3061_, 0, v_val_3057_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3061_);
v___x_3063_ = v___x_3059_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_object* v_val_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v_stx_3045_);
v_val_3066_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3068_ = v___x_3054_;
v_isShared_3069_ = v_isSharedCheck_3074_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_val_3066_);
lean_dec(v___x_3054_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3074_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3070_; lean_object* v___x_3072_; 
v___x_3070_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_val_3066_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3070_);
v___x_3072_ = v___x_3068_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3070_);
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
else
{
lean_object* v_val_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_stx_3045_);
v_val_3075_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3077_ = v___x_3053_;
v_isShared_3078_ = v_isSharedCheck_3083_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_val_3075_);
lean_dec(v___x_3053_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3083_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3079_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3079_, 0, v_val_3075_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v___x_3079_);
v___x_3081_ = v___x_3077_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_val_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_stx_3045_);
v_val_3084_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3086_ = v___x_3052_;
v_isShared_3087_ = v_isSharedCheck_3092_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_val_3084_);
lean_dec(v___x_3052_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3092_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3088_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_val_3084_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3088_);
v___x_3090_ = v___x_3086_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3088_);
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
lean_object* v_val_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v_stx_3045_);
v_val_3093_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3095_ = v___x_3051_;
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_val_3093_);
lean_dec(v___x_3051_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3097_, 0, v_val_3093_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v___x_3097_);
v___x_3099_ = v___x_3095_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v_val_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3110_; 
lean_dec(v_stx_3045_);
v_val_3102_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3104_ = v___x_3050_;
v_isShared_3105_ = v_isSharedCheck_3110_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_val_3102_);
lean_dec(v___x_3050_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3110_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_val_3102_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v___x_3106_);
v___x_3108_ = v___x_3104_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
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
else
{
lean_object* v_val_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_stx_3045_);
v_val_3111_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3113_ = v___x_3049_;
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_val_3111_);
lean_dec(v___x_3049_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3115_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3115_, 0, v_val_3111_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_object* v_val_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_stx_3045_);
v_val_3120_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3122_ = v___x_3048_;
v_isShared_3123_ = v_isSharedCheck_3128_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_val_3120_);
lean_dec(v___x_3048_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3128_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3124_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3124_, 0, v_val_3120_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3124_);
v___x_3126_ = v___x_3122_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
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
else
{
lean_object* v_val_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3137_; 
lean_dec(v_stx_3045_);
v_val_3129_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3131_ = v___x_3047_;
v_isShared_3132_ = v_isSharedCheck_3137_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_val_3129_);
lean_dec(v___x_3047_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3137_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v_val_3129_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v___x_3133_);
v___x_3135_ = v___x_3131_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
else
{
lean_object* v_val_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_stx_3045_);
v_val_3138_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3140_ = v___x_3046_;
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_val_3138_);
lean_dec(v___x_3046_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_val_3138_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3142_);
v___x_3144_ = v___x_3140_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(uint32_t v_a_3147_, lean_object* v_x_3148_){
_start:
{
if (lean_obj_tag(v_x_3148_) == 0)
{
uint8_t v___x_3149_; 
v___x_3149_ = 0;
return v___x_3149_;
}
else
{
lean_object* v_head_3150_; lean_object* v_tail_3151_; uint32_t v___x_3152_; uint8_t v___x_3153_; 
v_head_3150_ = lean_ctor_get(v_x_3148_, 0);
v_tail_3151_ = lean_ctor_get(v_x_3148_, 1);
v___x_3152_ = lean_unbox_uint32(v_head_3150_);
v___x_3153_ = lean_uint32_dec_eq(v_a_3147_, v___x_3152_);
if (v___x_3153_ == 0)
{
v_x_3148_ = v_tail_3151_;
goto _start;
}
else
{
return v___x_3153_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0___boxed(lean_object* v_a_3155_, lean_object* v_x_3156_){
_start:
{
uint32_t v_a_boxed_3157_; uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_a_boxed_3157_ = lean_unbox_uint32(v_a_3155_);
lean_dec(v_a_3155_);
v_res_3158_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v_a_boxed_3157_, v_x_3156_);
lean_dec(v_x_3156_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = 43;
v___x_3161_ = lean_box_uint32(v___x_3160_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__0(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = lean_box(0);
v___x_3163_ = l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1;
v___x_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___x_3162_);
return v___x_3164_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = 45;
v___x_3166_ = lean_box_uint32(v___x_3165_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__1(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__0, &l_Lean_Doc_UnorderedListItemView_of___closed__0_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__0);
v___x_3168_ = l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1;
v___x_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
lean_ctor_set(v___x_3169_, 1, v___x_3167_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = 42;
v___x_3171_ = lean_box_uint32(v___x_3170_);
return v___x_3171_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__2(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__1, &l_Lean_Doc_UnorderedListItemView_of___closed__1_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__1);
v___x_3173_ = l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1;
v___x_3174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of(lean_object* v_stx_3175_){
_start:
{
lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3176_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__4));
lean_inc(v_stx_3175_);
v___x_3177_ = l_Lean_Syntax_isOfKind(v_stx_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; 
lean_dec(v_stx_3175_);
v___x_3178_ = lean_box(0);
return v___x_3178_;
}
else
{
lean_object* v___x_3179_; lean_object* v_m_3180_; lean_object* v___x_3181_; uint8_t v___x_3182_; 
v___x_3179_ = lean_unsigned_to_nat(0u);
v_m_3180_ = l_Lean_Syntax_getArg(v_stx_3175_, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__6));
lean_inc(v_m_3180_);
v___x_3182_ = l_Lean_Syntax_isOfKind(v_m_3180_, v___x_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; 
lean_dec(v_m_3180_);
lean_dec(v_stx_3175_);
v___x_3183_ = lean_box(0);
return v___x_3183_;
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3184_ = l_Lean_TSyntax_getVersoDelimiter(v_m_3180_);
v___x_3185_ = lean_string_utf8_byte_size(v___x_3184_);
v___x_3186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3184_);
lean_ctor_set(v___x_3186_, 1, v___x_3179_);
lean_ctor_set(v___x_3186_, 2, v___x_3185_);
v___x_3187_ = l_String_Slice_Pos_get_x3f(v___x_3186_, v___x_3179_);
lean_dec_ref_known(v___x_3186_, 3);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v___x_3188_; 
lean_dec(v_m_3180_);
lean_dec(v_stx_3175_);
v___x_3188_ = lean_box(0);
return v___x_3188_;
}
else
{
lean_object* v_val_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3204_; 
v_val_3189_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3191_ = v___x_3187_;
v_isShared_3192_ = v_isSharedCheck_3204_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_val_3189_);
lean_dec(v___x_3187_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3204_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; uint32_t v___x_3194_; uint8_t v___x_3195_; 
v___x_3193_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__2, &l_Lean_Doc_UnorderedListItemView_of___closed__2_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__2);
v___x_3194_ = lean_unbox_uint32(v_val_3189_);
lean_dec(v_val_3189_);
v___x_3195_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v___x_3194_, v___x_3193_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; 
lean_del_object(v___x_3191_);
lean_dec(v_m_3180_);
lean_dec(v_stx_3175_);
v___x_3196_ = lean_box(0);
return v___x_3196_;
}
else
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_bs_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3197_ = lean_unsigned_to_nat(1u);
v___x_3198_ = l_Lean_Syntax_getArg(v_stx_3175_, v___x_3197_);
v_bs_3199_ = l_Lean_Syntax_getArgs(v___x_3198_);
lean_dec(v___x_3198_);
v___x_3200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3200_, 0, v_stx_3175_);
lean_ctor_set(v___x_3200_, 1, v_m_3180_);
lean_ctor_set(v___x_3200_, 2, v_bs_3199_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3200_);
v___x_3202_ = v___x_3191_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(lean_object* v_s_3205_, lean_object* v_pos_3206_){
_start:
{
lean_object* v_str_3207_; lean_object* v_startInclusive_3208_; lean_object* v_endExclusive_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v_decide_3213_; 
v_str_3207_ = lean_ctor_get(v_s_3205_, 0);
v_startInclusive_3208_ = lean_ctor_get(v_s_3205_, 1);
v_endExclusive_3209_ = lean_ctor_get(v_s_3205_, 2);
v___x_3210_ = lean_nat_add(v_startInclusive_3208_, v_pos_3206_);
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = lean_nat_sub(v_endExclusive_3209_, v___x_3210_);
v_decide_3213_ = lean_nat_dec_eq(v___x_3211_, v___x_3212_);
lean_dec(v___x_3212_);
if (v_decide_3213_ == 0)
{
uint32_t v___x_3214_; uint32_t v___x_3215_; uint8_t v___x_3216_; 
v___x_3214_ = lean_string_utf8_get_fast(v_str_3207_, v___x_3210_);
v___x_3215_ = 48;
v___x_3216_ = lean_uint32_dec_le(v___x_3215_, v___x_3214_);
if (v___x_3216_ == 0)
{
lean_dec(v___x_3210_);
return v_pos_3206_;
}
else
{
uint32_t v___x_3217_; uint8_t v___x_3218_; 
v___x_3217_ = 57;
v___x_3218_ = lean_uint32_dec_le(v___x_3214_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_dec(v___x_3210_);
return v_pos_3206_;
}
else
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3219_ = lean_string_utf8_next_fast(v_str_3207_, v___x_3210_);
v___x_3220_ = lean_nat_sub(v___x_3219_, v___x_3210_);
lean_dec(v___x_3210_);
v___x_3221_ = lean_nat_add(v_pos_3206_, v___x_3220_);
lean_dec(v___x_3220_);
v___x_3222_ = lean_unsigned_to_nat(1u);
v___x_3223_ = lean_nat_add(v_pos_3206_, v___x_3222_);
v___x_3224_ = lean_nat_dec_le(v___x_3223_, v___x_3221_);
lean_dec(v___x_3223_);
if (v___x_3224_ == 0)
{
lean_dec(v___x_3221_);
return v_pos_3206_;
}
else
{
lean_dec(v_pos_3206_);
v_pos_3206_ = v___x_3221_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_3210_);
return v_pos_3206_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0___boxed(lean_object* v_s_3226_, lean_object* v_pos_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v_s_3226_, v_pos_3227_);
lean_dec_ref(v_s_3226_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_number(lean_object* v_v_3229_){
_start:
{
lean_object* v_marker_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3245_; 
v_marker_3230_ = lean_ctor_get(v_v_3229_, 1);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_v_3229_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; lean_object* v_unused_3247_; 
v_unused_3246_ = lean_ctor_get(v_v_3229_, 2);
lean_dec(v_unused_3246_);
v_unused_3247_ = lean_ctor_get(v_v_3229_, 0);
lean_dec(v_unused_3247_);
v___x_3232_ = v_v_3229_;
v_isShared_3233_ = v_isSharedCheck_3245_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_marker_3230_);
lean_dec(v_v_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3245_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3234_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_3230_);
lean_dec(v_marker_3230_);
v___x_3235_ = lean_unsigned_to_nat(0u);
v___x_3236_ = lean_string_utf8_byte_size(v___x_3234_);
lean_inc_ref(v___x_3234_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 2, v___x_3236_);
lean_ctor_set(v___x_3232_, 1, v___x_3235_);
lean_ctor_set(v___x_3232_, 0, v___x_3234_);
v___x_3238_ = v___x_3232_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3239_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v___x_3238_, v___x_3235_);
lean_dec_ref(v___x_3238_);
v___x_3240_ = lean_string_utf8_extract_fast(v___x_3234_, v___x_3235_, v___x_3239_);
lean_dec(v___x_3239_);
lean_dec_ref(v___x_3234_);
v___x_3241_ = lean_string_utf8_byte_size(v___x_3240_);
v___x_3242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3235_);
lean_ctor_set(v___x_3242_, 2, v___x_3241_);
v___x_3243_ = l_String_Slice_toNat_x3f(v___x_3242_);
lean_dec_ref_known(v___x_3242_, 3);
return v___x_3243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_of(lean_object* v_stx_3248_){
_start:
{
lean_object* v___x_3249_; uint8_t v___x_3250_; 
v___x_3249_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__4));
lean_inc(v_stx_3248_);
v___x_3250_ = l_Lean_Syntax_isOfKind(v_stx_3248_, v___x_3249_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; 
lean_dec(v_stx_3248_);
v___x_3251_ = lean_box(0);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; lean_object* v_m_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3252_ = lean_unsigned_to_nat(0u);
v_m_3253_ = l_Lean_Syntax_getArg(v_stx_3248_, v___x_3252_);
v___x_3254_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__6));
lean_inc(v_m_3253_);
v___x_3255_ = l_Lean_Syntax_isOfKind(v_m_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
lean_dec(v_m_3253_);
lean_dec(v_stx_3248_);
v___x_3256_ = lean_box(0);
return v___x_3256_;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3257_ = l_Lean_TSyntax_getVersoDelimiter(v_m_3253_);
v___x_3258_ = lean_string_utf8_byte_size(v___x_3257_);
v___x_3259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3252_);
lean_ctor_set(v___x_3259_, 2, v___x_3258_);
v___x_3260_ = l_String_Slice_Pos_get_x3f(v___x_3259_, v___x_3252_);
lean_dec_ref_known(v___x_3259_, 3);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v___x_3261_; 
lean_dec(v_m_3253_);
lean_dec(v_stx_3248_);
v___x_3261_ = lean_box(0);
return v___x_3261_;
}
else
{
lean_object* v_val_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3281_; 
v_val_3262_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3264_ = v___x_3260_;
v_isShared_3265_ = v_isSharedCheck_3281_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_val_3262_);
lean_dec(v___x_3260_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3281_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
uint32_t v___x_3266_; uint32_t v___x_3267_; uint8_t v___x_3268_; 
v___x_3266_ = 48;
v___x_3267_ = lean_unbox_uint32(v_val_3262_);
v___x_3268_ = lean_uint32_dec_le(v___x_3266_, v___x_3267_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; 
lean_del_object(v___x_3264_);
lean_dec(v_val_3262_);
lean_dec(v_m_3253_);
lean_dec(v_stx_3248_);
v___x_3269_ = lean_box(0);
return v___x_3269_;
}
else
{
uint32_t v___x_3270_; uint32_t v___x_3271_; uint8_t v___x_3272_; 
v___x_3270_ = 57;
v___x_3271_ = lean_unbox_uint32(v_val_3262_);
lean_dec(v_val_3262_);
v___x_3272_ = lean_uint32_dec_le(v___x_3271_, v___x_3270_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; 
lean_del_object(v___x_3264_);
lean_dec(v_m_3253_);
lean_dec(v_stx_3248_);
v___x_3273_ = lean_box(0);
return v___x_3273_;
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v_bs_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
v___x_3274_ = lean_unsigned_to_nat(1u);
v___x_3275_ = l_Lean_Syntax_getArg(v_stx_3248_, v___x_3274_);
v_bs_3276_ = l_Lean_Syntax_getArgs(v___x_3275_);
lean_dec(v___x_3275_);
v___x_3277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3277_, 0, v_stx_3248_);
lean_ctor_set(v___x_3277_, 1, v_m_3253_);
lean_ctor_set(v___x_3277_, 2, v_bs_3276_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v___x_3277_);
v___x_3279_ = v___x_3264_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescItemView_of(lean_object* v_stx_3282_){
_start:
{
lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3283_ = ((lean_object*)(l_Lean_Doc_descItemToParser___closed__3));
lean_inc(v_stx_3282_);
v___x_3284_ = l_Lean_Syntax_isOfKind(v_stx_3282_, v___x_3283_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; 
lean_dec(v_stx_3282_);
v___x_3285_ = lean_box(0);
return v___x_3285_;
}
else
{
lean_object* v___x_3286_; lean_object* v_marker_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v_desc_3292_; lean_object* v_term_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3286_ = lean_unsigned_to_nat(0u);
v_marker_3287_ = l_Lean_Syntax_getArg(v_stx_3282_, v___x_3286_);
v___x_3288_ = lean_unsigned_to_nat(1u);
v___x_3289_ = l_Lean_Syntax_getArg(v_stx_3282_, v___x_3288_);
v___x_3290_ = lean_unsigned_to_nat(2u);
v___x_3291_ = l_Lean_Syntax_getArg(v_stx_3282_, v___x_3290_);
v_desc_3292_ = l_Lean_Syntax_getArgs(v___x_3291_);
lean_dec(v___x_3291_);
v_term_3293_ = l_Lean_Syntax_getArgs(v___x_3289_);
lean_dec(v___x_3289_);
v___x_3294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3294_, 0, v_stx_3282_);
lean_ctor_set(v___x_3294_, 1, v_marker_3287_);
lean_ctor_set(v___x_3294_, 2, v_term_3293_);
lean_ctor_set(v___x_3294_, 3, v_desc_3292_);
v___x_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
return v___x_3295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ParaView_of(lean_object* v_stx_3303_){
_start:
{
lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3304_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__42));
lean_inc(v_stx_3303_);
v___x_3305_ = l_Lean_Syntax_isOfKind(v_stx_3303_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; 
lean_dec(v_stx_3303_);
v___x_3306_ = lean_box(0);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_inl_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3307_ = lean_unsigned_to_nat(0u);
v___x_3308_ = l_Lean_Syntax_getArg(v_stx_3303_, v___x_3307_);
v_inl_3309_ = l_Lean_Syntax_getArgs(v___x_3308_);
lean_dec(v___x_3308_);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_stx_3303_);
lean_ctor_set(v___x_3310_, 1, v_inl_3309_);
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(size_t v_sz_3312_, size_t v_i_3313_, lean_object* v_bs_3314_){
_start:
{
uint8_t v___x_3315_; 
v___x_3315_ = lean_usize_dec_lt(v_i_3313_, v_sz_3312_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v_bs_3314_);
return v___x_3316_;
}
else
{
lean_object* v_v_3317_; lean_object* v___x_3318_; 
v_v_3317_ = lean_array_uget_borrowed(v_bs_3314_, v_i_3313_);
lean_inc(v_v_3317_);
v___x_3318_ = l_Lean_Doc_UnorderedListItemView_of(v_v_3317_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v___x_3319_; 
lean_dec_ref(v_bs_3314_);
v___x_3319_ = lean_box(0);
return v___x_3319_;
}
else
{
lean_object* v_val_3320_; lean_object* v___x_3321_; lean_object* v_bs_x27_3322_; size_t v___x_3323_; size_t v___x_3324_; lean_object* v___x_3325_; 
v_val_3320_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_val_3320_);
lean_dec_ref_known(v___x_3318_, 1);
v___x_3321_ = lean_unsigned_to_nat(0u);
v_bs_x27_3322_ = lean_array_uset(v_bs_3314_, v_i_3313_, v___x_3321_);
v___x_3323_ = ((size_t)1ULL);
v___x_3324_ = lean_usize_add(v_i_3313_, v___x_3323_);
v___x_3325_ = lean_array_uset(v_bs_x27_3322_, v_i_3313_, v_val_3320_);
v_i_3313_ = v___x_3324_;
v_bs_3314_ = v___x_3325_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0___boxed(lean_object* v_sz_3327_, lean_object* v_i_3328_, lean_object* v_bs_3329_){
_start:
{
size_t v_sz_boxed_3330_; size_t v_i_boxed_3331_; lean_object* v_res_3332_; 
v_sz_boxed_3330_ = lean_unbox_usize(v_sz_3327_);
lean_dec(v_sz_3327_);
v_i_boxed_3331_ = lean_unbox_usize(v_i_3328_);
lean_dec(v_i_3328_);
v_res_3332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_boxed_3330_, v_i_boxed_3331_, v_bs_3329_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListView_of(lean_object* v_stx_3333_){
_start:
{
lean_object* v___x_3334_; uint8_t v___x_3335_; 
v___x_3334_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__40));
lean_inc(v_stx_3333_);
v___x_3335_ = l_Lean_Syntax_isOfKind(v_stx_3333_, v___x_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
lean_dec(v_stx_3333_);
v___x_3336_ = lean_box(0);
return v___x_3336_;
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v_items_3339_; size_t v_sz_3340_; size_t v___x_3341_; lean_object* v___x_3342_; 
v___x_3337_ = lean_unsigned_to_nat(0u);
v___x_3338_ = l_Lean_Syntax_getArg(v_stx_3333_, v___x_3337_);
v_items_3339_ = l_Lean_Syntax_getArgs(v___x_3338_);
lean_dec(v___x_3338_);
v_sz_3340_ = lean_array_size(v_items_3339_);
v___x_3341_ = ((size_t)0ULL);
v___x_3342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_3340_, v___x_3341_, v_items_3339_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v___x_3343_; 
lean_dec(v_stx_3333_);
v___x_3343_ = lean_box(0);
return v___x_3343_;
}
else
{
lean_object* v_val_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3352_; 
v_val_3344_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3346_ = v___x_3342_;
v_isShared_3347_ = v_isSharedCheck_3352_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_val_3344_);
lean_dec(v___x_3342_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3352_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v_stx_3333_);
lean_ctor_set(v___x_3348_, 1, v_val_3344_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3348_);
v___x_3350_ = v___x_3346_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3348_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(size_t v_sz_3353_, size_t v_i_3354_, lean_object* v_bs_3355_){
_start:
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_usize_dec_lt(v_i_3354_, v_sz_3353_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3357_, 0, v_bs_3355_);
return v___x_3357_;
}
else
{
lean_object* v_v_3358_; lean_object* v___x_3359_; 
v_v_3358_ = lean_array_uget_borrowed(v_bs_3355_, v_i_3354_);
lean_inc(v_v_3358_);
v___x_3359_ = l_Lean_Doc_OrderedListItemView_of(v_v_3358_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v___x_3360_; 
lean_dec_ref(v_bs_3355_);
v___x_3360_ = lean_box(0);
return v___x_3360_;
}
else
{
lean_object* v_val_3361_; lean_object* v___x_3362_; lean_object* v_bs_x27_3363_; size_t v___x_3364_; size_t v___x_3365_; lean_object* v___x_3366_; 
v_val_3361_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_val_3361_);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3362_ = lean_unsigned_to_nat(0u);
v_bs_x27_3363_ = lean_array_uset(v_bs_3355_, v_i_3354_, v___x_3362_);
v___x_3364_ = ((size_t)1ULL);
v___x_3365_ = lean_usize_add(v_i_3354_, v___x_3364_);
v___x_3366_ = lean_array_uset(v_bs_x27_3363_, v_i_3354_, v_val_3361_);
v_i_3354_ = v___x_3365_;
v_bs_3355_ = v___x_3366_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0___boxed(lean_object* v_sz_3368_, lean_object* v_i_3369_, lean_object* v_bs_3370_){
_start:
{
size_t v_sz_boxed_3371_; size_t v_i_boxed_3372_; lean_object* v_res_3373_; 
v_sz_boxed_3371_ = lean_unbox_usize(v_sz_3368_);
lean_dec(v_sz_3368_);
v_i_boxed_3372_ = lean_unbox_usize(v_i_3369_);
lean_dec(v_i_3369_);
v_res_3373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_boxed_3371_, v_i_boxed_3372_, v_bs_3370_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListView_of(lean_object* v_stx_3374_){
_start:
{
lean_object* v___x_3375_; uint8_t v___x_3376_; 
v___x_3375_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__39));
lean_inc(v_stx_3374_);
v___x_3376_ = l_Lean_Syntax_isOfKind(v_stx_3374_, v___x_3375_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; 
lean_dec(v_stx_3374_);
v___x_3377_ = lean_box(0);
return v___x_3377_;
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v_items_3380_; size_t v_sz_3381_; size_t v___x_3382_; lean_object* v___x_3383_; 
v___x_3378_ = lean_unsigned_to_nat(0u);
v___x_3379_ = l_Lean_Syntax_getArg(v_stx_3374_, v___x_3378_);
v_items_3380_ = l_Lean_Syntax_getArgs(v___x_3379_);
lean_dec(v___x_3379_);
v_sz_3381_ = lean_array_size(v_items_3380_);
v___x_3382_ = ((size_t)0ULL);
v___x_3383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_3381_, v___x_3382_, v_items_3380_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3384_; 
lean_dec(v_stx_3374_);
v___x_3384_ = lean_box(0);
return v___x_3384_;
}
else
{
lean_object* v_val_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3402_; 
v_val_3385_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3387_ = v___x_3383_;
v_isShared_3388_ = v_isSharedCheck_3402_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_val_3385_);
lean_dec(v___x_3383_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3402_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___y_3390_; lean_object* v___x_3397_; uint8_t v___x_3398_; 
v___x_3397_ = lean_array_get_size(v_val_3385_);
v___x_3398_ = lean_nat_dec_lt(v___x_3378_, v___x_3397_);
if (v___x_3398_ == 0)
{
goto v___jp_3395_;
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = lean_array_fget_borrowed(v_val_3385_, v___x_3378_);
lean_inc(v___x_3399_);
v___x_3400_ = l_Lean_Doc_OrderedListItemView_number(v___x_3399_);
if (lean_obj_tag(v___x_3400_) == 0)
{
goto v___jp_3395_;
}
else
{
lean_object* v_val_3401_; 
v_val_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v___y_3390_ = v_val_3401_;
goto v___jp_3389_;
}
}
v___jp_3389_:
{
lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3391_, 0, v_stx_3374_);
lean_ctor_set(v___x_3391_, 1, v___y_3390_);
lean_ctor_set(v___x_3391_, 2, v_val_3385_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3391_);
v___x_3393_ = v___x_3387_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
v___jp_3395_:
{
lean_object* v___x_3396_; 
v___x_3396_ = lean_unsigned_to_nat(1u);
v___y_3390_ = v___x_3396_;
goto v___jp_3389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(size_t v_sz_3403_, size_t v_i_3404_, lean_object* v_bs_3405_){
_start:
{
uint8_t v___x_3406_; 
v___x_3406_ = lean_usize_dec_lt(v_i_3404_, v_sz_3403_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3407_, 0, v_bs_3405_);
return v___x_3407_;
}
else
{
lean_object* v_v_3408_; lean_object* v___x_3409_; 
v_v_3408_ = lean_array_uget_borrowed(v_bs_3405_, v_i_3404_);
lean_inc(v_v_3408_);
v___x_3409_ = l_Lean_Doc_DescItemView_of(v_v_3408_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v___x_3410_; 
lean_dec_ref(v_bs_3405_);
v___x_3410_ = lean_box(0);
return v___x_3410_;
}
else
{
lean_object* v_val_3411_; lean_object* v___x_3412_; lean_object* v_bs_x27_3413_; size_t v___x_3414_; size_t v___x_3415_; lean_object* v___x_3416_; 
v_val_3411_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_val_3411_);
lean_dec_ref_known(v___x_3409_, 1);
v___x_3412_ = lean_unsigned_to_nat(0u);
v_bs_x27_3413_ = lean_array_uset(v_bs_3405_, v_i_3404_, v___x_3412_);
v___x_3414_ = ((size_t)1ULL);
v___x_3415_ = lean_usize_add(v_i_3404_, v___x_3414_);
v___x_3416_ = lean_array_uset(v_bs_x27_3413_, v_i_3404_, v_val_3411_);
v_i_3404_ = v___x_3415_;
v_bs_3405_ = v___x_3416_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0___boxed(lean_object* v_sz_3418_, lean_object* v_i_3419_, lean_object* v_bs_3420_){
_start:
{
size_t v_sz_boxed_3421_; size_t v_i_boxed_3422_; lean_object* v_res_3423_; 
v_sz_boxed_3421_ = lean_unbox_usize(v_sz_3418_);
lean_dec(v_sz_3418_);
v_i_boxed_3422_ = lean_unbox_usize(v_i_3419_);
lean_dec(v_i_3419_);
v_res_3423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_boxed_3421_, v_i_boxed_3422_, v_bs_3420_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescListView_of(lean_object* v_stx_3424_){
_start:
{
lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3425_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__38));
lean_inc(v_stx_3424_);
v___x_3426_ = l_Lean_Syntax_isOfKind(v_stx_3424_, v___x_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec(v_stx_3424_);
v___x_3427_ = lean_box(0);
return v___x_3427_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v_items_3430_; size_t v_sz_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
v___x_3428_ = lean_unsigned_to_nat(0u);
v___x_3429_ = l_Lean_Syntax_getArg(v_stx_3424_, v___x_3428_);
v_items_3430_ = l_Lean_Syntax_getArgs(v___x_3429_);
lean_dec(v___x_3429_);
v_sz_3431_ = lean_array_size(v_items_3430_);
v___x_3432_ = ((size_t)0ULL);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_3431_, v___x_3432_, v_items_3430_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v___x_3434_; 
lean_dec(v_stx_3424_);
v___x_3434_ = lean_box(0);
return v___x_3434_;
}
else
{
lean_object* v_val_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3443_; 
v_val_3435_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3437_ = v___x_3433_;
v_isShared_3438_ = v_isSharedCheck_3443_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_val_3435_);
lean_dec(v___x_3433_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3443_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3439_, 0, v_stx_3424_);
lean_ctor_set(v___x_3439_, 1, v_val_3435_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3439_);
v___x_3441_ = v___x_3437_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockquoteView_of(lean_object* v_stx_3444_){
_start:
{
lean_object* v___x_3445_; uint8_t v___x_3446_; 
v___x_3445_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__41));
lean_inc(v_stx_3444_);
v___x_3446_ = l_Lean_Syntax_isOfKind(v_stx_3444_, v___x_3445_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
lean_dec(v_stx_3444_);
v___x_3447_ = lean_box(0);
return v___x_3447_;
}
else
{
lean_object* v___x_3448_; lean_object* v_gt_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v_bs_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3448_ = lean_unsigned_to_nat(0u);
v_gt_3449_ = l_Lean_Syntax_getArg(v_stx_3444_, v___x_3448_);
v___x_3450_ = lean_unsigned_to_nat(1u);
v___x_3451_ = l_Lean_Syntax_getArg(v_stx_3444_, v___x_3450_);
v_bs_3452_ = l_Lean_Syntax_getArgs(v___x_3451_);
lean_dec(v___x_3451_);
v___x_3453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3453_, 0, v_stx_3444_);
lean_ctor_set(v___x_3453_, 1, v_gt_3449_);
lean_ctor_set(v___x_3453_, 2, v_bs_3452_);
v___x_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
return v___x_3454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object* v_v_3455_){
_start:
{
lean_object* v_content_3456_; lean_object* v___x_3457_; 
v_content_3456_ = lean_ctor_get(v_v_3455_, 4);
v___x_3457_ = l_Lean_TSyntax_getVersoCodeBlock(v_content_3456_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock___boxed(lean_object* v_v_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_v_3458_);
lean_dec_ref(v_v_3458_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_of(lean_object* v_stx_3466_){
_start:
{
lean_object* v___x_3467_; uint8_t v___x_3468_; 
v___x_3467_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__36));
lean_inc(v_stx_3466_);
v___x_3468_ = l_Lean_Syntax_isOfKind(v_stx_3466_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; 
lean_dec(v_stx_3466_);
v___x_3469_ = lean_box(0);
return v___x_3469_;
}
else
{
lean_object* v___x_3470_; lean_object* v_openFence_3471_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v_name_3494_; lean_object* v_args_3495_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3470_ = lean_unsigned_to_nat(0u);
v_openFence_3471_ = l_Lean_Syntax_getArg(v_stx_3466_, v___x_3470_);
v___x_3508_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1));
lean_inc(v_openFence_3471_);
v___x_3509_ = l_Lean_Syntax_isOfKind(v_openFence_3471_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_dec(v_openFence_3471_);
lean_dec(v_stx_3466_);
v___x_3510_ = lean_box(0);
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; 
v___x_3511_ = lean_unsigned_to_nat(1u);
v___x_3512_ = l_Lean_Syntax_getArg(v_stx_3466_, v___x_3511_);
v___x_3513_ = l_Lean_Syntax_isNone(v___x_3512_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; uint8_t v___x_3515_; 
v___x_3514_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3512_);
v___x_3515_ = l_Lean_Syntax_matchesNull(v___x_3512_, v___x_3514_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; 
lean_dec(v___x_3512_);
lean_dec(v_openFence_3471_);
lean_dec(v_stx_3466_);
v___x_3516_ = lean_box(0);
return v___x_3516_;
}
else
{
lean_object* v_name_3517_; 
v_name_3517_ = l_Lean_Syntax_getArg(v___x_3512_, v___x_3470_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3523_; uint8_t v___x_3524_; 
v___x_3523_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_3517_);
v___x_3524_ = l_Lean_Syntax_isOfKind(v_name_3517_, v___x_3523_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; 
lean_dec(v_name_3517_);
lean_dec(v___x_3512_);
lean_dec(v_openFence_3471_);
lean_dec(v_stx_3466_);
v___x_3525_ = lean_box(0);
return v___x_3525_;
}
else
{
goto v___jp_3518_;
}
}
else
{
goto v___jp_3518_;
}
v___jp_3518_:
{
lean_object* v___x_3519_; lean_object* v_args_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3519_ = l_Lean_Syntax_getArg(v___x_3512_, v___x_3511_);
lean_dec(v___x_3512_);
v_args_3520_ = l_Lean_Syntax_getArgs(v___x_3519_);
lean_dec(v___x_3519_);
v___x_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3521_, 0, v_name_3517_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v_args_3520_);
v_name_3494_ = v___x_3521_;
v_args_3495_ = v___x_3522_;
goto v___jp_3493_;
}
}
}
else
{
lean_object* v___x_3526_; 
lean_dec(v___x_3512_);
v___x_3526_ = lean_box(0);
v_name_3494_ = v___x_3526_;
v_args_3495_ = v___x_3526_;
goto v___jp_3493_;
}
}
v___jp_3472_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3477_, 0, v_stx_3466_);
lean_ctor_set(v___x_3477_, 1, v_openFence_3471_);
lean_ctor_set(v___x_3477_, 2, v___y_3474_);
lean_ctor_set(v___x_3477_, 3, v___y_3476_);
lean_ctor_set(v___x_3477_, 4, v___y_3473_);
lean_ctor_set(v___x_3477_, 5, v___y_3475_);
v___x_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
return v___x_3478_;
}
v___jp_3479_:
{
if (lean_obj_tag(v___y_3481_) == 0)
{
lean_object* v___x_3484_; 
v___x_3484_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_codeLinesFrom___closed__0));
v___y_3473_ = v___y_3483_;
v___y_3474_ = v___y_3480_;
v___y_3475_ = v___y_3482_;
v___y_3476_ = v___x_3484_;
goto v___jp_3472_;
}
else
{
lean_object* v_val_3485_; 
v_val_3485_ = lean_ctor_get(v___y_3481_, 0);
lean_inc(v_val_3485_);
lean_dec_ref_known(v___y_3481_, 1);
v___y_3473_ = v___y_3483_;
v___y_3474_ = v___y_3480_;
v___y_3475_ = v___y_3482_;
v___y_3476_ = v_val_3485_;
goto v___jp_3472_;
}
}
v___jp_3486_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v___y_3490_);
v___x_3492_ = l_Lean_Syntax_setInfo(v___x_3491_, v___y_3488_);
v___y_3480_ = v___y_3487_;
v___y_3481_ = v___y_3489_;
v___y_3482_ = v___y_3490_;
v___y_3483_ = v___x_3492_;
goto v___jp_3479_;
}
v___jp_3493_:
{
lean_object* v___x_3496_; lean_object* v_s_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v___x_3496_ = lean_unsigned_to_nat(2u);
v_s_3497_ = l_Lean_Syntax_getArg(v_stx_3466_, v___x_3496_);
v___x_3498_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__1));
lean_inc(v_s_3497_);
v___x_3499_ = l_Lean_Syntax_isOfKind(v_s_3497_, v___x_3498_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; 
lean_dec(v_s_3497_);
lean_dec(v_args_3495_);
lean_dec(v_name_3494_);
lean_dec(v_openFence_3471_);
lean_dec(v_stx_3466_);
v___x_3500_ = lean_box(0);
return v___x_3500_;
}
else
{
lean_object* v___x_3501_; lean_object* v_closeFence_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3501_ = lean_unsigned_to_nat(3u);
v_closeFence_3502_ = l_Lean_Syntax_getArg(v_stx_3466_, v___x_3501_);
v___x_3503_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1));
lean_inc(v_closeFence_3502_);
v___x_3504_ = l_Lean_Syntax_isOfKind(v_closeFence_3502_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
lean_dec(v_closeFence_3502_);
lean_dec(v_s_3497_);
lean_dec(v_args_3495_);
lean_dec(v_name_3494_);
lean_dec(v_openFence_3471_);
lean_dec(v_stx_3466_);
v___x_3505_ = lean_box(0);
return v___x_3505_;
}
else
{
uint8_t v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = 0;
v___x_3507_ = l_Lean_Syntax_getPos_x3f(v_s_3497_, v___x_3506_);
if (lean_obj_tag(v___x_3507_) == 0)
{
v___y_3487_ = v_name_3494_;
v___y_3488_ = v_s_3497_;
v___y_3489_ = v_args_3495_;
v___y_3490_ = v_closeFence_3502_;
goto v___jp_3486_;
}
else
{
lean_dec_ref_known(v___x_3507_, 1);
if (v___x_3468_ == 0)
{
v___y_3487_ = v_name_3494_;
v___y_3488_ = v_s_3497_;
v___y_3489_ = v_args_3495_;
v___y_3490_ = v_closeFence_3502_;
goto v___jp_3486_;
}
else
{
v___y_3480_ = v_name_3494_;
v___y_3481_ = v_args_3495_;
v___y_3482_ = v_closeFence_3502_;
v___y_3483_ = v_s_3497_;
goto v___jp_3479_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DirectiveView_of(lean_object* v_stx_3527_){
_start:
{
lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3528_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__35));
lean_inc(v_stx_3527_);
v___x_3529_ = l_Lean_Syntax_isOfKind(v_stx_3527_, v___x_3528_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; 
lean_dec(v_stx_3527_);
v___x_3530_ = lean_box(0);
return v___x_3530_;
}
else
{
lean_object* v___x_3531_; lean_object* v_opener_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v___x_3531_ = lean_unsigned_to_nat(0u);
v_opener_3532_ = l_Lean_Syntax_getArg(v_stx_3527_, v___x_3531_);
v___x_3533_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1));
lean_inc(v_opener_3532_);
v___x_3534_ = l_Lean_Syntax_isOfKind(v_opener_3532_, v___x_3533_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3535_; 
lean_dec(v_opener_3532_);
lean_dec(v_stx_3527_);
v___x_3535_ = lean_box(0);
return v___x_3535_;
}
else
{
lean_object* v___x_3536_; lean_object* v_name_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v___x_3536_ = lean_unsigned_to_nat(1u);
v_name_3537_ = l_Lean_Syntax_getArg(v_stx_3527_, v___x_3536_);
v___x_3538_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_3537_);
v___x_3539_ = l_Lean_Syntax_isOfKind(v_name_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; 
lean_dec(v_name_3537_);
lean_dec(v_opener_3532_);
lean_dec(v_stx_3527_);
v___x_3540_ = lean_box(0);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v_closer_3542_; uint8_t v___x_3543_; 
v___x_3541_ = lean_unsigned_to_nat(4u);
v_closer_3542_ = l_Lean_Syntax_getArg(v_stx_3527_, v___x_3541_);
lean_inc(v_closer_3542_);
v___x_3543_ = l_Lean_Syntax_isOfKind(v_closer_3542_, v___x_3533_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; 
lean_dec(v_closer_3542_);
lean_dec(v_name_3537_);
lean_dec(v_opener_3532_);
lean_dec(v_stx_3527_);
v___x_3544_ = lean_box(0);
return v___x_3544_;
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v_bs_3549_; lean_object* v_args_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3545_ = lean_unsigned_to_nat(2u);
v___x_3546_ = l_Lean_Syntax_getArg(v_stx_3527_, v___x_3545_);
v___x_3547_ = lean_unsigned_to_nat(3u);
v___x_3548_ = l_Lean_Syntax_getArg(v_stx_3527_, v___x_3547_);
v_bs_3549_ = l_Lean_Syntax_getArgs(v___x_3548_);
lean_dec(v___x_3548_);
v_args_3550_ = l_Lean_Syntax_getArgs(v___x_3546_);
lean_dec(v___x_3546_);
v___x_3551_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3551_, 0, v_stx_3527_);
lean_ctor_set(v___x_3551_, 1, v_opener_3532_);
lean_ctor_set(v___x_3551_, 2, v_name_3537_);
lean_ctor_set(v___x_3551_, 3, v_args_3550_);
lean_ctor_set(v___x_3551_, 4, v_bs_3549_);
lean_ctor_set(v___x_3551_, 5, v_closer_3542_);
v___x_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
return v___x_3552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CommandView_of(lean_object* v_stx_3553_){
_start:
{
lean_object* v___x_3554_; uint8_t v___x_3555_; 
v___x_3554_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__34));
lean_inc(v_stx_3553_);
v___x_3555_ = l_Lean_Syntax_isOfKind(v_stx_3553_, v___x_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; 
lean_dec(v_stx_3553_);
v___x_3556_ = lean_box(0);
return v___x_3556_;
}
else
{
lean_object* v___x_3557_; lean_object* v_name_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3557_ = lean_unsigned_to_nat(1u);
v_name_3558_ = l_Lean_Syntax_getArg(v_stx_3553_, v___x_3557_);
v___x_3559_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_3558_);
v___x_3560_ = l_Lean_Syntax_isOfKind(v_name_3558_, v___x_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; 
lean_dec(v_name_3558_);
lean_dec(v_stx_3553_);
v___x_3561_ = lean_box(0);
return v___x_3561_;
}
else
{
lean_object* v___x_3562_; lean_object* v_braceOpen_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v_braceClose_3567_; lean_object* v_args_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3562_ = lean_unsigned_to_nat(0u);
v_braceOpen_3563_ = l_Lean_Syntax_getArg(v_stx_3553_, v___x_3562_);
v___x_3564_ = lean_unsigned_to_nat(2u);
v___x_3565_ = l_Lean_Syntax_getArg(v_stx_3553_, v___x_3564_);
v___x_3566_ = lean_unsigned_to_nat(3u);
v_braceClose_3567_ = l_Lean_Syntax_getArg(v_stx_3553_, v___x_3566_);
v_args_3568_ = l_Lean_Syntax_getArgs(v___x_3565_);
lean_dec(v___x_3565_);
v___x_3569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3569_, 0, v_stx_3553_);
lean_ctor_set(v___x_3569_, 1, v_braceOpen_3563_);
lean_ctor_set(v___x_3569_, 2, v_name_3558_);
lean_ctor_set(v___x_3569_, 3, v_args_3568_);
lean_ctor_set(v___x_3569_, 4, v_braceClose_3567_);
v___x_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
return v___x_3570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_HeaderView_of(lean_object* v_stx_3571_){
_start:
{
lean_object* v___x_3572_; uint8_t v___x_3573_; 
v___x_3572_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__31));
lean_inc(v_stx_3571_);
v___x_3573_ = l_Lean_Syntax_isOfKind(v_stx_3571_, v___x_3572_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; 
lean_dec(v_stx_3571_);
v___x_3574_ = lean_box(0);
return v___x_3574_;
}
else
{
lean_object* v___x_3575_; lean_object* v_marker_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3575_ = lean_unsigned_to_nat(0u);
v_marker_3576_ = l_Lean_Syntax_getArg(v_stx_3571_, v___x_3575_);
v___x_3577_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__33));
lean_inc(v_marker_3576_);
v___x_3578_ = l_Lean_Syntax_isOfKind(v_marker_3576_, v___x_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; 
lean_dec(v_marker_3576_);
lean_dec(v_stx_3571_);
v___x_3579_ = lean_box(0);
return v___x_3579_;
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v_content_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3580_ = lean_unsigned_to_nat(1u);
v___x_3581_ = l_Lean_Syntax_getArg(v_stx_3571_, v___x_3580_);
v_content_3582_ = l_Lean_Syntax_getArgs(v___x_3581_);
lean_dec(v___x_3581_);
v___x_3583_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_3576_);
v___x_3584_ = lean_string_length(v___x_3583_);
lean_dec_ref(v___x_3583_);
v___x_3585_ = lean_nat_sub(v___x_3584_, v___x_3580_);
v___x_3586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3586_, 0, v_stx_3571_);
lean_ctor_set(v___x_3586_, 1, v_marker_3576_);
lean_ctor_set(v___x_3586_, 2, v___x_3585_);
lean_ctor_set(v___x_3586_, 3, v_content_3582_);
v___x_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
return v___x_3587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName(lean_object* v_v_3588_){
_start:
{
lean_object* v_name_3589_; lean_object* v___x_3590_; 
v_name_3589_ = lean_ctor_get(v_v_3588_, 2);
v___x_3590_ = l_Lean_TSyntax_getVersoRefName(v_name_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName___boxed(lean_object* v_v_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Doc_LinkRefView_getName(v_v_3591_);
lean_dec_ref(v_v_3591_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object* v_v_3593_){
_start:
{
lean_object* v_url_3594_; lean_object* v___x_3595_; 
v_url_3594_ = lean_ctor_get(v_v_3593_, 4);
v___x_3595_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_url_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl___boxed(lean_object* v_v_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_Doc_LinkRefView_getUrl(v_v_3596_);
lean_dec_ref(v_v_3596_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_of(lean_object* v_stx_3604_){
_start:
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__30));
lean_inc(v_stx_3604_);
v___x_3606_ = l_Lean_Syntax_isOfKind(v_stx_3604_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; 
lean_dec(v_stx_3604_);
v___x_3607_ = lean_box(0);
return v___x_3607_;
}
else
{
lean_object* v___x_3608_; lean_object* v_name_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v___x_3608_ = lean_unsigned_to_nat(1u);
v_name_3609_ = l_Lean_Syntax_getArg(v_stx_3604_, v___x_3608_);
v___x_3610_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__1));
lean_inc(v_name_3609_);
v___x_3611_ = l_Lean_Syntax_isOfKind(v_name_3609_, v___x_3610_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; 
lean_dec(v_name_3609_);
lean_dec(v_stx_3604_);
v___x_3612_ = lean_box(0);
return v___x_3612_;
}
else
{
lean_object* v___x_3613_; lean_object* v_url_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; 
v___x_3613_ = lean_unsigned_to_nat(3u);
v_url_3614_ = l_Lean_Syntax_getArg(v_stx_3604_, v___x_3613_);
v___x_3615_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__1));
lean_inc(v_url_3614_);
v___x_3616_ = l_Lean_Syntax_isOfKind(v_url_3614_, v___x_3615_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; 
lean_dec(v_url_3614_);
lean_dec(v_name_3609_);
lean_dec(v_stx_3604_);
v___x_3617_ = lean_box(0);
return v___x_3617_;
}
else
{
lean_object* v___x_3618_; lean_object* v_opener_3619_; lean_object* v___x_3620_; lean_object* v_closer_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3618_ = lean_unsigned_to_nat(0u);
v_opener_3619_ = l_Lean_Syntax_getArg(v_stx_3604_, v___x_3618_);
v___x_3620_ = lean_unsigned_to_nat(2u);
v_closer_3621_ = l_Lean_Syntax_getArg(v_stx_3604_, v___x_3620_);
v___x_3622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3622_, 0, v_stx_3604_);
lean_ctor_set(v___x_3622_, 1, v_opener_3619_);
lean_ctor_set(v___x_3622_, 2, v_name_3609_);
lean_ctor_set(v___x_3622_, 3, v_closer_3621_);
lean_ctor_set(v___x_3622_, 4, v_url_3614_);
v___x_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
return v___x_3623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object* v_v_3624_){
_start:
{
lean_object* v_name_3625_; lean_object* v___x_3626_; 
v_name_3625_ = lean_ctor_get(v_v_3624_, 2);
v___x_3626_ = l_Lean_TSyntax_getVersoRefName(v_name_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName___boxed(lean_object* v_v_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Doc_FootnoteRefView_getName(v_v_3627_);
lean_dec_ref(v_v_3627_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_of(lean_object* v_stx_3629_){
_start:
{
lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3630_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__29));
lean_inc(v_stx_3629_);
v___x_3631_ = l_Lean_Syntax_isOfKind(v_stx_3629_, v___x_3630_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; 
lean_dec(v_stx_3629_);
v___x_3632_ = lean_box(0);
return v___x_3632_;
}
else
{
lean_object* v___x_3633_; lean_object* v_name_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v___x_3633_ = lean_unsigned_to_nat(1u);
v_name_3634_ = l_Lean_Syntax_getArg(v_stx_3629_, v___x_3633_);
v___x_3635_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__1));
lean_inc(v_name_3634_);
v___x_3636_ = l_Lean_Syntax_isOfKind(v_name_3634_, v___x_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; 
lean_dec(v_name_3634_);
lean_dec(v_stx_3629_);
v___x_3637_ = lean_box(0);
return v___x_3637_;
}
else
{
lean_object* v___x_3638_; lean_object* v_opener_3639_; lean_object* v___x_3640_; lean_object* v_closer_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v_content_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3638_ = lean_unsigned_to_nat(0u);
v_opener_3639_ = l_Lean_Syntax_getArg(v_stx_3629_, v___x_3638_);
v___x_3640_ = lean_unsigned_to_nat(2u);
v_closer_3641_ = l_Lean_Syntax_getArg(v_stx_3629_, v___x_3640_);
v___x_3642_ = lean_unsigned_to_nat(3u);
v___x_3643_ = l_Lean_Syntax_getArg(v_stx_3629_, v___x_3642_);
v_content_3644_ = l_Lean_Syntax_getArgs(v___x_3643_);
lean_dec(v___x_3643_);
v___x_3645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3645_, 0, v_stx_3629_);
lean_ctor_set(v___x_3645_, 1, v_opener_3639_);
lean_ctor_set(v___x_3645_, 2, v_name_3634_);
lean_ctor_set(v___x_3645_, 3, v_closer_3641_);
lean_ctor_set(v___x_3645_, 4, v_content_3644_);
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
return v___x_3646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(size_t v_sz_3647_, size_t v_i_3648_, lean_object* v_bs_3649_){
_start:
{
uint8_t v___x_3650_; 
v___x_3650_ = lean_usize_dec_lt(v_i_3648_, v_sz_3647_);
if (v___x_3650_ == 0)
{
return v_bs_3649_;
}
else
{
lean_object* v_v_3651_; lean_object* v___x_3652_; lean_object* v_bs_x27_3653_; size_t v___x_3654_; size_t v___x_3655_; lean_object* v___x_3656_; 
v_v_3651_ = lean_array_uget(v_bs_3649_, v_i_3648_);
v___x_3652_ = lean_unsigned_to_nat(0u);
v_bs_x27_3653_ = lean_array_uset(v_bs_3649_, v_i_3648_, v___x_3652_);
v___x_3654_ = ((size_t)1ULL);
v___x_3655_ = lean_usize_add(v_i_3648_, v___x_3654_);
v___x_3656_ = lean_array_uset(v_bs_x27_3653_, v_i_3648_, v_v_3651_);
v_i_3648_ = v___x_3655_;
v_bs_3649_ = v___x_3656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0___boxed(lean_object* v_sz_3658_, lean_object* v_i_3659_, lean_object* v_bs_3660_){
_start:
{
size_t v_sz_boxed_3661_; size_t v_i_boxed_3662_; lean_object* v_res_3663_; 
v_sz_boxed_3661_ = lean_unbox_usize(v_sz_3658_);
lean_dec(v_sz_3658_);
v_i_boxed_3662_ = lean_unbox_usize(v_i_3659_);
lean_dec(v_i_3659_);
v_res_3663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_boxed_3661_, v_i_boxed_3662_, v_bs_3660_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields(lean_object* v_v_3664_){
_start:
{
lean_object* v_contents_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; size_t v_sz_3669_; size_t v___x_3670_; lean_object* v___x_3671_; 
v_contents_3665_ = lean_ctor_get(v_v_3664_, 2);
v___x_3666_ = lean_unsigned_to_nat(0u);
v___x_3667_ = l_Lean_Syntax_getArg(v_contents_3665_, v___x_3666_);
v___x_3668_ = l_Lean_Syntax_getSepArgs(v___x_3667_);
lean_dec(v___x_3667_);
v_sz_3669_ = lean_array_size(v___x_3668_);
v___x_3670_ = ((size_t)0ULL);
v___x_3671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_3669_, v___x_3670_, v___x_3668_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields___boxed(lean_object* v_v_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_Doc_MetadataView_fields(v_v_3672_);
lean_dec_ref(v_v_3672_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_of(lean_object* v_stx_3674_){
_start:
{
lean_object* v___x_3675_; uint8_t v___x_3676_; 
v___x_3675_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__28));
lean_inc(v_stx_3674_);
v___x_3676_ = l_Lean_Syntax_isOfKind(v_stx_3674_, v___x_3675_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; 
lean_dec(v_stx_3674_);
v___x_3677_ = lean_box(0);
return v___x_3677_;
}
else
{
lean_object* v___x_3678_; lean_object* v_contents_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3678_ = lean_unsigned_to_nat(1u);
v_contents_3679_ = l_Lean_Syntax_getArg(v_stx_3674_, v___x_3678_);
v___x_3680_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__26));
lean_inc(v_contents_3679_);
v___x_3681_ = l_Lean_Syntax_isOfKind(v_contents_3679_, v___x_3680_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; 
lean_dec(v_contents_3679_);
lean_dec(v_stx_3674_);
v___x_3682_ = lean_box(0);
return v___x_3682_;
}
else
{
lean_object* v___x_3683_; lean_object* v_opener_3684_; lean_object* v___x_3685_; lean_object* v_closer_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3683_ = lean_unsigned_to_nat(0u);
v_opener_3684_ = l_Lean_Syntax_getArg(v_stx_3674_, v___x_3683_);
v___x_3685_ = lean_unsigned_to_nat(2u);
v_closer_3686_ = l_Lean_Syntax_getArg(v_stx_3674_, v___x_3685_);
v___x_3687_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3687_, 0, v_stx_3674_);
lean_ctor_set(v___x_3687_, 1, v_opener_3684_);
lean_ctor_set(v___x_3687_, 2, v_contents_3679_);
lean_ctor_set(v___x_3687_, 3, v_closer_3686_);
v___x_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
return v___x_3688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx(lean_object* v_x_3689_){
_start:
{
switch(lean_obj_tag(v_x_3689_))
{
case 0:
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_unsigned_to_nat(0u);
return v___x_3690_;
}
case 1:
{
lean_object* v___x_3691_; 
v___x_3691_ = lean_unsigned_to_nat(1u);
return v___x_3691_;
}
case 2:
{
lean_object* v___x_3692_; 
v___x_3692_ = lean_unsigned_to_nat(2u);
return v___x_3692_;
}
case 3:
{
lean_object* v___x_3693_; 
v___x_3693_ = lean_unsigned_to_nat(3u);
return v___x_3693_;
}
case 4:
{
lean_object* v___x_3694_; 
v___x_3694_ = lean_unsigned_to_nat(4u);
return v___x_3694_;
}
case 5:
{
lean_object* v___x_3695_; 
v___x_3695_ = lean_unsigned_to_nat(5u);
return v___x_3695_;
}
case 6:
{
lean_object* v___x_3696_; 
v___x_3696_ = lean_unsigned_to_nat(6u);
return v___x_3696_;
}
case 7:
{
lean_object* v___x_3697_; 
v___x_3697_ = lean_unsigned_to_nat(7u);
return v___x_3697_;
}
case 8:
{
lean_object* v___x_3698_; 
v___x_3698_ = lean_unsigned_to_nat(8u);
return v___x_3698_;
}
case 9:
{
lean_object* v___x_3699_; 
v___x_3699_ = lean_unsigned_to_nat(9u);
return v___x_3699_;
}
case 10:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_unsigned_to_nat(10u);
return v___x_3700_;
}
default: 
{
lean_object* v___x_3701_; 
v___x_3701_ = lean_unsigned_to_nat(11u);
return v___x_3701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___boxed(lean_object* v_x_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_Doc_BlockView_ctorIdx(v_x_3702_);
lean_dec_ref(v_x_3702_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___redArg(lean_object* v_t_3704_, lean_object* v_k_3705_){
_start:
{
lean_object* v_view_3706_; lean_object* v___x_3707_; 
v_view_3706_ = lean_ctor_get(v_t_3704_, 0);
lean_inc_ref(v_view_3706_);
lean_dec_ref(v_t_3704_);
v___x_3707_ = lean_apply_1(v_k_3705_, v_view_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim(lean_object* v_motive_3708_, lean_object* v_ctorIdx_3709_, lean_object* v_t_3710_, lean_object* v_h_3711_, lean_object* v_k_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3710_, v_k_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___boxed(lean_object* v_motive_3714_, lean_object* v_ctorIdx_3715_, lean_object* v_t_3716_, lean_object* v_h_3717_, lean_object* v_k_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_Doc_BlockView_ctorElim(v_motive_3714_, v_ctorIdx_3715_, v_t_3716_, v_h_3717_, v_k_3718_);
lean_dec(v_ctorIdx_3715_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim___redArg(lean_object* v_t_3720_, lean_object* v_para_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3720_, v_para_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim(lean_object* v_motive_3723_, lean_object* v_t_3724_, lean_object* v_h_3725_, lean_object* v_para_3726_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3724_, v_para_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim___redArg(lean_object* v_t_3728_, lean_object* v_ul_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3728_, v_ul_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim(lean_object* v_motive_3731_, lean_object* v_t_3732_, lean_object* v_h_3733_, lean_object* v_ul_3734_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3732_, v_ul_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim___redArg(lean_object* v_t_3736_, lean_object* v_ol_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3736_, v_ol_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim(lean_object* v_motive_3739_, lean_object* v_t_3740_, lean_object* v_h_3741_, lean_object* v_ol_3742_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3740_, v_ol_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim___redArg(lean_object* v_t_3744_, lean_object* v_dl_3745_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3744_, v_dl_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim(lean_object* v_motive_3747_, lean_object* v_t_3748_, lean_object* v_h_3749_, lean_object* v_dl_3750_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3748_, v_dl_3750_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim___redArg(lean_object* v_t_3752_, lean_object* v_blockquote_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3752_, v_blockquote_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim(lean_object* v_motive_3755_, lean_object* v_t_3756_, lean_object* v_h_3757_, lean_object* v_blockquote_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3756_, v_blockquote_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim___redArg(lean_object* v_t_3760_, lean_object* v_codeblock_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3760_, v_codeblock_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim(lean_object* v_motive_3763_, lean_object* v_t_3764_, lean_object* v_h_3765_, lean_object* v_codeblock_3766_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3764_, v_codeblock_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim___redArg(lean_object* v_t_3768_, lean_object* v_directive_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3768_, v_directive_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim(lean_object* v_motive_3771_, lean_object* v_t_3772_, lean_object* v_h_3773_, lean_object* v_directive_3774_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3772_, v_directive_3774_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim___redArg(lean_object* v_t_3776_, lean_object* v_command_3777_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3776_, v_command_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim(lean_object* v_motive_3779_, lean_object* v_t_3780_, lean_object* v_h_3781_, lean_object* v_command_3782_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3780_, v_command_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim___redArg(lean_object* v_t_3784_, lean_object* v_header_3785_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3784_, v_header_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim(lean_object* v_motive_3787_, lean_object* v_t_3788_, lean_object* v_h_3789_, lean_object* v_header_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3788_, v_header_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim___redArg(lean_object* v_t_3792_, lean_object* v_linkRef_3793_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3792_, v_linkRef_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim(lean_object* v_motive_3795_, lean_object* v_t_3796_, lean_object* v_h_3797_, lean_object* v_linkRef_3798_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3796_, v_linkRef_3798_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim___redArg(lean_object* v_t_3800_, lean_object* v_footnoteRef_3801_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3800_, v_footnoteRef_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim(lean_object* v_motive_3803_, lean_object* v_t_3804_, lean_object* v_h_3805_, lean_object* v_footnoteRef_3806_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3804_, v_footnoteRef_3806_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim___redArg(lean_object* v_t_3808_, lean_object* v_metadata_3809_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3808_, v_metadata_3809_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim(lean_object* v_motive_3811_, lean_object* v_t_3812_, lean_object* v_h_3813_, lean_object* v_metadata_3814_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3812_, v_metadata_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeParaViewBlockView___lam__0(lean_object* v_view_3820_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3821_, 0, v_view_3820_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0(lean_object* v_view_3824_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3825_, 0, v_view_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0(lean_object* v_view_3828_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3829_, 0, v_view_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDescListViewBlockView___lam__0(lean_object* v_view_3832_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3833_, 0, v_view_3832_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0(lean_object* v_view_3836_){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3837_, 0, v_view_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0(lean_object* v_view_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3841_, 0, v_view_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0(lean_object* v_view_3844_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3845_, 0, v_view_3844_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCommandViewBlockView___lam__0(lean_object* v_view_3848_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3849_, 0, v_view_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___lam__0(lean_object* v_view_3852_){
_start:
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_view_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0(lean_object* v_view_3856_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3857_, 0, v_view_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0(lean_object* v_view_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3861_, 0, v_view_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___lam__0(lean_object* v_view_3864_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_3865_, 0, v_view_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx(lean_object* v_x_3868_){
_start:
{
lean_object* v_view_3869_; lean_object* v_stx_3870_; 
v_view_3869_ = lean_ctor_get(v_x_3868_, 0);
v_stx_3870_ = lean_ctor_get(v_view_3869_, 0);
lean_inc(v_stx_3870_);
return v_stx_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx___boxed(lean_object* v_x_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_Doc_BlockView_stx(v_x_3871_);
lean_dec_ref(v_x_3871_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_of(lean_object* v_stx_3873_){
_start:
{
lean_object* v___x_3874_; 
lean_inc(v_stx_3873_);
v___x_3874_ = l_Lean_Doc_ParaView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v___x_3875_; 
lean_inc(v_stx_3873_);
v___x_3875_ = l_Lean_Doc_UnorderedListView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v___x_3876_; 
lean_inc(v_stx_3873_);
v___x_3876_ = l_Lean_Doc_OrderedListView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v___x_3877_; 
lean_inc(v_stx_3873_);
v___x_3877_ = l_Lean_Doc_DescListView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v___x_3878_; 
lean_inc(v_stx_3873_);
v___x_3878_ = l_Lean_Doc_BlockquoteView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v___x_3879_; 
lean_inc(v_stx_3873_);
v___x_3879_ = l_Lean_Doc_CodeBlockView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v___x_3880_; 
lean_inc(v_stx_3873_);
v___x_3880_ = l_Lean_Doc_DirectiveView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v___x_3881_; 
lean_inc(v_stx_3873_);
v___x_3881_ = l_Lean_Doc_CommandView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v___x_3882_; 
lean_inc(v_stx_3873_);
v___x_3882_ = l_Lean_Doc_HeaderView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v___x_3883_; 
lean_inc(v_stx_3873_);
v___x_3883_ = l_Lean_Doc_LinkRefView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v___x_3884_; 
lean_inc(v_stx_3873_);
v___x_3884_ = l_Lean_Doc_FootnoteRefView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_Doc_MetadataView_of(v_stx_3873_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_box(0);
return v___x_3886_;
}
else
{
lean_object* v_val_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3895_; 
v_val_3887_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3889_ = v___x_3885_;
v_isShared_3890_ = v_isSharedCheck_3895_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_val_3887_);
lean_dec(v___x_3885_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3895_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3891_; lean_object* v___x_3893_; 
v___x_3891_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_3891_, 0, v_val_3887_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3891_);
v___x_3893_ = v___x_3889_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_object* v_val_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3904_; 
lean_dec(v_stx_3873_);
v_val_3896_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3898_ = v___x_3884_;
v_isShared_3899_ = v_isSharedCheck_3904_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_val_3896_);
lean_dec(v___x_3884_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3904_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3900_; lean_object* v___x_3902_; 
v___x_3900_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3900_, 0, v_val_3896_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v___x_3900_);
v___x_3902_ = v___x_3898_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
else
{
lean_object* v_val_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v_stx_3873_);
v_val_3905_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3907_ = v___x_3883_;
v_isShared_3908_ = v_isSharedCheck_3913_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_val_3905_);
lean_dec(v___x_3883_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3913_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3909_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3909_, 0, v_val_3905_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3909_);
v___x_3911_ = v___x_3907_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v_val_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v_stx_3873_);
v_val_3914_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3916_ = v___x_3882_;
v_isShared_3917_ = v_isSharedCheck_3922_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_val_3914_);
lean_dec(v___x_3882_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3922_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3918_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3918_, 0, v_val_3914_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3918_);
v___x_3920_ = v___x_3916_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
else
{
lean_object* v_val_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v_stx_3873_);
v_val_3923_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3925_ = v___x_3881_;
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_val_3923_);
lean_dec(v___x_3881_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3927_, 0, v_val_3923_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3927_);
v___x_3929_ = v___x_3925_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v_val_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3940_; 
lean_dec(v_stx_3873_);
v_val_3932_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3934_ = v___x_3880_;
v_isShared_3935_ = v_isSharedCheck_3940_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_val_3932_);
lean_dec(v___x_3880_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3940_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3936_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3936_, 0, v_val_3932_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 0, v___x_3936_);
v___x_3938_ = v___x_3934_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3936_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
else
{
lean_object* v_val_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3949_; 
lean_dec(v_stx_3873_);
v_val_3941_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3943_ = v___x_3879_;
v_isShared_3944_ = v_isSharedCheck_3949_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_val_3941_);
lean_dec(v___x_3879_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3949_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3945_; lean_object* v___x_3947_; 
v___x_3945_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3945_, 0, v_val_3941_);
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 0, v___x_3945_);
v___x_3947_ = v___x_3943_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
else
{
lean_object* v_val_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3958_; 
lean_dec(v_stx_3873_);
v_val_3950_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3952_ = v___x_3878_;
v_isShared_3953_ = v_isSharedCheck_3958_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_val_3950_);
lean_dec(v___x_3878_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3958_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; lean_object* v___x_3956_; 
v___x_3954_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3954_, 0, v_val_3950_);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v___x_3954_);
v___x_3956_ = v___x_3952_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
else
{
lean_object* v_val_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3967_; 
lean_dec(v_stx_3873_);
v_val_3959_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3961_ = v___x_3877_;
v_isShared_3962_ = v_isSharedCheck_3967_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_val_3959_);
lean_dec(v___x_3877_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3967_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3963_; lean_object* v___x_3965_; 
v___x_3963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3963_, 0, v_val_3959_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 0, v___x_3963_);
v___x_3965_ = v___x_3961_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
else
{
lean_object* v_val_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3976_; 
lean_dec(v_stx_3873_);
v_val_3968_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3970_ = v___x_3876_;
v_isShared_3971_ = v_isSharedCheck_3976_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_val_3968_);
lean_dec(v___x_3876_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3976_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___x_3972_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3972_, 0, v_val_3968_);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v___x_3972_);
v___x_3974_ = v___x_3970_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
else
{
lean_object* v_val_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3985_; 
lean_dec(v_stx_3873_);
v_val_3977_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3979_ = v___x_3875_;
v_isShared_3980_ = v_isSharedCheck_3985_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_val_3977_);
lean_dec(v___x_3875_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3985_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3981_; lean_object* v___x_3983_; 
v___x_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3981_, 0, v_val_3977_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 0, v___x_3981_);
v___x_3983_ = v___x_3979_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
else
{
lean_object* v_val_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3994_; 
lean_dec(v_stx_3873_);
v_val_3986_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3988_ = v___x_3874_;
v_isShared_3989_ = v_isSharedCheck_3994_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_val_3986_);
lean_dec(v___x_3874_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3994_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v_val_3986_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 0, v___x_3990_);
v___x_3992_ = v___x_3988_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoInline_view(lean_object* v_stx_3995_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Lean_Doc_InlineView_of(v_stx_3995_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v___x_3997_; 
v___x_3997_ = ((lean_object*)(l_Lean_Doc_instInhabitedInlineView_default));
return v___x_3997_;
}
else
{
lean_object* v_val_3998_; 
v_val_3998_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_val_3998_);
lean_dec_ref_known(v___x_3996_, 1);
return v_val_3998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoBlock_view(lean_object* v_stx_3999_){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_Lean_Doc_BlockView_of(v_stx_3999_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v___x_4001_; 
v___x_4001_ = ((lean_object*)(l_Lean_Doc_instInhabitedBlockView_default));
return v___x_4001_;
}
else
{
lean_object* v_val_4002_; 
v_val_4002_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_val_4002_);
lean_dec_ref_known(v___x_4000_, 1);
return v_val_4002_;
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
l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1 = _init_l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1);
l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1 = _init_l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1);
l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1 = _init_l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1);
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
