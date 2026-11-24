// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.NotationExtra
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Lean.Parser.Term meta import Init.NotationExtra meta import Init.Notation import Lean.Fmt.FmtM.CommonFormatters import Init.Data import Init.While import Lean.Fmt.Util.Basic
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_infixFmtAttribute;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Fmt_TaggedDoc_nl;
lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_quantifierFmtAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAltsTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_space;
lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnOverflow(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclarationSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_sepFill(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithDeclModifiers(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtArrayLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_sepLines(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__0_value)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtTermMatches_spec__0___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTermMatches___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtTermMatches___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtTermMatches___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "term_Matches_|"};
static const lean_object* l_Lean_Fmt_fmtTermMatches___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermMatches___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermMatches___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 90, 108, 139, 70, 136, 238, 145)}};
static const lean_object* l_Lean_Fmt_fmtTermMatches___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__2_value;
static const lean_closure_object l_Lean_Fmt_fmtTermMatches___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtTermMatches___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtTermMatches___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__3_value;
static lean_once_cell_t l_Lean_Fmt_fmtTermMatches___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTermMatches___closed__4;
static const lean_closure_object l_Lean_Fmt_fmtTermMatches___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_nested, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtTermMatches___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__5_value;
static lean_once_cell_t l_Lean_Fmt_fmtTermMatches___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTermMatches___closed__6;
static lean_once_cell_t l_Lean_Fmt_fmtTermMatches___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTermMatches___closed__7;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtTermMatches_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtTermMatches"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 253, 249, 123, 147, 209, 144, 242)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unbracketedExplicitBinders"};
static const lean_object* l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 220, 119, 82, 242, 112, 119, 200)}};
static const lean_object* l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnbracketedExplicitBinders(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnbracketedExplicitBinders___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "fmtUnbracketedExplicitBinders"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 212, 153, 225, 208, 198, 136, 97)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBracketedExplicitBinders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "bracketedExplicitBinders"};
static const lean_object* l_Lean_Fmt_fmtBracketedExplicitBinders___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBracketedExplicitBinders___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBracketedExplicitBinders___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 65, 7, 186, 44, 89, 152, 79)}};
static const lean_object* l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBracketedExplicitBinders(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBracketedExplicitBinders___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "fmtBracketedExplicitBinders"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 138, 53, 123, 45, 130, 67, 91)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_explicitBindersToGroup_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_explicitBindersToGroup_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_explicitBindersToGroup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "explicitBinders"};
static const lean_object* l_Lean_Fmt_explicitBindersToGroup___closed__0 = (const lean_object*)&l_Lean_Fmt_explicitBindersToGroup___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_explicitBindersToGroup___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_explicitBindersToGroup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_explicitBindersToGroup___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_explicitBindersToGroup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 149, 127, 13, 202, 239, 226, 94)}};
static const lean_object* l_Lean_Fmt_explicitBindersToGroup___closed__1 = (const lean_object*)&l_Lean_Fmt_explicitBindersToGroup___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_explicitBindersToGroup(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term∃_,_"};
static const lean_object* l_Lean_Fmt_fmtExists___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExists___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExists___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 105, 219, 112, 166, 139, 167, 161)}};
static const lean_object* l_Lean_Fmt_fmtExists___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExists___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExists(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtExists"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 135, 2, 117, 224, 164, 198, 125)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExistsKeyword___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "termExists_,_"};
static const lean_object* l_Lean_Fmt_fmtExistsKeyword___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExistsKeyword___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtExistsKeyword___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExistsKeyword___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 28, 246, 22, 86, 216, 86, 26)}};
static const lean_object* l_Lean_Fmt_fmtExistsKeyword___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExistsKeyword___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExistsKeyword(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtExistsKeyword"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 40, 7, 182, 83, 236, 253, 158)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSigma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 8, .m_data = "termΣ_,_"};
static const lean_object* l_Lean_Fmt_fmtSigma___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSigma___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSigma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSigma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 61, 86, 48, 13, 47, 85, 120)}};
static const lean_object* l_Lean_Fmt_fmtSigma___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSigma___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSigma(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtSigma"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 96, 36, 12, 158, 60, 77, 110)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPSigma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 9, .m_data = "termΣ'_,_"};
static const lean_object* l_Lean_Fmt_fmtPSigma___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPSigma___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtPSigma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPSigma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 244, 129, 9, 43, 224, 237, 22)}};
static const lean_object* l_Lean_Fmt_fmtPSigma___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPSigma___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPSigma(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtPSigma"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 91, 118, 44, 0, 181, 49, 77)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtTimes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtTimes___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTimes___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTimes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTimes___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtTimes___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTimes___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtTimes___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 9, .m_data = "term_×__1"};
static const lean_object* l_Lean_Fmt_fmtTimes___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTimes___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtTimes___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTimes___closed__2_value),LEAN_SCALAR_PTR_LITERAL(114, 66, 226, 190, 84, 185, 148, 180)}};
static const lean_object* l_Lean_Fmt_fmtTimes___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTimes___closed__3_value;
static lean_once_cell_t l_Lean_Fmt_fmtTimes___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTimes___closed__4;
static lean_once_cell_t l_Lean_Fmt_fmtTimes___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTimes___closed__5;
static lean_once_cell_t l_Lean_Fmt_fmtTimes___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTimes___closed__6;
static lean_once_cell_t l_Lean_Fmt_fmtTimes___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTimes___closed__7;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimes;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 7, .m_data = "term_×_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 89, 233, 57, 172, 127, 134, 63)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtTimes"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(20, 122, 254, 196, 36, 189, 208, 115)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtSigmaTimes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtSigmaTimes___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSigmaTimes___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSigmaTimes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSigmaTimes___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtSigmaTimes___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSigmaTimes___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtSigmaTimes___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSigmaTimes___closed__2;
static lean_once_cell_t l_Lean_Fmt_fmtSigmaTimes___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSigmaTimes___closed__3;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSigmaTimes;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtSigmaTimes"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 94, 81, 110, 130, 140, 105, 55)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTimes_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 10, .m_data = "term_×'__1"};
static const lean_object* l_Lean_Fmt_fmtTimes_x27___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTimes_x27___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTimes_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTimes_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 58, 119, 129, 26, 229, 143, 92)}};
static const lean_object* l_Lean_Fmt_fmtTimes_x27___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTimes_x27___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtTimes_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTimes_x27___closed__2;
static lean_once_cell_t l_Lean_Fmt_fmtTimes_x27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTimes_x27___closed__3;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimes_x27;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 8, .m_data = "term_×'_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 48, 59, 85, 121, 154, 128, 216)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtTimes'"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(200, 116, 254, 47, 45, 23, 6, 224)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_fmtPSigmaTimes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtPSigmaTimes___closed__0;
static lean_once_cell_t l_Lean_Fmt_fmtPSigmaTimes___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtPSigmaTimes___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPSigmaTimes;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtPSigmaTimes"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 156, 230, 70, 19, 67, 219, 236)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSetNotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term{_}"};
static const lean_object* l_Lean_Fmt_fmtSetNotation___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSetNotation___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSetNotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSetNotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 26, 220, 95, 138, 254, 219, 101)}};
static const lean_object* l_Lean_Fmt_fmtSetNotation___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSetNotation___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSetNotation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSetNotation___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtSetNotation"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 161, 159, 170, 45, 15, 108, 58)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtUnifConstraint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtUnifConstraint___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtUnifConstraint___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtUnifConstraint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnifConstraint___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtUnifConstraint___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtUnifConstraint___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtUnifConstraint___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtUnifConstraint___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnifConstraint;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "unifConstraint"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 40, 39, 182, 219, 40, 214, 56)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtUnifConstraint"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 238, 168, 235, 193, 135, 71, 253)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unifConstraintElem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 160, 61, 144, 137, 134, 194, 47)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtUnifHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 34, .m_data = "command__Unif_hint____Where_|_-⊢__"};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 81, 240, 79, 209, 199, 153, 255)}};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtUnifHint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtUnifHint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtUnifHint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtUnifHint___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtUnifHint___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__7_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__8_value;
static const lean_string_object l_Lean_Fmt_fmtUnifHint___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__9_value;
static const lean_string_object l_Lean_Fmt_fmtUnifHint___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__10_value;
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__11_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__11_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__9_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnifHint___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__11_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__10_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtUnifHint___closed__11 = (const lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnifHint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnifHint___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtUnifHint"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 170, 27, 183, 217, 207, 95, 254)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtClassAbbrev___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "classAbbrev"};
static const lean_object* l_Lean_Fmt_fmtClassAbbrev___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__9_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 112, 139, 141, 120, 66, 29, 3)}};
static const lean_object* l_Lean_Fmt_fmtClassAbbrev___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtClassAbbrev___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Fmt_fmtClassAbbrev___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__9_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Fmt_fmtClassAbbrev___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtClassAbbrev___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Fmt_fmtClassAbbrev___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__9_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtClassAbbrev___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Fmt_fmtClassAbbrev___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtClassAbbrev___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtClassAbbrev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtClassAbbrev___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtClassAbbrev"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 250, 97, 155, 144, 109, 67, 139)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtFunext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "tacticFunext___"};
static const lean_object* l_Lean_Fmt_fmtFunext___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtFunext___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtFunext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtFunext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 155, 131, 24, 73, 26, 166, 240)}};
static const lean_object* l_Lean_Fmt_fmtFunext___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtFunext___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFunext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFunext___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtFunext"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 123, 39, 44, 141, 185, 110, 93)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCdotTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l_Lean_Fmt_fmtCdotTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCdotTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCdotTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 151, 138, 49, 249, 18, 254, 242)}};
static const lean_object* l_Lean_Fmt_fmtCdotTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtCdotTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l_Lean_Fmt_fmtCdotTactic___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtCdotTactic___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCdotTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l_Lean_Fmt_fmtCdotTactic___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtCdotTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtCdotTactic___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtCdotTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Fmt_fmtCdotTactic___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtCdotTactic___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCdotTactic___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtUnifHint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCdotTactic___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtCdotTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Fmt_fmtCdotTactic___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtCdotTactic___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCdotTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCdotTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtCdotTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 119, 198, 12, 175, 9, 227, 96)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSolve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "solveTactic"};
static const lean_object* l_Lean_Fmt_fmtSolve___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSolve___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSolve___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSolve___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSolve___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSolve___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 93, 240, 221, 8, 79, 216, 244)}};
static const lean_object* l_Lean_Fmt_fmtSolve___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSolve___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSolve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSolve___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtSolve"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 107, 45, 234, 188, 59, 6, 115)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStepLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStepLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCalcFirstStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "calcFirstStep"};
static const lean_object* l_Lean_Fmt_fmtCalcFirstStep___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCalcFirstStep___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCalcFirstStep___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCalcFirstStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCalcFirstStep___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCalcFirstStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 79, 246, 49, 58, 153, 94, 105)}};
static const lean_object* l_Lean_Fmt_fmtCalcFirstStep___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCalcFirstStep___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcFirstStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcFirstStep___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtCalcFirstStep"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 195, 231, 117, 163, 183, 214, 96)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCalcStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "calcStep"};
static const lean_object* l_Lean_Fmt_fmtCalcStep___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCalcStep___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCalcStep___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCalcStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCalcStep___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCalcStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 3, 210, 123, 188, 211, 75, 180)}};
static const lean_object* l_Lean_Fmt_fmtCalcStep___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCalcStep___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStep___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtCalcStep"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 184, 133, 234, 211, 108, 119, 232)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCalcSteps_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCalcSteps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcSteps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcSteps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCalcTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "calc"};
static const lean_object* l_Lean_Fmt_fmtCalcTerm___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCalcTerm___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCalcTerm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCalcTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCalcTerm___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCalcTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 46, 171, 201, 40, 237, 174, 33)}};
static const lean_object* l_Lean_Fmt_fmtCalcTerm___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCalcTerm___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtCalcTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "calcSteps"};
static const lean_object* l_Lean_Fmt_fmtCalcTerm___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtCalcTerm___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtCalcTerm___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCalcTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCalcTerm___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCalcTerm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(115, 10, 254, 10, 206, 238, 242, 161)}};
static const lean_object* l_Lean_Fmt_fmtCalcTerm___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtCalcTerm___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTerm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTerm___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtCalcTerm"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 252, 122, 212, 11, 76, 43, 246)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCalcTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "calcTactic"};
static const lean_object* l_Lean_Fmt_fmtCalcTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCalcTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCalcTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCalcTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCalcTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCalcTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 188, 49, 237, 47, 139, 25, 127)}};
static const lean_object* l_Lean_Fmt_fmtCalcTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCalcTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtCalcTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 39, 87, 9, 193, 245, 2, 36)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvCalc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "convCalc_"};
static const lean_object* l_Lean_Fmt_fmtConvCalc___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvCalc___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvCalc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvCalc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvCalc___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvCalc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 82, 111, 111, 95, 3, 213, 249)}};
static const lean_object* l_Lean_Fmt_fmtConvCalc___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvCalc___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCalc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCalc___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtConvCalc"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermMatches___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 207, 144, 201, 48, 189, 71, 16)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg(lean_object* v_secondaryPats_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_30_; 
v_fst_3_ = lean_ctor_get(v_a_2_, 0);
v_snd_4_ = lean_ctor_get(v_a_2_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_30_ == 0)
{
v___x_6_ = v_a_2_;
v_isShared_7_ = v_isSharedCheck_30_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_snd_4_);
lean_inc(v_fst_3_);
lean_dec(v_a_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_30_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = lean_array_get_size(v_secondaryPats_1_);
v___x_9_ = lean_nat_dec_lt(v_fst_3_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_11_; 
if (v_isShared_7_ == 0)
{
v___x_11_ = v___x_6_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_fst_3_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v_snd_4_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
else
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_13_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_14_ = lean_array_get_borrowed(v___x_13_, v_secondaryPats_1_, v_fst_3_);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_add(v_fst_3_, v___x_15_);
v___x_17_ = lean_array_get_borrowed(v___x_13_, v_secondaryPats_1_, v___x_16_);
lean_dec(v___x_16_);
v___x_18_ = lean_unsigned_to_nat(2u);
v___x_19_ = lean_mk_empty_array_with_capacity(v___x_18_);
lean_inc(v___x_14_);
v___x_20_ = lean_array_push(v___x_19_, v___x_14_);
lean_inc(v___x_17_);
v___x_21_ = lean_array_push(v___x_20_, v___x_17_);
v___x_22_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v___x_21_);
lean_dec_ref(v___x_21_);
v___x_23_ = l_Lean_Fmt_TaggedDoc_nested(v___x_22_);
v___x_24_ = lean_array_push(v_snd_4_, v___x_23_);
v___x_25_ = lean_nat_add(v_fst_3_, v___x_18_);
lean_dec(v_fst_3_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___x_24_);
lean_ctor_set(v___x_6_, 0, v___x_25_);
v___x_27_ = v___x_6_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v___x_24_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
v_a_2_ = v___x_27_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg___boxed(lean_object* v_secondaryPats_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg(v_secondaryPats_31_, v_a_32_);
lean_dec_ref(v_secondaryPats_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___lam__0(lean_object* v___y_34_){
_start:
{
lean_inc_ref(v___y_34_);
return v___y_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___lam__0___boxed(lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___lam__0(v___y_35_);
lean_dec_ref(v___y_35_);
return v_res_36_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__1(void){
_start:
{
lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___f_38_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__0));
v___x_39_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___f_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1(size_t v_sz_41_, size_t v_i_42_, lean_object* v_bs_43_){
_start:
{
uint8_t v___x_44_; 
v___x_44_ = lean_usize_dec_lt(v_i_42_, v_sz_41_);
if (v___x_44_ == 0)
{
return v_bs_43_;
}
else
{
lean_object* v_v_45_; lean_object* v___x_46_; lean_object* v_bs_x27_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; size_t v___x_51_; size_t v___x_52_; lean_object* v___x_53_; 
v_v_45_ = lean_array_uget(v_bs_43_, v_i_42_);
v___x_46_ = lean_unsigned_to_nat(0u);
v_bs_x27_47_ = lean_array_uset(v_bs_43_, v_i_42_, v___x_46_);
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v_v_45_);
v___x_49_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__1);
v___x_50_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_48_, v___x_49_);
v___x_51_ = ((size_t)1ULL);
v___x_52_ = lean_usize_add(v_i_42_, v___x_51_);
v___x_53_ = lean_array_uset(v_bs_x27_47_, v_i_42_, v___x_50_);
v_i_42_ = v___x_52_;
v_bs_43_ = v___x_53_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___boxed(lean_object* v_sz_55_, lean_object* v_i_56_, lean_object* v_bs_57_){
_start:
{
size_t v_sz_boxed_58_; size_t v_i_boxed_59_; lean_object* v_res_60_; 
v_sz_boxed_58_ = lean_unbox_usize(v_sz_55_);
lean_dec(v_sz_55_);
v_i_boxed_59_ = lean_unbox_usize(v_i_56_);
lean_dec(v_i_56_);
v_res_60_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1(v_sz_boxed_58_, v_i_boxed_59_, v_bs_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats(lean_object* v_secondaryPats_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_snd_69_; size_t v_sz_70_; size_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_67_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__1));
v___x_68_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg(v_secondaryPats_66_, v___x_67_);
v_snd_69_ = lean_ctor_get(v___x_68_, 1);
lean_inc(v_snd_69_);
lean_dec_ref(v___x_68_);
v_sz_70_ = lean_array_size(v_snd_69_);
v___x_71_ = ((size_t)0ULL);
v___x_72_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1(v_sz_70_, v___x_71_, v_snd_69_);
v___x_73_ = l_Lean_Fmt_TaggedDoc_combine(v___x_72_);
lean_dec_ref(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___boxed(lean_object* v_secondaryPats_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats(v_secondaryPats_74_);
lean_dec_ref(v_secondaryPats_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0(lean_object* v_secondaryPats_76_, lean_object* v_inst_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg(v_secondaryPats_76_, v_a_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___boxed(lean_object* v_secondaryPats_80_, lean_object* v_inst_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0(v_secondaryPats_80_, v_inst_81_, v_a_82_);
lean_dec_ref(v_secondaryPats_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches___lam__0(lean_object* v___y_84_){
_start:
{
lean_inc_ref(v___y_84_);
return v___y_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches___lam__0___boxed(lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Fmt_fmtTermMatches___lam__0(v___y_85_);
lean_dec_ref(v___y_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtTermMatches_spec__0___redArg(lean_object* v_a_87_, lean_object* v_b_88_){
_start:
{
lean_object* v_array_89_; lean_object* v_start_90_; lean_object* v_stop_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_104_; 
v_array_89_ = lean_ctor_get(v_a_87_, 0);
v_start_90_ = lean_ctor_get(v_a_87_, 1);
v_stop_91_ = lean_ctor_get(v_a_87_, 2);
v_isSharedCheck_104_ = !lean_is_exclusive(v_a_87_);
if (v_isSharedCheck_104_ == 0)
{
v___x_93_ = v_a_87_;
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_stop_91_);
lean_inc(v_start_90_);
lean_inc(v_array_89_);
lean_dec(v_a_87_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
uint8_t v___x_95_; 
v___x_95_ = lean_nat_dec_lt(v_start_90_, v_stop_91_);
if (v___x_95_ == 0)
{
lean_del_object(v___x_93_);
lean_dec(v_stop_91_);
lean_dec(v_start_90_);
lean_dec_ref(v_array_89_);
return v_b_88_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_nat_add(v_start_90_, v___x_96_);
lean_inc_ref(v_array_89_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v___x_97_);
v___x_99_ = v___x_93_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_array_89_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_stop_91_);
v___x_99_ = v_reuseFailAlloc_103_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_array_fget(v_array_89_, v_start_90_);
lean_dec(v_start_90_);
lean_dec_ref(v_array_89_);
v___x_101_ = lean_array_push(v_b_88_, v___x_100_);
v_a_87_ = v___x_99_;
v_b_88_ = v___x_101_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermMatches___closed__4(void){
_start:
{
lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___f_111_ = ((lean_object*)(l_Lean_Fmt_fmtTermMatches___closed__3));
v___x_112_ = l_Lean_Fmt_TaggedDoc_space;
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___f_111_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermMatches___closed__6(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = ((lean_object*)(l_Lean_Fmt_fmtTermMatches___closed__5));
v___x_116_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermMatches___closed__7(void){
_start:
{
lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___f_118_ = ((lean_object*)(l_Lean_Fmt_fmtTermMatches___closed__3));
v___x_119_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___f_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches(lean_object* v_x_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Fmt_fmtTermMatches___closed__2));
lean_inc(v_x_121_);
v___x_125_ = l_Lean_Syntax_isOfKind(v_x_121_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v_x_121_);
v___x_126_ = l_Lean_Fmt_Error_partialFormatter;
v___x_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v_a_123_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = l_Lean_Syntax_getArg(v_x_121_, v___x_128_);
v___x_130_ = l_Lean_Fmt_fmt(v___x_129_, v_a_122_, v_a_123_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v_a_132_; lean_object* v___x_133_; lean_object* v_matchesTk_134_; lean_object* v___x_135_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
v_a_132_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_130_, 2);
v___x_133_ = lean_unsigned_to_nat(1u);
v_matchesTk_134_ = l_Lean_Syntax_getArg(v_x_121_, v___x_133_);
v___x_135_ = l_Lean_Fmt_fmt(v_matchesTk_134_, v_a_122_, v_a_132_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v_a_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_pats_140_; lean_object* v___x_141_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
v_a_137_ = lean_ctor_get(v___x_135_, 1);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_135_, 2);
v___x_138_ = lean_unsigned_to_nat(2u);
v___x_139_ = l_Lean_Syntax_getArg(v_x_121_, v___x_138_);
lean_dec(v_x_121_);
v_pats_140_ = l_Lean_Syntax_getArgs(v___x_139_);
lean_dec(v___x_139_);
v___x_141_ = l_Lean_Fmt_fmtTSepArray___redArg(v_pats_140_, v_a_122_, v_a_137_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_198_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_a_143_ = lean_ctor_get(v___x_141_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_198_ == 0)
{
v___x_145_ = v___x_141_;
v_isShared_146_ = v_isSharedCheck_198_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_inc(v_a_142_);
lean_dec(v___x_141_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_198_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_array_get_size(v_a_142_);
v___x_148_ = lean_nat_dec_eq(v___x_147_, v___x_133_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_149_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_150_ = lean_array_get_borrowed(v___x_149_, v_a_142_, v___x_128_);
lean_inc(v___x_150_);
v___x_151_ = l_Lean_Fmt_TaggedDoc_nested(v___x_150_);
v___x_152_ = l_Array_toSubarray___redArg(v_a_142_, v___x_133_, v___x_147_);
v___x_153_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__0));
v___x_154_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtTermMatches_spec__0___redArg(v___x_152_, v___x_153_);
v___x_155_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats(v___x_154_);
lean_dec_ref(v___x_154_);
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v_a_136_);
v___x_157_ = lean_obj_once(&l_Lean_Fmt_fmtTermMatches___closed__4, &l_Lean_Fmt_fmtTermMatches___closed__4_once, _init_l_Lean_Fmt_fmtTermMatches___closed__4);
lean_inc_ref(v___x_156_);
v___x_158_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_156_, v___x_157_);
lean_inc_ref(v___x_151_);
v___x_159_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_151_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
v___x_161_ = lean_obj_once(&l_Lean_Fmt_fmtTermMatches___closed__6, &l_Lean_Fmt_fmtTermMatches___closed__6_once, _init_l_Lean_Fmt_fmtTermMatches___closed__6);
v___x_162_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_160_, v___x_161_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_155_);
v___x_165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
lean_ctor_set(v___x_165_, 2, v___x_163_);
v___x_166_ = lean_unsigned_to_nat(3u);
v___x_167_ = lean_mk_empty_array_with_capacity(v___x_166_);
lean_inc_ref(v___x_167_);
v___x_168_ = lean_array_push(v___x_167_, v___x_158_);
v___x_169_ = lean_array_push(v___x_168_, v___x_162_);
lean_inc_ref(v___x_165_);
v___x_170_ = lean_array_push(v___x_169_, v___x_165_);
v___x_171_ = l_Lean_Fmt_TaggedDoc_combine(v___x_170_);
lean_dec_ref(v___x_170_);
v___x_172_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_156_, v___x_161_);
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_151_);
v___x_174_ = lean_obj_once(&l_Lean_Fmt_fmtTermMatches___closed__7, &l_Lean_Fmt_fmtTermMatches___closed__7_once, _init_l_Lean_Fmt_fmtTermMatches___closed__7);
v___x_175_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_173_, v___x_174_);
v___x_176_ = lean_array_push(v___x_167_, v___x_172_);
v___x_177_ = lean_array_push(v___x_176_, v___x_175_);
v___x_178_ = lean_array_push(v___x_177_, v___x_165_);
v___x_179_ = l_Lean_Fmt_TaggedDoc_combine(v___x_178_);
lean_dec_ref(v___x_178_);
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_138_);
lean_inc_ref(v___x_180_);
v___x_181_ = lean_array_push(v___x_180_, v___x_171_);
v___x_182_ = lean_array_push(v___x_181_, v___x_179_);
v___x_183_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_182_);
v___x_184_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_183_);
v___x_185_ = l_Lean_Fmt_TaggedDoc_hardNested(v_a_131_);
v___x_186_ = lean_array_push(v___x_180_, v___x_185_);
v___x_187_ = lean_array_push(v___x_186_, v___x_184_);
v___x_188_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_187_);
lean_dec_ref(v___x_187_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_188_);
v___x_190_ = v___x_145_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_a_143_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_192_ = lean_array_fget(v_a_142_, v___x_128_);
lean_dec(v_a_142_);
v___x_193_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_193_, 0, v___x_148_);
lean_ctor_set_uint8(v___x_193_, 1, v___x_148_);
v___x_194_ = l_Lean_Fmt_Layouts_keywordSeparated(v_a_131_, v_a_136_, v___x_192_, v___x_193_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_194_);
v___x_196_ = v___x_145_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_a_143_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_a_136_);
lean_dec(v_a_131_);
v_a_199_ = lean_ctor_get(v___x_141_, 0);
v_a_200_ = lean_ctor_get(v___x_141_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_141_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_inc(v_a_199_);
lean_dec(v___x_141_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_199_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_dec(v_a_131_);
lean_dec(v_x_121_);
return v___x_135_;
}
}
else
{
lean_dec(v_x_121_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches___boxed(lean_object* v_x_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Fmt_fmtTermMatches(v_x_208_, v_a_209_, v_a_210_);
lean_dec_ref(v_a_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtTermMatches_spec__0(lean_object* v_inst_212_, lean_object* v_R_213_, lean_object* v_a_214_, lean_object* v_b_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtTermMatches_spec__0___redArg(v_a_214_, v_b_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1(){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_224_ = l_Lean_Fmt_fmtAttribute;
v___x_225_ = ((lean_object*)(l_Lean_Fmt_fmtTermMatches___closed__2));
v___x_226_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__2));
v___x_227_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermMatches___boxed), 3, 0);
v___x_228_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_224_, v___x_225_, v___x_226_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___boxed(lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1();
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnbracketedExplicitBinders(lean_object* v_x_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1));
lean_inc(v_x_239_);
v___x_243_ = l_Lean_Syntax_isOfKind(v_x_239_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_x_239_);
v___x_244_ = l_Lean_Fmt_Error_partialFormatter;
v___x_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_a_241_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_typeAscriptionTk_x3f_249_; lean_object* v_type_x3f_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = l_Lean_Syntax_getArg(v_x_239_, v___x_246_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = l_Lean_Syntax_getArg(v_x_239_, v___x_258_);
lean_dec(v_x_239_);
v___x_260_ = l_Lean_Syntax_isNone(v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_259_);
v___x_262_ = l_Lean_Syntax_matchesNull(v___x_259_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v___x_259_);
lean_dec(v___x_247_);
v___x_263_ = l_Lean_Fmt_Error_partialFormatter;
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_a_241_);
return v___x_264_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_265_; lean_object* v_type_x3f_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_typeAscriptionTk_x3f_265_ = l_Lean_Syntax_getArg(v___x_259_, v___x_246_);
v_type_x3f_266_ = l_Lean_Syntax_getArg(v___x_259_, v___x_258_);
lean_dec(v___x_259_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v_typeAscriptionTk_x3f_265_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v_type_x3f_266_);
v_typeAscriptionTk_x3f_249_ = v___x_267_;
v_type_x3f_250_ = v___x_268_;
v___y_251_ = v_a_240_;
v___y_252_ = v_a_241_;
goto v___jp_248_;
}
}
else
{
lean_object* v___x_269_; 
lean_dec(v___x_259_);
v___x_269_ = lean_box(0);
v_typeAscriptionTk_x3f_249_ = v___x_269_;
v_type_x3f_250_ = v___x_269_;
v___y_251_ = v_a_240_;
v___y_252_ = v_a_241_;
goto v___jp_248_;
}
v___jp_248_:
{
lean_object* v_ids_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_ids_253_ = l_Lean_Syntax_getArgs(v___x_247_);
lean_dec(v___x_247_);
v___x_254_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2));
v___x_255_ = lean_box(0);
v___x_256_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__3));
v___x_257_ = l_Lean_Fmt_fmtBinder(v___x_254_, v_ids_253_, v___x_254_, v_typeAscriptionTk_x3f_249_, v_type_x3f_250_, v___x_255_, v___x_254_, v___x_256_, v___y_251_, v___y_252_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnbracketedExplicitBinders___boxed(lean_object* v_x_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Fmt_fmtUnbracketedExplicitBinders(v_x_270_, v_a_271_, v_a_272_);
lean_dec_ref(v_a_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1(){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_280_ = l_Lean_Fmt_fmtAttribute;
v___x_281_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1));
v___x_282_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__1));
v___x_283_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___boxed), 3, 0);
v___x_284_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_280_, v___x_281_, v___x_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___boxed(lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1();
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBracketedExplicitBinders(lean_object* v_x_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1));
lean_inc(v_x_291_);
v___x_295_ = l_Lean_Syntax_isOfKind(v_x_291_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v_x_291_);
v___x_296_ = l_Lean_Fmt_Error_partialFormatter;
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_a_293_);
return v___x_297_;
}
else
{
lean_object* v___x_298_; lean_object* v_lbTk_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_typeAscriptionTk_303_; lean_object* v___x_304_; lean_object* v_type_305_; lean_object* v___x_306_; lean_object* v_rbTk_307_; lean_object* v_ids_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v_lbTk_299_ = l_Lean_Syntax_getArg(v_x_291_, v___x_298_);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = l_Lean_Syntax_getArg(v_x_291_, v___x_300_);
v___x_302_ = lean_unsigned_to_nat(2u);
v_typeAscriptionTk_303_ = l_Lean_Syntax_getArg(v_x_291_, v___x_302_);
v___x_304_ = lean_unsigned_to_nat(3u);
v_type_305_ = l_Lean_Syntax_getArg(v_x_291_, v___x_304_);
v___x_306_ = lean_unsigned_to_nat(4u);
v_rbTk_307_ = l_Lean_Syntax_getArg(v_x_291_, v___x_306_);
lean_dec(v_x_291_);
v_ids_308_ = l_Lean_Syntax_getArgs(v___x_301_);
lean_dec(v___x_301_);
v___x_309_ = lean_mk_empty_array_with_capacity(v___x_300_);
lean_inc_ref(v___x_309_);
v___x_310_ = lean_array_push(v___x_309_, v_lbTk_299_);
v___x_311_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2));
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v_typeAscriptionTk_303_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v_type_305_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_array_push(v___x_309_, v_rbTk_307_);
v___x_316_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__3));
v___x_317_ = l_Lean_Fmt_fmtBinder(v___x_310_, v_ids_308_, v___x_311_, v___x_312_, v___x_313_, v___x_314_, v___x_315_, v___x_316_, v_a_292_, v_a_293_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBracketedExplicitBinders___boxed(lean_object* v_x_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Fmt_fmtBracketedExplicitBinders(v_x_318_, v_a_319_, v_a_320_);
lean_dec_ref(v_a_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1(){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_328_ = l_Lean_Fmt_fmtAttribute;
v___x_329_ = ((lean_object*)(l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1));
v___x_330_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__1));
v___x_331_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBracketedExplicitBinders___boxed), 3, 0);
v___x_332_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_328_, v___x_329_, v___x_330_, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___boxed(lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1();
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_explicitBindersToGroup_spec__0(size_t v_sz_335_, size_t v_i_336_, lean_object* v_bs_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_lt(v_i_336_, v_sz_335_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v_bs_337_);
return v___x_339_;
}
else
{
lean_object* v_v_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_v_340_ = lean_array_uget(v_bs_337_, v_i_336_);
v___x_341_ = ((lean_object*)(l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1));
lean_inc(v_v_340_);
v___x_342_ = l_Lean_Syntax_isOfKind(v_v_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec(v_v_340_);
lean_dec_ref(v_bs_337_);
v___x_343_ = lean_box(0);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v_bs_x27_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v_bs_x27_345_ = lean_array_uset(v_bs_337_, v_i_336_, v___x_344_);
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_add(v_i_336_, v___x_346_);
v___x_348_ = lean_array_uset(v_bs_x27_345_, v_i_336_, v_v_340_);
v_i_336_ = v___x_347_;
v_bs_337_ = v___x_348_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_explicitBindersToGroup_spec__0___boxed(lean_object* v_sz_350_, lean_object* v_i_351_, lean_object* v_bs_352_){
_start:
{
size_t v_sz_boxed_353_; size_t v_i_boxed_354_; lean_object* v_res_355_; 
v_sz_boxed_353_ = lean_unbox_usize(v_sz_350_);
lean_dec(v_sz_350_);
v_i_boxed_354_ = lean_unbox_usize(v_i_351_);
lean_dec(v_i_351_);
v_res_355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_explicitBindersToGroup_spec__0(v_sz_boxed_353_, v_i_boxed_354_, v_bs_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_explicitBindersToGroup(lean_object* v_bs_360_){
_start:
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_Fmt_explicitBindersToGroup___closed__1));
lean_inc(v_bs_360_);
v___x_362_ = l_Lean_Syntax_isOfKind(v_bs_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v_bs_360_);
v___x_363_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2));
return v___x_363_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = l_Lean_Syntax_getArg(v_bs_360_, v___x_364_);
lean_dec(v_bs_360_);
v___x_366_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1));
lean_inc(v___x_365_);
v___x_367_ = l_Lean_Syntax_isOfKind(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; size_t v_sz_369_; size_t v___x_370_; lean_object* v___x_371_; 
v___x_368_ = l_Lean_Syntax_getArgs(v___x_365_);
lean_dec(v___x_365_);
v_sz_369_ = lean_array_size(v___x_368_);
v___x_370_ = ((size_t)0ULL);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_explicitBindersToGroup_spec__0(v_sz_369_, v___x_370_, v___x_368_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v___x_372_; 
v___x_372_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2));
return v___x_372_;
}
else
{
lean_object* v_val_373_; 
v_val_373_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_373_);
lean_dec_ref_known(v___x_371_, 1);
return v_val_373_;
}
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_unsigned_to_nat(1u);
v___x_375_ = lean_mk_empty_array_with_capacity(v___x_374_);
v___x_376_ = lean_array_push(v___x_375_, v___x_365_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExists(lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_Fmt_fmtExists___closed__1));
lean_inc(v_x_380_);
v___x_382_ = l_Lean_Syntax_isOfKind(v_x_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_x_380_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v___x_384_; lean_object* v_bs_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v_bs_385_ = l_Lean_Syntax_getArg(v_x_380_, v___x_384_);
v___x_386_ = ((lean_object*)(l_Lean_Fmt_explicitBindersToGroup___closed__1));
lean_inc(v_bs_385_);
v___x_387_ = l_Lean_Syntax_isOfKind(v_bs_385_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec(v_bs_385_);
lean_dec(v_x_380_);
v___x_388_ = lean_box(0);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v_exTk_390_; lean_object* v___x_391_; lean_object* v_commaTk_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_389_ = lean_unsigned_to_nat(0u);
v_exTk_390_ = l_Lean_Syntax_getArg(v_x_380_, v___x_389_);
v___x_391_ = lean_unsigned_to_nat(2u);
v_commaTk_392_ = l_Lean_Syntax_getArg(v_x_380_, v___x_391_);
v___x_393_ = lean_unsigned_to_nat(3u);
v___x_394_ = l_Lean_Syntax_getArg(v_x_380_, v___x_393_);
lean_dec(v_x_380_);
v___x_395_ = l_Lean_Fmt_explicitBindersToGroup(v_bs_385_);
v___x_396_ = lean_mk_empty_array_with_capacity(v___x_384_);
lean_inc_ref(v___x_396_);
v___x_397_ = lean_array_push(v___x_396_, v___x_395_);
v___x_398_ = lean_array_push(v___x_396_, v___x_397_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
v___x_400_ = lean_box(0);
v___x_401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_401_, 0, v_exTk_390_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
lean_ctor_set(v___x_401_, 3, v___x_400_);
lean_ctor_set(v___x_401_, 4, v_commaTk_392_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_394_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1(){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_410_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_411_ = ((lean_object*)(l_Lean_Fmt_fmtExists___closed__1));
v___x_412_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__1));
v___x_413_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExists), 1, 0);
v___x_414_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_410_, v___x_411_, v___x_412_, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___boxed(lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1();
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExistsKeyword(lean_object* v_x_420_){
_start:
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Fmt_fmtExistsKeyword___closed__1));
lean_inc(v_x_420_);
v___x_422_ = l_Lean_Syntax_isOfKind(v_x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_dec(v_x_420_);
v___x_423_ = lean_box(0);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v_bs_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v_bs_425_ = l_Lean_Syntax_getArg(v_x_420_, v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Fmt_explicitBindersToGroup___closed__1));
lean_inc(v_bs_425_);
v___x_427_ = l_Lean_Syntax_isOfKind(v_bs_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v_bs_425_);
lean_dec(v_x_420_);
v___x_428_ = lean_box(0);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v_existsTk_430_; lean_object* v___x_431_; lean_object* v_commaTk_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v_existsTk_430_ = l_Lean_Syntax_getArg(v_x_420_, v___x_429_);
v___x_431_ = lean_unsigned_to_nat(2u);
v_commaTk_432_ = l_Lean_Syntax_getArg(v_x_420_, v___x_431_);
v___x_433_ = lean_unsigned_to_nat(3u);
v___x_434_ = l_Lean_Syntax_getArg(v_x_420_, v___x_433_);
lean_dec(v_x_420_);
v___x_435_ = l_Lean_Fmt_explicitBindersToGroup(v_bs_425_);
v___x_436_ = lean_mk_empty_array_with_capacity(v___x_424_);
lean_inc_ref(v___x_436_);
v___x_437_ = lean_array_push(v___x_436_, v___x_435_);
v___x_438_ = lean_array_push(v___x_436_, v___x_437_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_441_, 0, v_existsTk_430_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_440_);
lean_ctor_set(v___x_441_, 3, v___x_440_);
lean_ctor_set(v___x_441_, 4, v_commaTk_432_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_434_);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1(){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_450_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_451_ = ((lean_object*)(l_Lean_Fmt_fmtExistsKeyword___closed__1));
v___x_452_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__1));
v___x_453_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExistsKeyword), 1, 0);
v___x_454_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_450_, v___x_451_, v___x_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___boxed(lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1();
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSigma(lean_object* v_x_460_){
_start:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Fmt_fmtSigma___closed__1));
lean_inc(v_x_460_);
v___x_462_ = l_Lean_Syntax_isOfKind(v_x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec(v_x_460_);
v___x_463_ = lean_box(0);
return v___x_463_;
}
else
{
lean_object* v___x_464_; lean_object* v_bs_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_464_ = lean_unsigned_to_nat(1u);
v_bs_465_ = l_Lean_Syntax_getArg(v_x_460_, v___x_464_);
v___x_466_ = ((lean_object*)(l_Lean_Fmt_explicitBindersToGroup___closed__1));
lean_inc(v_bs_465_);
v___x_467_ = l_Lean_Syntax_isOfKind(v_bs_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec(v_bs_465_);
lean_dec(v_x_460_);
v___x_468_ = lean_box(0);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v_sigmaTk_470_; lean_object* v___x_471_; lean_object* v_commaTk_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v_sigmaTk_470_ = l_Lean_Syntax_getArg(v_x_460_, v___x_469_);
v___x_471_ = lean_unsigned_to_nat(2u);
v_commaTk_472_ = l_Lean_Syntax_getArg(v_x_460_, v___x_471_);
v___x_473_ = lean_unsigned_to_nat(3u);
v___x_474_ = l_Lean_Syntax_getArg(v_x_460_, v___x_473_);
lean_dec(v_x_460_);
v___x_475_ = l_Lean_Fmt_explicitBindersToGroup(v_bs_465_);
v___x_476_ = lean_mk_empty_array_with_capacity(v___x_464_);
lean_inc_ref(v___x_476_);
v___x_477_ = lean_array_push(v___x_476_, v___x_475_);
v___x_478_ = lean_array_push(v___x_476_, v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
v___x_480_ = lean_box(0);
v___x_481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_481_, 0, v_sigmaTk_470_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
lean_ctor_set(v___x_481_, 3, v___x_480_);
lean_ctor_set(v___x_481_, 4, v_commaTk_472_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_474_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1(){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_490_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_491_ = ((lean_object*)(l_Lean_Fmt_fmtSigma___closed__1));
v___x_492_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__1));
v___x_493_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSigma), 1, 0);
v___x_494_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_490_, v___x_491_, v___x_492_, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___boxed(lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1();
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPSigma(lean_object* v_x_500_){
_start:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_Fmt_fmtPSigma___closed__1));
lean_inc(v_x_500_);
v___x_502_ = l_Lean_Syntax_isOfKind(v_x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v_x_500_);
v___x_503_ = lean_box(0);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v_bs_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v_bs_505_ = l_Lean_Syntax_getArg(v_x_500_, v___x_504_);
v___x_506_ = ((lean_object*)(l_Lean_Fmt_explicitBindersToGroup___closed__1));
lean_inc(v_bs_505_);
v___x_507_ = l_Lean_Syntax_isOfKind(v_bs_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec(v_bs_505_);
lean_dec(v_x_500_);
v___x_508_ = lean_box(0);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v_psigmaTk_510_; lean_object* v___x_511_; lean_object* v_commaTk_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v_psigmaTk_510_ = l_Lean_Syntax_getArg(v_x_500_, v___x_509_);
v___x_511_ = lean_unsigned_to_nat(2u);
v_commaTk_512_ = l_Lean_Syntax_getArg(v_x_500_, v___x_511_);
v___x_513_ = lean_unsigned_to_nat(3u);
v___x_514_ = l_Lean_Syntax_getArg(v_x_500_, v___x_513_);
lean_dec(v_x_500_);
v___x_515_ = l_Lean_Fmt_explicitBindersToGroup(v_bs_505_);
v___x_516_ = lean_mk_empty_array_with_capacity(v___x_504_);
lean_inc_ref(v___x_516_);
v___x_517_ = lean_array_push(v___x_516_, v___x_515_);
v___x_518_ = lean_array_push(v___x_516_, v___x_517_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_521_, 0, v_psigmaTk_510_);
lean_ctor_set(v___x_521_, 1, v___x_519_);
lean_ctor_set(v___x_521_, 2, v___x_520_);
lean_ctor_set(v___x_521_, 3, v___x_520_);
lean_ctor_set(v___x_521_, 4, v_commaTk_512_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_514_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1(){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_530_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_531_ = ((lean_object*)(l_Lean_Fmt_fmtPSigma___closed__1));
v___x_532_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__1));
v___x_533_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPSigma), 1, 0);
v___x_534_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_530_, v___x_531_, v___x_532_, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___boxed(lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1();
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
return v_x_537_;
}
else
{
lean_object* v_key_539_; lean_object* v_value_540_; lean_object* v_tail_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_567_; 
v_key_539_ = lean_ctor_get(v_x_538_, 0);
v_value_540_ = lean_ctor_get(v_x_538_, 1);
v_tail_541_ = lean_ctor_get(v_x_538_, 2);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_567_ == 0)
{
v___x_543_ = v_x_538_;
v_isShared_544_ = v_isSharedCheck_567_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_tail_541_);
lean_inc(v_value_540_);
lean_inc(v_key_539_);
lean_dec(v_x_538_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_567_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; uint64_t v___y_547_; 
v___x_545_ = lean_array_get_size(v_x_537_);
if (lean_obj_tag(v_key_539_) == 0)
{
uint64_t v___x_565_; 
v___x_565_ = 1723ULL;
v___y_547_ = v___x_565_;
goto v___jp_546_;
}
else
{
uint64_t v_hash_566_; 
v_hash_566_ = lean_ctor_get_uint64(v_key_539_, sizeof(void*)*2);
v___y_547_ = v_hash_566_;
goto v___jp_546_;
}
v___jp_546_:
{
uint64_t v___x_548_; uint64_t v___x_549_; uint64_t v_fold_550_; uint64_t v___x_551_; uint64_t v___x_552_; uint64_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_548_ = 32ULL;
v___x_549_ = lean_uint64_shift_right(v___y_547_, v___x_548_);
v_fold_550_ = lean_uint64_xor(v___y_547_, v___x_549_);
v___x_551_ = 16ULL;
v___x_552_ = lean_uint64_shift_right(v_fold_550_, v___x_551_);
v___x_553_ = lean_uint64_xor(v_fold_550_, v___x_552_);
v___x_554_ = lean_uint64_to_usize(v___x_553_);
v___x_555_ = lean_usize_of_nat(v___x_545_);
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_sub(v___x_555_, v___x_556_);
v___x_558_ = lean_usize_land(v___x_554_, v___x_557_);
v___x_559_ = lean_array_uget_borrowed(v_x_537_, v___x_558_);
lean_inc(v___x_559_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 2, v___x_559_);
v___x_561_ = v___x_543_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_key_539_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_value_540_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v___x_559_);
v___x_561_ = v_reuseFailAlloc_564_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; 
v___x_562_ = lean_array_uset(v_x_537_, v___x_558_, v___x_561_);
v_x_537_ = v___x_562_;
v_x_538_ = v_tail_541_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2___redArg(lean_object* v_i_568_, lean_object* v_source_569_, lean_object* v_target_570_){
_start:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_array_get_size(v_source_569_);
v___x_572_ = lean_nat_dec_lt(v_i_568_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec_ref(v_source_569_);
lean_dec(v_i_568_);
return v_target_570_;
}
else
{
lean_object* v_es_573_; lean_object* v___x_574_; lean_object* v_source_575_; lean_object* v_target_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_es_573_ = lean_array_fget(v_source_569_, v_i_568_);
v___x_574_ = lean_box(0);
v_source_575_ = lean_array_fset(v_source_569_, v_i_568_, v___x_574_);
v_target_576_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2_spec__3___redArg(v_target_570_, v_es_573_);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_i_568_, v___x_577_);
lean_dec(v_i_568_);
v_i_568_ = v___x_578_;
v_source_569_ = v_source_575_;
v_target_570_ = v_target_576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1___redArg(lean_object* v_data_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_nbuckets_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_581_ = lean_array_get_size(v_data_580_);
v___x_582_ = lean_unsigned_to_nat(2u);
v_nbuckets_583_ = lean_nat_mul(v___x_581_, v___x_582_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_box(0);
v___x_586_ = lean_mk_array(v_nbuckets_583_, v___x_585_);
v___x_587_ = lean_array_propagate_mark(v_data_580_, v___x_586_);
v___x_588_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2___redArg(v___x_584_, v_data_580_, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg(lean_object* v_a_589_, lean_object* v_x_590_){
_start:
{
if (lean_obj_tag(v_x_590_) == 0)
{
uint8_t v___x_591_; 
v___x_591_ = 0;
return v___x_591_;
}
else
{
lean_object* v_key_592_; lean_object* v_tail_593_; uint8_t v___x_594_; 
v_key_592_ = lean_ctor_get(v_x_590_, 0);
v_tail_593_ = lean_ctor_get(v_x_590_, 2);
v___x_594_ = lean_name_eq(v_key_592_, v_a_589_);
if (v___x_594_ == 0)
{
v_x_590_ = v_tail_593_;
goto _start;
}
else
{
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg___boxed(lean_object* v_a_596_, lean_object* v_x_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg(v_a_596_, v_x_597_);
lean_dec(v_x_597_);
lean_dec(v_a_596_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(lean_object* v_m_600_, lean_object* v_a_601_, lean_object* v_b_602_){
_start:
{
lean_object* v_size_603_; lean_object* v_buckets_604_; lean_object* v___x_605_; uint64_t v___y_607_; 
v_size_603_ = lean_ctor_get(v_m_600_, 0);
v_buckets_604_ = lean_ctor_get(v_m_600_, 1);
v___x_605_ = lean_array_get_size(v_buckets_604_);
if (lean_obj_tag(v_a_601_) == 0)
{
uint64_t v___x_644_; 
v___x_644_ = 1723ULL;
v___y_607_ = v___x_644_;
goto v___jp_606_;
}
else
{
uint64_t v_hash_645_; 
v_hash_645_ = lean_ctor_get_uint64(v_a_601_, sizeof(void*)*2);
v___y_607_ = v_hash_645_;
goto v___jp_606_;
}
v___jp_606_:
{
uint64_t v___x_608_; uint64_t v___x_609_; uint64_t v_fold_610_; uint64_t v___x_611_; uint64_t v___x_612_; uint64_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v___x_618_; lean_object* v_bkt_619_; uint8_t v___x_620_; 
v___x_608_ = 32ULL;
v___x_609_ = lean_uint64_shift_right(v___y_607_, v___x_608_);
v_fold_610_ = lean_uint64_xor(v___y_607_, v___x_609_);
v___x_611_ = 16ULL;
v___x_612_ = lean_uint64_shift_right(v_fold_610_, v___x_611_);
v___x_613_ = lean_uint64_xor(v_fold_610_, v___x_612_);
v___x_614_ = lean_uint64_to_usize(v___x_613_);
v___x_615_ = lean_usize_of_nat(v___x_605_);
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_sub(v___x_615_, v___x_616_);
v___x_618_ = lean_usize_land(v___x_614_, v___x_617_);
v_bkt_619_ = lean_array_uget_borrowed(v_buckets_604_, v___x_618_);
v___x_620_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg(v_a_601_, v_bkt_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_641_; 
lean_inc_ref(v_buckets_604_);
lean_inc(v_size_603_);
v_isSharedCheck_641_ = !lean_is_exclusive(v_m_600_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; lean_object* v_unused_643_; 
v_unused_642_ = lean_ctor_get(v_m_600_, 1);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_m_600_, 0);
lean_dec(v_unused_643_);
v___x_622_ = v_m_600_;
v_isShared_623_ = v_isSharedCheck_641_;
goto v_resetjp_621_;
}
else
{
lean_dec(v_m_600_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_641_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v_size_x27_625_; lean_object* v___x_626_; lean_object* v_buckets_x27_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v_size_x27_625_ = lean_nat_add(v_size_603_, v___x_624_);
lean_dec(v_size_603_);
lean_inc(v_bkt_619_);
v___x_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_626_, 0, v_a_601_);
lean_ctor_set(v___x_626_, 1, v_b_602_);
lean_ctor_set(v___x_626_, 2, v_bkt_619_);
v_buckets_x27_627_ = lean_array_uset(v_buckets_604_, v___x_618_, v___x_626_);
v___x_628_ = lean_unsigned_to_nat(4u);
v___x_629_ = lean_nat_mul(v_size_x27_625_, v___x_628_);
v___x_630_ = lean_unsigned_to_nat(3u);
v___x_631_ = lean_nat_div(v___x_629_, v___x_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_array_get_size(v_buckets_x27_627_);
v___x_633_ = lean_nat_dec_le(v___x_631_, v___x_632_);
lean_dec(v___x_631_);
if (v___x_633_ == 0)
{
lean_object* v_val_634_; lean_object* v___x_636_; 
v_val_634_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1___redArg(v_buckets_x27_627_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v_val_634_);
lean_ctor_set(v___x_622_, 0, v_size_x27_625_);
v___x_636_ = v___x_622_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_size_x27_625_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_val_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___x_639_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v_buckets_x27_627_);
lean_ctor_set(v___x_622_, 0, v_size_x27_625_);
v___x_639_ = v___x_622_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_size_x27_625_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_buckets_x27_627_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_dec(v_b_602_);
lean_dec(v_a_601_);
return v_m_600_;
}
}
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes___closed__4(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_654_ = lean_box(0);
v___x_655_ = lean_unsigned_to_nat(16u);
v___x_656_ = lean_mk_array(v___x_655_, v___x_654_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes___closed__5(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__4, &l_Lean_Fmt_fmtTimes___closed__4_once, _init_l_Lean_Fmt_fmtTimes___closed__4);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes___closed__6(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_660_ = lean_box(0);
v___x_661_ = ((lean_object*)(l_Lean_Fmt_fmtTimes___closed__3));
v___x_662_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__5, &l_Lean_Fmt_fmtTimes___closed__5_once, _init_l_Lean_Fmt_fmtTimes___closed__5);
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(v___x_662_, v___x_661_, v___x_660_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes___closed__7(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; lean_object* v___x_667_; 
v___x_664_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__6, &l_Lean_Fmt_fmtTimes___closed__6_once, _init_l_Lean_Fmt_fmtTimes___closed__6);
v___x_665_ = ((lean_object*)(l_Lean_Fmt_fmtTimes___closed__1));
v___x_666_ = 0;
v___x_667_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_664_);
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*2, v___x_666_);
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*2 + 1, v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes(void){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__7, &l_Lean_Fmt_fmtTimes___closed__7_once, _init_l_Lean_Fmt_fmtTimes___closed__7);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0(lean_object* v_00_u03b2_669_, lean_object* v_m_670_, lean_object* v_a_671_, lean_object* v_b_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(v_m_670_, v_a_671_, v_b_672_);
return v___x_673_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0(lean_object* v_00_u03b2_674_, lean_object* v_a_675_, lean_object* v_x_676_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg(v_a_675_, v_x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___boxed(lean_object* v_00_u03b2_678_, lean_object* v_a_679_, lean_object* v_x_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0(v_00_u03b2_678_, v_a_679_, v_x_680_);
lean_dec(v_x_680_);
lean_dec(v_a_679_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1(lean_object* v_00_u03b2_683_, lean_object* v_data_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1___redArg(v_data_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_686_, lean_object* v_i_687_, lean_object* v_source_688_, lean_object* v_target_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2___redArg(v_i_687_, v_source_688_, v_target_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2_spec__3___redArg(v_x_692_, v_x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1(){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_704_ = l_Lean_Fmt_infixFmtAttribute;
v___x_705_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__1));
v___x_706_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__3));
v___x_707_ = l_Lean_Fmt_fmtTimes;
v___x_708_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_704_, v___x_705_, v___x_706_, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___boxed(lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1();
return v_res_710_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSigmaTimes___closed__2(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_box(0);
v___x_717_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__1));
v___x_718_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__5, &l_Lean_Fmt_fmtTimes___closed__5_once, _init_l_Lean_Fmt_fmtTimes___closed__5);
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(v___x_718_, v___x_717_, v___x_716_);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSigmaTimes___closed__3(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; 
v___x_720_ = lean_obj_once(&l_Lean_Fmt_fmtSigmaTimes___closed__2, &l_Lean_Fmt_fmtSigmaTimes___closed__2_once, _init_l_Lean_Fmt_fmtSigmaTimes___closed__2);
v___x_721_ = ((lean_object*)(l_Lean_Fmt_fmtSigmaTimes___closed__1));
v___x_722_ = 0;
v___x_723_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_720_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*2, v___x_722_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*2 + 1, v___x_722_);
return v___x_723_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSigmaTimes(void){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_obj_once(&l_Lean_Fmt_fmtSigmaTimes___closed__3, &l_Lean_Fmt_fmtSigmaTimes___closed__3_once, _init_l_Lean_Fmt_fmtSigmaTimes___closed__3);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1(){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_731_ = l_Lean_Fmt_infixFmtAttribute;
v___x_732_ = ((lean_object*)(l_Lean_Fmt_fmtTimes___closed__3));
v___x_733_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__1));
v___x_734_ = l_Lean_Fmt_fmtSigmaTimes;
v___x_735_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_731_, v___x_732_, v___x_733_, v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___boxed(lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1();
return v_res_737_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes_x27___closed__2(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_741_ = lean_box(0);
v___x_742_ = ((lean_object*)(l_Lean_Fmt_fmtTimes_x27___closed__1));
v___x_743_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__5, &l_Lean_Fmt_fmtTimes___closed__5_once, _init_l_Lean_Fmt_fmtTimes___closed__5);
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(v___x_743_, v___x_742_, v___x_741_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes_x27___closed__3(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; 
v___x_745_ = lean_obj_once(&l_Lean_Fmt_fmtTimes_x27___closed__2, &l_Lean_Fmt_fmtTimes_x27___closed__2_once, _init_l_Lean_Fmt_fmtTimes_x27___closed__2);
v___x_746_ = ((lean_object*)(l_Lean_Fmt_fmtTimes___closed__1));
v___x_747_ = 0;
v___x_748_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_745_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*2, v___x_747_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*2 + 1, v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes_x27(void){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_obj_once(&l_Lean_Fmt_fmtTimes_x27___closed__3, &l_Lean_Fmt_fmtTimes_x27___closed__3_once, _init_l_Lean_Fmt_fmtTimes_x27___closed__3);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1(){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_759_ = l_Lean_Fmt_infixFmtAttribute;
v___x_760_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__1));
v___x_761_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__3));
v___x_762_ = l_Lean_Fmt_fmtTimes_x27;
v___x_763_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_759_, v___x_760_, v___x_761_, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___boxed(lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1();
return v_res_765_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPSigmaTimes___closed__0(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_766_ = lean_box(0);
v___x_767_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__1));
v___x_768_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__5, &l_Lean_Fmt_fmtTimes___closed__5_once, _init_l_Lean_Fmt_fmtTimes___closed__5);
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(v___x_768_, v___x_767_, v___x_766_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPSigmaTimes___closed__1(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; 
v___x_770_ = lean_obj_once(&l_Lean_Fmt_fmtPSigmaTimes___closed__0, &l_Lean_Fmt_fmtPSigmaTimes___closed__0_once, _init_l_Lean_Fmt_fmtPSigmaTimes___closed__0);
v___x_771_ = ((lean_object*)(l_Lean_Fmt_fmtSigmaTimes___closed__1));
v___x_772_ = 0;
v___x_773_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_770_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*2, v___x_772_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*2 + 1, v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPSigmaTimes(void){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = lean_obj_once(&l_Lean_Fmt_fmtPSigmaTimes___closed__1, &l_Lean_Fmt_fmtPSigmaTimes___closed__1_once, _init_l_Lean_Fmt_fmtPSigmaTimes___closed__1);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1(){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_781_ = l_Lean_Fmt_infixFmtAttribute;
v___x_782_ = ((lean_object*)(l_Lean_Fmt_fmtTimes_x27___closed__1));
v___x_783_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__1));
v___x_784_ = l_Lean_Fmt_fmtPSigmaTimes;
v___x_785_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_781_, v___x_782_, v___x_783_, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___boxed(lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1();
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSetNotation(lean_object* v_x_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_Fmt_fmtSetNotation___closed__1));
lean_inc(v_x_791_);
v___x_795_ = l_Lean_Syntax_isOfKind(v_x_791_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v_x_791_);
v___x_796_ = l_Lean_Fmt_Error_partialFormatter;
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v_a_793_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; lean_object* v_lbTk_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_rbTk_803_; lean_object* v_elems_804_; lean_object* v___x_805_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v_lbTk_799_ = l_Lean_Syntax_getArg(v_x_791_, v___x_798_);
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = l_Lean_Syntax_getArg(v_x_791_, v___x_800_);
v___x_802_ = lean_unsigned_to_nat(2u);
v_rbTk_803_ = l_Lean_Syntax_getArg(v_x_791_, v___x_802_);
lean_dec(v_x_791_);
v_elems_804_ = l_Lean_Syntax_getArgs(v___x_801_);
lean_dec(v___x_801_);
v___x_805_ = l_Lean_Fmt_fmtArrayLit___redArg(v_lbTk_799_, v_elems_804_, v_rbTk_803_, v_a_792_, v_a_793_);
lean_dec_ref(v_elems_804_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSetNotation___boxed(lean_object* v_x_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Fmt_fmtSetNotation(v_x_806_, v_a_807_, v_a_808_);
lean_dec_ref(v_a_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1(){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_816_ = l_Lean_Fmt_fmtAttribute;
v___x_817_ = ((lean_object*)(l_Lean_Fmt_fmtSetNotation___closed__1));
v___x_818_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__1));
v___x_819_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSetNotation___boxed), 3, 0);
v___x_820_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_816_, v___x_817_, v___x_818_, v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___boxed(lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1();
return v_res_822_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtUnifConstraint___closed__2(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; uint8_t v___x_830_; lean_object* v___x_831_; 
v___x_827_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__5, &l_Lean_Fmt_fmtTimes___closed__5_once, _init_l_Lean_Fmt_fmtTimes___closed__5);
v___x_828_ = ((lean_object*)(l_Lean_Fmt_fmtUnifConstraint___closed__1));
v___x_829_ = 0;
v___x_830_ = 1;
v___x_831_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_831_, 0, v___x_828_);
lean_ctor_set(v___x_831_, 1, v___x_827_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*2, v___x_830_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*2 + 1, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtUnifConstraint(void){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lean_obj_once(&l_Lean_Fmt_fmtUnifConstraint___closed__2, &l_Lean_Fmt_fmtUnifConstraint___closed__2_once, _init_l_Lean_Fmt_fmtUnifConstraint___closed__2);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1(){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_843_ = l_Lean_Fmt_infixFmtAttribute;
v___x_844_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1));
v___x_845_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__3));
v___x_846_ = l_Lean_Fmt_fmtUnifConstraint;
v___x_847_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_843_, v___x_844_, v___x_845_, v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___boxed(lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1();
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4(size_t v_sz_850_, size_t v_i_851_, lean_object* v_bs_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_853_ == 0)
{
return v_bs_852_;
}
else
{
lean_object* v_v_854_; lean_object* v___x_855_; lean_object* v_bs_x27_856_; size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v_v_854_ = lean_array_uget(v_bs_852_, v_i_851_);
v___x_855_ = lean_unsigned_to_nat(0u);
v_bs_x27_856_ = lean_array_uset(v_bs_852_, v_i_851_, v___x_855_);
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_add(v_i_851_, v___x_857_);
v___x_859_ = lean_array_uset(v_bs_x27_856_, v_i_851_, v_v_854_);
v_i_851_ = v___x_858_;
v_bs_852_ = v___x_859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4___boxed(lean_object* v_sz_861_, lean_object* v_i_862_, lean_object* v_bs_863_){
_start:
{
size_t v_sz_boxed_864_; size_t v_i_boxed_865_; lean_object* v_res_866_; 
v_sz_boxed_864_ = lean_unbox_usize(v_sz_861_);
lean_dec(v_sz_861_);
v_i_boxed_865_ = lean_unbox_usize(v_i_862_);
lean_dec(v_i_862_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4(v_sz_boxed_864_, v_i_boxed_865_, v_bs_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2(size_t v_sz_867_, size_t v_i_868_, lean_object* v_bs_869_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = lean_usize_dec_lt(v_i_868_, v_sz_867_);
if (v___x_870_ == 0)
{
return v_bs_869_;
}
else
{
lean_object* v_v_871_; lean_object* v_fst_872_; lean_object* v___x_873_; lean_object* v_bs_x27_874_; size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; 
v_v_871_ = lean_array_uget_borrowed(v_bs_869_, v_i_868_);
v_fst_872_ = lean_ctor_get(v_v_871_, 0);
lean_inc(v_fst_872_);
v___x_873_ = lean_unsigned_to_nat(0u);
v_bs_x27_874_ = lean_array_uset(v_bs_869_, v_i_868_, v___x_873_);
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_add(v_i_868_, v___x_875_);
v___x_877_ = lean_array_uset(v_bs_x27_874_, v_i_868_, v_fst_872_);
v_i_868_ = v___x_876_;
v_bs_869_ = v___x_877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2___boxed(lean_object* v_sz_879_, lean_object* v_i_880_, lean_object* v_bs_881_){
_start:
{
size_t v_sz_boxed_882_; size_t v_i_boxed_883_; lean_object* v_res_884_; 
v_sz_boxed_882_ = lean_unbox_usize(v_sz_879_);
lean_dec(v_sz_879_);
v_i_boxed_883_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_res_884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2(v_sz_boxed_882_, v_i_boxed_883_, v_bs_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1(size_t v_sz_885_, size_t v_i_886_, lean_object* v_bs_887_){
_start:
{
uint8_t v___x_888_; 
v___x_888_ = lean_usize_dec_lt(v_i_886_, v_sz_885_);
if (v___x_888_ == 0)
{
return v_bs_887_;
}
else
{
lean_object* v_v_889_; lean_object* v_snd_890_; lean_object* v___x_891_; lean_object* v_bs_x27_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
v_v_889_ = lean_array_uget_borrowed(v_bs_887_, v_i_886_);
v_snd_890_ = lean_ctor_get(v_v_889_, 1);
lean_inc(v_snd_890_);
v___x_891_ = lean_unsigned_to_nat(0u);
v_bs_x27_892_ = lean_array_uset(v_bs_887_, v_i_886_, v___x_891_);
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_add(v_i_886_, v___x_893_);
v___x_895_ = lean_array_uset(v_bs_x27_892_, v_i_886_, v_snd_890_);
v_i_886_ = v___x_894_;
v_bs_887_ = v___x_895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1___boxed(lean_object* v_sz_897_, lean_object* v_i_898_, lean_object* v_bs_899_){
_start:
{
size_t v_sz_boxed_900_; size_t v_i_boxed_901_; lean_object* v_res_902_; 
v_sz_boxed_900_ = lean_unbox_usize(v_sz_897_);
lean_dec(v_sz_897_);
v_i_boxed_901_ = lean_unbox_usize(v_i_898_);
lean_dec(v_i_898_);
v_res_902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1(v_sz_boxed_900_, v_i_boxed_901_, v_bs_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0(size_t v_sz_907_, size_t v_i_908_, lean_object* v_bs_909_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = lean_usize_dec_lt(v_i_908_, v_sz_907_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v_bs_909_);
return v___x_911_;
}
else
{
lean_object* v_v_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_v_912_ = lean_array_uget(v_bs_909_, v_i_908_);
v___x_913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__1));
lean_inc(v_v_912_);
v___x_914_ = l_Lean_Syntax_isOfKind(v_v_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v_v_912_);
lean_dec_ref(v_bs_909_);
v___x_915_ = lean_box(0);
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v_constraints_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_916_ = lean_unsigned_to_nat(0u);
v_constraints_917_ = l_Lean_Syntax_getArg(v_v_912_, v___x_916_);
v___x_918_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1));
lean_inc(v_constraints_917_);
v___x_919_ = l_Lean_Syntax_isOfKind(v_constraints_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
lean_dec(v_constraints_917_);
lean_dec(v_v_912_);
lean_dec_ref(v_bs_909_);
v___x_920_ = lean_box(0);
return v___x_920_;
}
else
{
lean_object* v___x_921_; lean_object* v_bs_x27_922_; lean_object* v_commaTks_924_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_921_ = lean_unsigned_to_nat(1u);
v_bs_x27_922_ = lean_array_uset(v_bs_909_, v_i_908_, v___x_916_);
v___x_930_ = l_Lean_Syntax_getArg(v_v_912_, v___x_921_);
lean_dec(v_v_912_);
v___x_931_ = l_Lean_Syntax_isNone(v___x_930_);
if (v___x_931_ == 0)
{
uint8_t v___x_932_; 
lean_inc(v___x_930_);
v___x_932_ = l_Lean_Syntax_matchesNull(v___x_930_, v___x_921_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
lean_dec(v___x_930_);
lean_dec_ref(v_bs_x27_922_);
lean_dec(v_constraints_917_);
v___x_933_ = lean_box(0);
return v___x_933_;
}
else
{
lean_object* v_commaTks_934_; lean_object* v___x_935_; 
v_commaTks_934_ = l_Lean_Syntax_getArg(v___x_930_, v___x_916_);
lean_dec(v___x_930_);
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v_commaTks_934_);
v_commaTks_924_ = v___x_935_;
goto v___jp_923_;
}
}
else
{
lean_object* v___x_936_; 
lean_dec(v___x_930_);
v___x_936_ = lean_box(0);
v_commaTks_924_ = v___x_936_;
goto v___jp_923_;
}
v___jp_923_:
{
lean_object* v___x_925_; size_t v___x_926_; size_t v___x_927_; lean_object* v___x_928_; 
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_constraints_917_);
lean_ctor_set(v___x_925_, 1, v_commaTks_924_);
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_908_, v___x_926_);
v___x_928_ = lean_array_uset(v_bs_x27_922_, v_i_908_, v___x_925_);
v_i_908_ = v___x_927_;
v_bs_909_ = v___x_928_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___boxed(lean_object* v_sz_937_, lean_object* v_i_938_, lean_object* v_bs_939_){
_start:
{
size_t v_sz_boxed_940_; size_t v_i_boxed_941_; lean_object* v_res_942_; 
v_sz_boxed_940_ = lean_unbox_usize(v_sz_937_);
lean_dec(v_sz_937_);
v_i_boxed_941_ = lean_unbox_usize(v_i_938_);
lean_dec(v_i_938_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0(v_sz_boxed_940_, v_i_boxed_941_, v_bs_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3(size_t v_sz_943_, size_t v_i_944_, lean_object* v_bs_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_944_, v_sz_943_);
if (v___x_946_ == 0)
{
return v_bs_945_;
}
else
{
lean_object* v_v_947_; lean_object* v___x_948_; lean_object* v_bs_x27_949_; size_t v___x_950_; size_t v___x_951_; lean_object* v___x_952_; 
v_v_947_ = lean_array_uget(v_bs_945_, v_i_944_);
v___x_948_ = lean_unsigned_to_nat(0u);
v_bs_x27_949_ = lean_array_uset(v_bs_945_, v_i_944_, v___x_948_);
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_add(v_i_944_, v___x_950_);
v___x_952_ = lean_array_uset(v_bs_x27_949_, v_i_944_, v_v_947_);
v_i_944_ = v___x_951_;
v_bs_945_ = v___x_952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3___boxed(lean_object* v_sz_954_, lean_object* v_i_955_, lean_object* v_bs_956_){
_start:
{
size_t v_sz_boxed_957_; size_t v_i_boxed_958_; lean_object* v_res_959_; 
v_sz_boxed_957_ = lean_unbox_usize(v_sz_954_);
lean_dec(v_sz_954_);
v_i_boxed_958_ = lean_unbox_usize(v_i_955_);
lean_dec(v_i_955_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3(v_sz_boxed_957_, v_i_boxed_958_, v_bs_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnifHint(lean_object* v_x_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_986_; uint8_t v___x_987_; lean_object* v___y_989_; lean_object* v___y_990_; size_t v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; size_t v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v_declId_x3f_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; 
v___x_986_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__1));
lean_inc(v_x_983_);
v___x_987_ = l_Lean_Syntax_isOfKind(v_x_983_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v_x_983_);
v___x_1125_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v_a_985_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; lean_object* v_docComment_x3f_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1153_ = l_Lean_Syntax_getArg(v_x_983_, v___x_1127_);
v___x_1154_ = l_Lean_Syntax_isNone(v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1153_);
v___x_1156_ = l_Lean_Syntax_matchesNull(v___x_1153_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v___x_1153_);
lean_dec(v_x_983_);
v___x_1157_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v_a_985_);
return v___x_1158_;
}
else
{
lean_object* v_docComment_x3f_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v_docComment_x3f_1159_ = l_Lean_Syntax_getArg(v___x_1153_, v___x_1127_);
lean_dec(v___x_1153_);
v___x_1160_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__11));
lean_inc(v_docComment_x3f_1159_);
v___x_1161_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_1159_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec(v_docComment_x3f_1159_);
lean_dec(v_x_983_);
v___x_1162_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v_a_985_);
return v___x_1163_;
}
else
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_docComment_x3f_1159_);
v_docComment_x3f_1129_ = v___x_1164_;
v___y_1130_ = v_a_984_;
v___y_1131_ = v_a_985_;
goto v___jp_1128_;
}
}
}
else
{
lean_object* v___x_1165_; 
lean_dec(v___x_1153_);
v___x_1165_ = lean_box(0);
v_docComment_x3f_1129_ = v___x_1165_;
v___y_1130_ = v_a_984_;
v___y_1131_ = v_a_985_;
goto v___jp_1128_;
}
v___jp_1128_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = l_Lean_Syntax_getArg(v_x_983_, v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__6));
lean_inc(v___x_1133_);
v___x_1135_ = l_Lean_Syntax_isOfKind(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v___x_1133_);
lean_dec(v_docComment_x3f_1129_);
lean_dec(v_x_983_);
v___x_1136_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___y_1131_);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; lean_object* v_unifHintTk_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1138_ = lean_unsigned_to_nat(2u);
v_unifHintTk_1139_ = l_Lean_Syntax_getArg(v_x_983_, v___x_1138_);
v___x_1140_ = lean_unsigned_to_nat(3u);
v___x_1141_ = l_Lean_Syntax_getArg(v_x_983_, v___x_1140_);
v___x_1142_ = l_Lean_Syntax_isNone(v___x_1141_);
if (v___x_1142_ == 0)
{
uint8_t v___x_1143_; 
lean_inc(v___x_1141_);
v___x_1143_ = l_Lean_Syntax_matchesNull(v___x_1141_, v___x_1132_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v___x_1141_);
lean_dec(v_unifHintTk_1139_);
lean_dec(v___x_1133_);
lean_dec(v_docComment_x3f_1129_);
lean_dec(v_x_983_);
v___x_1144_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v___y_1131_);
return v___x_1145_;
}
else
{
lean_object* v_declId_x3f_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_declId_x3f_1146_ = l_Lean_Syntax_getArg(v___x_1141_, v___x_1127_);
lean_dec(v___x_1141_);
v___x_1147_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__8));
lean_inc(v_declId_x3f_1146_);
v___x_1148_ = l_Lean_Syntax_isOfKind(v_declId_x3f_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v_declId_x3f_1146_);
lean_dec(v_unifHintTk_1139_);
lean_dec(v___x_1133_);
lean_dec(v_docComment_x3f_1129_);
lean_dec(v_x_983_);
v___x_1149_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v___y_1131_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_declId_x3f_1146_);
v___y_1085_ = v_docComment_x3f_1129_;
v___y_1086_ = v___x_1133_;
v___y_1087_ = v___x_1138_;
v___y_1088_ = v_unifHintTk_1139_;
v_declId_x3f_1089_ = v___x_1151_;
v___y_1090_ = v___y_1130_;
v___y_1091_ = v___y_1131_;
goto v___jp_1084_;
}
}
}
else
{
lean_object* v___x_1152_; 
lean_dec(v___x_1141_);
v___x_1152_ = lean_box(0);
v___y_1085_ = v_docComment_x3f_1129_;
v___y_1086_ = v___x_1133_;
v___y_1087_ = v___x_1138_;
v___y_1088_ = v_unifHintTk_1139_;
v_declId_x3f_1089_ = v___x_1152_;
v___y_1090_ = v___y_1130_;
v___y_1091_ = v___y_1131_;
goto v___jp_1084_;
}
}
}
}
v___jp_988_:
{
size_t v_sz_1003_; lean_object* v___x_1004_; size_t v_sz_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_sz_1003_ = lean_array_size(v___y_996_);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3(v_sz_1003_, v___y_991_, v___y_996_);
v_sz_1005_ = lean_array_size(v___x_1004_);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4(v_sz_1005_, v___y_991_, v___x_1004_);
lean_inc_n(v___y_994_, 2);
v___x_1007_ = l_Lean_Fmt_fmtDeclarationSignature(v___y_997_, v___y_994_, v___y_1002_, v___x_1006_, v___y_994_, v___y_994_, v___y_1001_, v___y_995_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v_a_1009_; lean_object* v___x_1010_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
v_a_1009_ = lean_ctor_get(v___x_1007_, 1);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1007_, 2);
v___x_1010_ = l_Lean_Fmt_fmt(v___y_998_, v___y_1001_, v_a_1009_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
v_a_1012_ = lean_ctor_get(v___x_1010_, 1);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1010_, 2);
v___x_1013_ = l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(v___y_989_, v___y_990_);
lean_dec_ref(v___y_990_);
lean_dec_ref(v___y_989_);
v___x_1014_ = l_Lean_Fmt_fmtTSepArray___redArg(v___x_1013_, v___y_1001_, v_a_1012_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
v_a_1016_ = lean_ctor_get(v___x_1014_, 1);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1014_, 2);
v___x_1017_ = l_Lean_Syntax_getArg(v_x_983_, v___y_1000_);
lean_dec(v_x_983_);
v___x_1018_ = l_Lean_Fmt_fmtAtomic(v___x_1017_, v___y_1001_, v_a_1016_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v_a_1020_; lean_object* v___x_1021_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
v_a_1020_ = lean_ctor_get(v___x_1018_, 1);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1018_, 2);
v___x_1021_ = l_Lean_Fmt_fmt(v___y_993_, v___y_1001_, v_a_1020_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1044_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_a_1023_ = lean_ctor_get(v___x_1021_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1025_ = v___x_1021_;
v_isShared_1026_ = v_isSharedCheck_1044_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1044_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1027_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__2));
v___x_1028_ = 0;
v___x_1029_ = l_Lean_Fmt_Layouts_sepLines(v___x_1027_, v_a_1015_, v___x_1028_);
lean_dec(v_a_1015_);
v___x_1030_ = lean_unsigned_to_nat(3u);
v___x_1031_ = lean_mk_empty_array_with_capacity(v___x_1030_);
v___x_1032_ = lean_array_push(v___x_1031_, v___x_1029_);
v___x_1033_ = lean_array_push(v___x_1032_, v_a_1019_);
v___x_1034_ = lean_array_push(v___x_1033_, v_a_1022_);
v___x_1035_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_1034_, v___x_987_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = l_Lean_Fmt_Layouts_whereDeclaration(v_a_1008_, v_a_1011_, v___x_1035_);
v___x_1037_ = lean_mk_empty_array_with_capacity(v___y_999_);
v___x_1038_ = lean_array_push(v___x_1037_, v___y_992_);
v___x_1039_ = lean_array_push(v___x_1038_, v___x_1036_);
v___x_1040_ = l_Lean_Fmt_Layouts_lines(v___x_1039_);
lean_dec_ref(v___x_1039_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1040_);
v___x_1042_ = v___x_1025_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_a_1023_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
lean_dec(v_a_1019_);
lean_dec(v_a_1015_);
lean_dec(v_a_1011_);
lean_dec(v_a_1008_);
lean_dec_ref(v___y_992_);
return v___x_1021_;
}
}
else
{
lean_dec(v_a_1015_);
lean_dec(v_a_1011_);
lean_dec(v_a_1008_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v___x_1018_;
}
}
else
{
lean_object* v_a_1045_; lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v_a_1011_);
lean_dec(v_a_1008_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v_x_983_);
v_a_1045_ = lean_ctor_get(v___x_1014_, 0);
v_a_1046_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1014_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_inc(v_a_1045_);
lean_dec(v___x_1014_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1045_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
lean_dec(v_a_1008_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v_x_983_);
return v___x_1010_;
}
}
else
{
lean_dec(v___y_998_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v_x_983_);
return v___x_1007_;
}
}
v___jp_1054_:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Fmt_fmt_x3f(v___y_1068_, v___y_1067_, v___y_1066_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
v_a_1071_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1069_, 2);
v___x_1072_ = lean_mk_empty_array_with_capacity(v___y_1063_);
v___x_1073_ = lean_array_push(v___x_1072_, v___y_1061_);
v___x_1074_ = lean_array_push(v___x_1073_, v___y_1064_);
v___x_1075_ = lean_box(0);
if (lean_obj_tag(v___y_1055_) == 0)
{
v___y_989_ = v___y_1056_;
v___y_990_ = v___y_1057_;
v___y_991_ = v___y_1058_;
v___y_992_ = v_a_1070_;
v___y_993_ = v___y_1059_;
v___y_994_ = v___x_1075_;
v___y_995_ = v_a_1071_;
v___y_996_ = v___y_1060_;
v___y_997_ = v___x_1074_;
v___y_998_ = v___y_1062_;
v___y_999_ = v___y_1063_;
v___y_1000_ = v___y_1065_;
v___y_1001_ = v___y_1067_;
v___y_1002_ = v___x_1075_;
goto v___jp_988_;
}
else
{
lean_object* v_val_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_val_1076_ = lean_ctor_get(v___y_1055_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___y_1055_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___y_1055_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_val_1076_);
lean_dec(v___y_1055_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_val_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
v___y_989_ = v___y_1056_;
v___y_990_ = v___y_1057_;
v___y_991_ = v___y_1058_;
v___y_992_ = v_a_1070_;
v___y_993_ = v___y_1059_;
v___y_994_ = v___x_1075_;
v___y_995_ = v_a_1071_;
v___y_996_ = v___y_1060_;
v___y_997_ = v___x_1074_;
v___y_998_ = v___y_1062_;
v___y_999_ = v___y_1063_;
v___y_1000_ = v___y_1065_;
v___y_1001_ = v___y_1067_;
v___y_1002_ = v___x_1081_;
goto v___jp_988_;
}
}
}
}
else
{
lean_dec(v___y_1064_);
lean_dec(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec(v_x_983_);
return v___x_1069_;
}
}
v___jp_1084_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; size_t v_sz_1095_; size_t v___x_1096_; lean_object* v___x_1097_; 
v___x_1092_ = lean_unsigned_to_nat(6u);
v___x_1093_ = l_Lean_Syntax_getArg(v_x_983_, v___x_1092_);
v___x_1094_ = l_Lean_Syntax_getArgs(v___x_1093_);
lean_dec(v___x_1093_);
v_sz_1095_ = lean_array_size(v___x_1094_);
v___x_1096_ = ((size_t)0ULL);
v___x_1097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0(v_sz_1095_, v___x_1096_, v___x_1094_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec(v_declId_x3f_1089_);
lean_dec(v___y_1088_);
lean_dec(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec(v_x_983_);
v___x_1098_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___y_1091_);
return v___x_1099_;
}
else
{
lean_object* v_val_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_val_1100_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_val_1100_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1101_ = lean_unsigned_to_nat(8u);
v___x_1102_ = l_Lean_Syntax_getArg(v_x_983_, v___x_1101_);
v___x_1103_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1));
lean_inc(v___x_1102_);
v___x_1104_ = l_Lean_Syntax_isOfKind(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v___x_1102_);
lean_dec(v_val_1100_);
lean_dec(v_declId_x3f_1089_);
lean_dec(v___y_1088_);
lean_dec(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec(v_x_983_);
v___x_1105_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___y_1091_);
return v___x_1106_;
}
else
{
size_t v_sz_1107_; lean_object* v_commaTks_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_whereTk_1112_; lean_object* v_constraints_1113_; lean_object* v___x_1114_; lean_object* v_binders_1115_; 
v_sz_1107_ = lean_array_size(v_val_1100_);
lean_inc(v_val_1100_);
v_commaTks_1108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1(v_sz_1107_, v___x_1096_, v_val_1100_);
v___x_1109_ = lean_unsigned_to_nat(4u);
v___x_1110_ = l_Lean_Syntax_getArg(v_x_983_, v___x_1109_);
v___x_1111_ = lean_unsigned_to_nat(5u);
v_whereTk_1112_ = l_Lean_Syntax_getArg(v_x_983_, v___x_1111_);
v_constraints_1113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2(v_sz_1107_, v___x_1096_, v_val_1100_);
v___x_1114_ = lean_unsigned_to_nat(7u);
v_binders_1115_ = l_Lean_Syntax_getArgs(v___x_1110_);
lean_dec(v___x_1110_);
if (lean_obj_tag(v___y_1085_) == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_box(0);
v___y_1055_ = v_declId_x3f_1089_;
v___y_1056_ = v_constraints_1113_;
v___y_1057_ = v_commaTks_1108_;
v___y_1058_ = v___x_1096_;
v___y_1059_ = v___x_1102_;
v___y_1060_ = v_binders_1115_;
v___y_1061_ = v___y_1086_;
v___y_1062_ = v_whereTk_1112_;
v___y_1063_ = v___y_1087_;
v___y_1064_ = v___y_1088_;
v___y_1065_ = v___x_1114_;
v___y_1066_ = v___y_1091_;
v___y_1067_ = v___y_1090_;
v___y_1068_ = v___x_1116_;
goto v___jp_1054_;
}
else
{
lean_object* v_val_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v_val_1117_ = lean_ctor_get(v___y_1085_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___y_1085_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___y_1085_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_val_1117_);
lean_dec(v___y_1085_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_val_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
v___y_1055_ = v_declId_x3f_1089_;
v___y_1056_ = v_constraints_1113_;
v___y_1057_ = v_commaTks_1108_;
v___y_1058_ = v___x_1096_;
v___y_1059_ = v___x_1102_;
v___y_1060_ = v_binders_1115_;
v___y_1061_ = v___y_1086_;
v___y_1062_ = v_whereTk_1112_;
v___y_1063_ = v___y_1087_;
v___y_1064_ = v___y_1088_;
v___y_1065_ = v___x_1114_;
v___y_1066_ = v___y_1091_;
v___y_1067_ = v___y_1090_;
v___y_1068_ = v___x_1122_;
goto v___jp_1054_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnifHint___boxed(lean_object* v_x_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Fmt_fmtUnifHint(v_x_1166_, v_a_1167_, v_a_1168_);
lean_dec_ref(v_a_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1(){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1176_ = l_Lean_Fmt_fmtAttribute;
v___x_1177_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__1));
v___x_1178_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__1));
v___x_1179_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtUnifHint___boxed), 3, 0);
v___x_1180_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1176_, v___x_1177_, v___x_1178_, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___boxed(lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1();
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0(size_t v_sz_1186_, size_t v_i_1187_, lean_object* v_bs_1188_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_lt(v_i_1187_, v_sz_1186_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_bs_1188_);
return v___x_1190_;
}
else
{
lean_object* v_v_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_v_1191_ = lean_array_uget(v_bs_1188_, v_i_1187_);
v___x_1192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__1));
lean_inc(v_v_1191_);
v___x_1193_ = l_Lean_Syntax_isOfKind(v_v_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec(v_v_1191_);
lean_dec_ref(v_bs_1188_);
v___x_1194_ = lean_box(0);
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v_bs_x27_1197_; lean_object* v_parents_1198_; lean_object* v_commaTks_1200_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = lean_unsigned_to_nat(1u);
v_bs_x27_1197_ = lean_array_uset(v_bs_1188_, v_i_1187_, v___x_1195_);
v_parents_1198_ = l_Lean_Syntax_getArg(v_v_1191_, v___x_1195_);
v___x_1206_ = l_Lean_Syntax_getArg(v_v_1191_, v___x_1196_);
lean_dec(v_v_1191_);
v___x_1207_ = l_Lean_Syntax_isNone(v___x_1206_);
if (v___x_1207_ == 0)
{
uint8_t v___x_1208_; 
lean_inc(v___x_1206_);
v___x_1208_ = l_Lean_Syntax_matchesNull(v___x_1206_, v___x_1196_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_dec(v___x_1206_);
lean_dec(v_parents_1198_);
lean_dec_ref(v_bs_x27_1197_);
v___x_1209_ = lean_box(0);
return v___x_1209_;
}
else
{
lean_object* v_commaTks_1210_; lean_object* v___x_1211_; 
v_commaTks_1210_ = l_Lean_Syntax_getArg(v___x_1206_, v___x_1195_);
lean_dec(v___x_1206_);
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_commaTks_1210_);
v_commaTks_1200_ = v___x_1211_;
goto v___jp_1199_;
}
}
else
{
lean_object* v___x_1212_; 
lean_dec(v___x_1206_);
v___x_1212_ = lean_box(0);
v_commaTks_1200_ = v___x_1212_;
goto v___jp_1199_;
}
v___jp_1199_:
{
lean_object* v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v_parents_1198_);
lean_ctor_set(v___x_1201_, 1, v_commaTks_1200_);
v___x_1202_ = ((size_t)1ULL);
v___x_1203_ = lean_usize_add(v_i_1187_, v___x_1202_);
v___x_1204_ = lean_array_uset(v_bs_x27_1197_, v_i_1187_, v___x_1201_);
v_i_1187_ = v___x_1203_;
v_bs_1188_ = v___x_1204_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___boxed(lean_object* v_sz_1213_, lean_object* v_i_1214_, lean_object* v_bs_1215_){
_start:
{
size_t v_sz_boxed_1216_; size_t v_i_boxed_1217_; lean_object* v_res_1218_; 
v_sz_boxed_1216_ = lean_unbox_usize(v_sz_1213_);
lean_dec(v_sz_1213_);
v_i_boxed_1217_ = lean_unbox_usize(v_i_1214_);
lean_dec(v_i_1214_);
v_res_1218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0(v_sz_boxed_1216_, v_i_boxed_1217_, v_bs_1215_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtClassAbbrev(lean_object* v_x_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = ((lean_object*)(l_Lean_Fmt_fmtClassAbbrev___closed__1));
lean_inc(v_x_1237_);
v___x_1241_ = l_Lean_Syntax_isOfKind(v_x_1237_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_x_1237_);
v___x_1242_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v_a_1239_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; lean_object* v_mods_1245_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1244_ = lean_unsigned_to_nat(0u);
v_mods_1245_ = l_Lean_Syntax_getArg(v_x_1237_, v___x_1244_);
v___x_1282_ = ((lean_object*)(l_Lean_Fmt_fmtClassAbbrev___closed__3));
lean_inc(v_mods_1245_);
v___x_1283_ = l_Lean_Syntax_isOfKind(v_mods_1245_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec(v_mods_1245_);
lean_dec(v_x_1237_);
v___x_1284_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v_a_1239_);
return v___x_1285_;
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1286_ = lean_unsigned_to_nat(3u);
v___x_1287_ = l_Lean_Syntax_getArg(v_x_1237_, v___x_1286_);
v___x_1288_ = ((lean_object*)(l_Lean_Fmt_fmtClassAbbrev___closed__5));
lean_inc(v___x_1287_);
v___x_1289_ = l_Lean_Syntax_isOfKind(v___x_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec(v___x_1287_);
lean_dec(v_mods_1245_);
lean_dec(v_x_1237_);
v___x_1290_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_a_1239_);
return v___x_1291_;
}
else
{
lean_object* v___x_1292_; lean_object* v_classTk_1293_; lean_object* v___x_1294_; lean_object* v_abbrevTk_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v_typeAscriptionTk_x3f_1299_; lean_object* v_type_x3f_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1292_ = lean_unsigned_to_nat(1u);
v_classTk_1293_ = l_Lean_Syntax_getArg(v_x_1237_, v___x_1292_);
v___x_1294_ = lean_unsigned_to_nat(2u);
v_abbrevTk_1295_ = l_Lean_Syntax_getArg(v_x_1237_, v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(4u);
v___x_1297_ = l_Lean_Syntax_getArg(v_x_1237_, v___x_1296_);
v___x_1341_ = lean_unsigned_to_nat(5u);
v___x_1342_ = l_Lean_Syntax_getArg(v_x_1237_, v___x_1341_);
v___x_1343_ = l_Lean_Syntax_isNone(v___x_1342_);
if (v___x_1343_ == 0)
{
uint8_t v___x_1344_; 
lean_inc(v___x_1342_);
v___x_1344_ = l_Lean_Syntax_matchesNull(v___x_1342_, v___x_1294_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v___x_1342_);
lean_dec(v___x_1297_);
lean_dec(v_abbrevTk_1295_);
lean_dec(v_classTk_1293_);
lean_dec(v___x_1287_);
lean_dec(v_mods_1245_);
lean_dec(v_x_1237_);
v___x_1345_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v_a_1239_);
return v___x_1346_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_1347_; lean_object* v_type_x3f_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_typeAscriptionTk_x3f_1347_ = l_Lean_Syntax_getArg(v___x_1342_, v___x_1244_);
v_type_x3f_1348_ = l_Lean_Syntax_getArg(v___x_1342_, v___x_1292_);
lean_dec(v___x_1342_);
v___x_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1349_, 0, v_typeAscriptionTk_x3f_1347_);
v___x_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_type_x3f_1348_);
v_typeAscriptionTk_x3f_1299_ = v___x_1349_;
v_type_x3f_1300_ = v___x_1350_;
v___y_1301_ = v_a_1238_;
v___y_1302_ = v_a_1239_;
goto v___jp_1298_;
}
}
else
{
lean_object* v___x_1351_; 
lean_dec(v___x_1342_);
v___x_1351_ = lean_box(0);
v_typeAscriptionTk_x3f_1299_ = v___x_1351_;
v_type_x3f_1300_ = v___x_1351_;
v___y_1301_ = v_a_1238_;
v___y_1302_ = v_a_1239_;
goto v___jp_1298_;
}
v___jp_1298_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; size_t v_sz_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1303_ = lean_unsigned_to_nat(7u);
v___x_1304_ = l_Lean_Syntax_getArg(v_x_1237_, v___x_1303_);
v___x_1305_ = l_Lean_Syntax_getArgs(v___x_1304_);
lean_dec(v___x_1304_);
v_sz_1306_ = lean_array_size(v___x_1305_);
v___x_1307_ = ((size_t)0ULL);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0(v_sz_1306_, v___x_1307_, v___x_1305_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec(v_type_x3f_1300_);
lean_dec(v_typeAscriptionTk_x3f_1299_);
lean_dec(v___x_1297_);
lean_dec(v_abbrevTk_1295_);
lean_dec(v_classTk_1293_);
lean_dec(v___x_1287_);
lean_dec(v_mods_1245_);
lean_dec(v_x_1237_);
v___x_1309_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___y_1302_);
return v___x_1310_;
}
else
{
lean_object* v_val_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1340_; 
v_val_1311_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1313_ = v___x_1308_;
v_isShared_1314_ = v_isSharedCheck_1340_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_val_1311_);
lean_dec(v___x_1308_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1340_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v_colonEqTk_1316_; size_t v_sz_1317_; lean_object* v_commaTks_1318_; lean_object* v_parents_1319_; lean_object* v_binders_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1315_ = lean_unsigned_to_nat(6u);
v_colonEqTk_1316_ = l_Lean_Syntax_getArg(v_x_1237_, v___x_1315_);
lean_dec(v_x_1237_);
v_sz_1317_ = lean_array_size(v_val_1311_);
lean_inc(v_val_1311_);
v_commaTks_1318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1(v_sz_1317_, v___x_1307_, v_val_1311_);
v_parents_1319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2(v_sz_1317_, v___x_1307_, v_val_1311_);
v_binders_1320_ = l_Lean_Syntax_getArgs(v___x_1297_);
lean_dec(v___x_1297_);
v___x_1321_ = lean_mk_empty_array_with_capacity(v___x_1294_);
v___x_1322_ = lean_array_push(v___x_1321_, v_classTk_1293_);
v___x_1323_ = lean_array_push(v___x_1322_, v_abbrevTk_1295_);
v___x_1324_ = lean_box(0);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1287_);
v___x_1326_ = v___x_1313_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1287_);
v___x_1326_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
size_t v_sz_1327_; lean_object* v___x_1328_; size_t v_sz_1329_; lean_object* v___x_1330_; 
v_sz_1327_ = lean_array_size(v_binders_1320_);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3(v_sz_1327_, v___x_1307_, v_binders_1320_);
v_sz_1329_ = lean_array_size(v___x_1328_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4(v_sz_1329_, v___x_1307_, v___x_1328_);
if (lean_obj_tag(v_type_x3f_1300_) == 0)
{
v___y_1247_ = v___x_1326_;
v___y_1248_ = v_colonEqTk_1316_;
v___y_1249_ = v_parents_1319_;
v___y_1250_ = v___x_1330_;
v___y_1251_ = v_typeAscriptionTk_x3f_1299_;
v___y_1252_ = v___x_1323_;
v___y_1253_ = v___x_1324_;
v___y_1254_ = v___y_1302_;
v___y_1255_ = v_commaTks_1318_;
v___y_1256_ = v___y_1301_;
v___y_1257_ = v___x_1324_;
goto v___jp_1246_;
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
v_val_1331_ = lean_ctor_get(v_type_x3f_1300_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_type_x3f_1300_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v_type_x3f_1300_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_val_1331_);
lean_dec(v_type_x3f_1300_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_val_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
v___y_1247_ = v___x_1326_;
v___y_1248_ = v_colonEqTk_1316_;
v___y_1249_ = v_parents_1319_;
v___y_1250_ = v___x_1330_;
v___y_1251_ = v_typeAscriptionTk_x3f_1299_;
v___y_1252_ = v___x_1323_;
v___y_1253_ = v___x_1324_;
v___y_1254_ = v___y_1302_;
v___y_1255_ = v_commaTks_1318_;
v___y_1256_ = v___y_1301_;
v___y_1257_ = v___x_1336_;
goto v___jp_1246_;
}
}
}
}
}
}
}
}
}
v___jp_1246_:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Fmt_fmtDeclarationSignature(v___y_1252_, v___y_1253_, v___y_1247_, v___y_1250_, v___y_1251_, v___y_1257_, v___y_1256_, v___y_1254_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v_a_1260_; lean_object* v___x_1261_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
v_a_1260_ = lean_ctor_get(v___x_1258_, 1);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1258_, 2);
v___x_1261_ = l_Lean_Fmt_fmt(v___y_1248_, v___y_1256_, v_a_1260_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v_a_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
v_a_1263_ = lean_ctor_get(v___x_1261_, 1);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1261_, 2);
v___x_1264_ = l_Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(v___y_1249_, v___y_1255_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1249_);
v___x_1265_ = l_Lean_Fmt_fmtTSepArray___redArg(v___x_1264_, v___y_1256_, v_a_1263_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
v_a_1267_ = lean_ctor_get(v___x_1265_, 1);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1265_, 2);
v___x_1268_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__2));
v___x_1269_ = l_Lean_Fmt_Layouts_sepFill(v___x_1268_, v_a_1266_);
lean_dec(v_a_1266_);
v___x_1270_ = 0;
v___x_1271_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1259_, v_a_1262_, v___x_1269_, v___x_1270_);
v___x_1272_ = l_Lean_Fmt_fmtDeclWithDeclModifiers(v_mods_1245_, v___x_1271_, v___y_1256_, v_a_1267_);
return v___x_1272_;
}
else
{
lean_object* v_a_1273_; lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v_a_1262_);
lean_dec(v_a_1259_);
lean_dec(v_mods_1245_);
v_a_1273_ = lean_ctor_get(v___x_1265_, 0);
v_a_1274_ = lean_ctor_get(v___x_1265_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1265_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_inc(v_a_1273_);
lean_dec(v___x_1265_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1273_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_dec(v_a_1259_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1249_);
lean_dec(v_mods_1245_);
return v___x_1261_;
}
}
else
{
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v_mods_1245_);
return v___x_1258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtClassAbbrev___boxed(lean_object* v_x_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Fmt_fmtClassAbbrev(v_x_1352_, v_a_1353_, v_a_1354_);
lean_dec_ref(v_a_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1(){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1362_ = l_Lean_Fmt_fmtAttribute;
v___x_1363_ = ((lean_object*)(l_Lean_Fmt_fmtClassAbbrev___closed__1));
v___x_1364_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__1));
v___x_1365_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtClassAbbrev___boxed), 3, 0);
v___x_1366_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1362_, v___x_1363_, v___x_1364_, v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___boxed(lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1();
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFunext(lean_object* v_x_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = ((lean_object*)(l_Lean_Fmt_fmtFunext___closed__1));
lean_inc(v_x_1372_);
v___x_1376_ = l_Lean_Syntax_isOfKind(v_x_1372_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec(v_x_1372_);
v___x_1377_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v_a_1374_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; lean_object* v_funextTk_1380_; lean_object* v___x_1381_; 
v___x_1379_ = lean_unsigned_to_nat(0u);
v_funextTk_1380_ = l_Lean_Syntax_getArg(v_x_1372_, v___x_1379_);
v___x_1381_ = l_Lean_Fmt_fmt(v_funextTk_1380_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_args_1386_; lean_object* v___x_1387_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
v_a_1383_ = lean_ctor_get(v___x_1381_, 1);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1381_, 2);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = l_Lean_Syntax_getArg(v_x_1372_, v___x_1384_);
lean_dec(v_x_1372_);
v_args_1386_ = l_Lean_Syntax_getArgs(v___x_1385_);
lean_dec(v___x_1385_);
v___x_1387_ = l_Lean_Fmt_fmtArray___redArg(v_args_1386_, v_a_1373_, v_a_1383_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1402_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_a_1389_ = lean_ctor_get(v___x_1387_, 1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1391_ = v___x_1387_;
v_isShared_1392_ = v_isSharedCheck_1402_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1402_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1393_ = lean_mk_empty_array_with_capacity(v___x_1384_);
v___x_1394_ = lean_array_push(v___x_1393_, v_a_1382_);
v___x_1395_ = l_Array_append___redArg(v___x_1394_, v_a_1388_);
lean_dec(v_a_1388_);
v___x_1396_ = 0;
v___x_1397_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1397_, 0, v___x_1376_);
lean_ctor_set_uint8(v___x_1397_, 1, v___x_1396_);
lean_ctor_set_uint8(v___x_1397_, 2, v___x_1376_);
lean_ctor_set_uint8(v___x_1397_, 3, v___x_1396_);
v___x_1398_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1395_, v___x_1397_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1398_);
v___x_1400_ = v___x_1391_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_a_1389_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec(v_a_1382_);
v_a_1403_ = lean_ctor_get(v___x_1387_, 0);
v_a_1404_ = lean_ctor_get(v___x_1387_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1387_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_inc(v_a_1403_);
lean_dec(v___x_1387_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1403_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
else
{
lean_dec(v_x_1372_);
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFunext___boxed(lean_object* v_x_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Fmt_fmtFunext(v_x_1412_, v_a_1413_, v_a_1414_);
lean_dec_ref(v_a_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1(){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1422_ = l_Lean_Fmt_fmtAttribute;
v___x_1423_ = ((lean_object*)(l_Lean_Fmt_fmtFunext___closed__1));
v___x_1424_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__1));
v___x_1425_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtFunext___boxed), 3, 0);
v___x_1426_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1422_, v___x_1423_, v___x_1424_, v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___boxed(lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1();
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCdotTactic(lean_object* v_x_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = ((lean_object*)(l_Lean_Fmt_fmtCdotTactic___closed__1));
lean_inc(v_x_1444_);
v___x_1448_ = l_Lean_Syntax_isOfKind(v_x_1444_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec(v_x_1444_);
v___x_1449_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v_a_1446_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Lean_Fmt_fmtCdotTactic___closed__3));
lean_inc(v___x_1452_);
v___x_1454_ = l_Lean_Syntax_isOfKind(v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v___x_1452_);
lean_dec(v_x_1444_);
v___x_1455_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v_a_1446_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1457_);
lean_dec(v_x_1444_);
v___x_1459_ = ((lean_object*)(l_Lean_Fmt_fmtCdotTactic___closed__6));
lean_inc(v___x_1458_);
v___x_1460_ = l_Lean_Syntax_isOfKind(v___x_1458_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec(v___x_1458_);
lean_dec(v___x_1452_);
v___x_1461_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v_a_1446_);
return v___x_1462_;
}
else
{
lean_object* v_cdotTk_1463_; lean_object* v___x_1464_; 
v_cdotTk_1463_ = l_Lean_Syntax_getArg(v___x_1452_, v___x_1451_);
lean_dec(v___x_1452_);
v___x_1464_ = l_Lean_Fmt_fmt(v_cdotTk_1463_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v_a_1466_; lean_object* v___x_1467_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
v_a_1466_ = lean_ctor_get(v___x_1464_, 1);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1464_, 2);
v___x_1467_ = l_Lean_Fmt_fmt(v___x_1458_, v_a_1445_, v_a_1466_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1484_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_a_1469_ = lean_ctor_get(v___x_1467_, 1);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1471_ = v___x_1467_;
v_isShared_1472_ = v_isSharedCheck_1484_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1484_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1473_ = lean_unsigned_to_nat(2u);
v___x_1474_ = lean_mk_empty_array_with_capacity(v___x_1473_);
v___x_1475_ = lean_array_push(v___x_1474_, v_a_1465_);
v___x_1476_ = lean_array_push(v___x_1475_, v_a_1468_);
v___x_1477_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v___x_1476_);
lean_dec_ref(v___x_1476_);
v___x_1478_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1477_);
v___x_1479_ = 0;
v___x_1480_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_1478_, v___x_1479_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1480_);
v___x_1482_ = v___x_1471_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_a_1469_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
else
{
lean_dec(v_a_1465_);
return v___x_1467_;
}
}
else
{
lean_dec(v___x_1458_);
return v___x_1464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCdotTactic___boxed(lean_object* v_x_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Fmt_fmtCdotTactic(v_x_1485_, v_a_1486_, v_a_1487_);
lean_dec_ref(v_a_1486_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1(){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1495_ = l_Lean_Fmt_fmtAttribute;
v___x_1496_ = ((lean_object*)(l_Lean_Fmt_fmtCdotTactic___closed__1));
v___x_1497_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__1));
v___x_1498_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCdotTactic___boxed), 3, 0);
v___x_1499_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1495_, v___x_1496_, v___x_1497_, v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___boxed(lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1();
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__1(size_t v_sz_1502_, size_t v_i_1503_, lean_object* v_bs_1504_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_usize_dec_lt(v_i_1503_, v_sz_1502_);
if (v___x_1505_ == 0)
{
return v_bs_1504_;
}
else
{
lean_object* v_v_1506_; lean_object* v_snd_1507_; lean_object* v___x_1508_; lean_object* v_bs_x27_1509_; size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v_v_1506_ = lean_array_uget_borrowed(v_bs_1504_, v_i_1503_);
v_snd_1507_ = lean_ctor_get(v_v_1506_, 1);
lean_inc(v_snd_1507_);
v___x_1508_ = lean_unsigned_to_nat(0u);
v_bs_x27_1509_ = lean_array_uset(v_bs_1504_, v_i_1503_, v___x_1508_);
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1503_, v___x_1510_);
v___x_1512_ = lean_array_uset(v_bs_x27_1509_, v_i_1503_, v_snd_1507_);
v_i_1503_ = v___x_1511_;
v_bs_1504_ = v___x_1512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__1___boxed(lean_object* v_sz_1514_, lean_object* v_i_1515_, lean_object* v_bs_1516_){
_start:
{
size_t v_sz_boxed_1517_; size_t v_i_boxed_1518_; lean_object* v_res_1519_; 
v_sz_boxed_1517_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_i_boxed_1518_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_res_1519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__1(v_sz_boxed_1517_, v_i_boxed_1518_, v_bs_1516_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__0(size_t v_sz_1520_, size_t v_i_1521_, lean_object* v_bs_1522_){
_start:
{
uint8_t v___x_1523_; 
v___x_1523_ = lean_usize_dec_lt(v_i_1521_, v_sz_1520_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_bs_1522_);
return v___x_1524_;
}
else
{
lean_object* v_v_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v_v_1525_ = lean_array_uget(v_bs_1522_, v_i_1521_);
v___x_1526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__1));
lean_inc(v_v_1525_);
v___x_1527_ = l_Lean_Syntax_isOfKind(v_v_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_dec(v_v_1525_);
lean_dec_ref(v_bs_1522_);
v___x_1528_ = lean_box(0);
return v___x_1528_;
}
else
{
lean_object* v___x_1529_; lean_object* v_tacticSeqs_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1529_ = lean_unsigned_to_nat(1u);
v_tacticSeqs_1530_ = l_Lean_Syntax_getArg(v_v_1525_, v___x_1529_);
v___x_1531_ = ((lean_object*)(l_Lean_Fmt_fmtCdotTactic___closed__6));
lean_inc(v_tacticSeqs_1530_);
v___x_1532_ = l_Lean_Syntax_isOfKind(v_tacticSeqs_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_dec(v_tacticSeqs_1530_);
lean_dec(v_v_1525_);
lean_dec_ref(v_bs_1522_);
v___x_1533_ = lean_box(0);
return v___x_1533_;
}
else
{
lean_object* v___x_1534_; lean_object* v_bs_x27_1535_; lean_object* v_barTks_1536_; lean_object* v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1534_ = lean_unsigned_to_nat(0u);
v_bs_x27_1535_ = lean_array_uset(v_bs_1522_, v_i_1521_, v___x_1534_);
v_barTks_1536_ = l_Lean_Syntax_getArg(v_v_1525_, v___x_1534_);
lean_dec(v_v_1525_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_barTks_1536_);
lean_ctor_set(v___x_1537_, 1, v_tacticSeqs_1530_);
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1521_, v___x_1538_);
v___x_1540_ = lean_array_uset(v_bs_x27_1535_, v_i_1521_, v___x_1537_);
v_i_1521_ = v___x_1539_;
v_bs_1522_ = v___x_1540_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__0___boxed(lean_object* v_sz_1542_, lean_object* v_i_1543_, lean_object* v_bs_1544_){
_start:
{
size_t v_sz_boxed_1545_; size_t v_i_boxed_1546_; lean_object* v_res_1547_; 
v_sz_boxed_1545_ = lean_unbox_usize(v_sz_1542_);
lean_dec(v_sz_1542_);
v_i_boxed_1546_ = lean_unbox_usize(v_i_1543_);
lean_dec(v_i_1543_);
v_res_1547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__0(v_sz_boxed_1545_, v_i_boxed_1546_, v_bs_1544_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__2(size_t v_sz_1548_, size_t v_i_1549_, lean_object* v_bs_1550_){
_start:
{
uint8_t v___x_1551_; 
v___x_1551_ = lean_usize_dec_lt(v_i_1549_, v_sz_1548_);
if (v___x_1551_ == 0)
{
return v_bs_1550_;
}
else
{
lean_object* v_v_1552_; lean_object* v_fst_1553_; lean_object* v___x_1554_; lean_object* v_bs_x27_1555_; size_t v___x_1556_; size_t v___x_1557_; lean_object* v___x_1558_; 
v_v_1552_ = lean_array_uget_borrowed(v_bs_1550_, v_i_1549_);
v_fst_1553_ = lean_ctor_get(v_v_1552_, 0);
lean_inc(v_fst_1553_);
v___x_1554_ = lean_unsigned_to_nat(0u);
v_bs_x27_1555_ = lean_array_uset(v_bs_1550_, v_i_1549_, v___x_1554_);
v___x_1556_ = ((size_t)1ULL);
v___x_1557_ = lean_usize_add(v_i_1549_, v___x_1556_);
v___x_1558_ = lean_array_uset(v_bs_x27_1555_, v_i_1549_, v_fst_1553_);
v_i_1549_ = v___x_1557_;
v_bs_1550_ = v___x_1558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__2___boxed(lean_object* v_sz_1560_, lean_object* v_i_1561_, lean_object* v_bs_1562_){
_start:
{
size_t v_sz_boxed_1563_; size_t v_i_boxed_1564_; lean_object* v_res_1565_; 
v_sz_boxed_1563_ = lean_unbox_usize(v_sz_1560_);
lean_dec(v_sz_1560_);
v_i_boxed_1564_ = lean_unbox_usize(v_i_1561_);
lean_dec(v_i_1561_);
v_res_1565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__2(v_sz_boxed_1563_, v_i_boxed_1564_, v_bs_1562_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSolve(lean_object* v_x_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_Fmt_fmtSolve___closed__1));
lean_inc(v_x_1570_);
v___x_1574_ = l_Lean_Syntax_isOfKind(v_x_1570_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec(v_x_1570_);
v___x_1575_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v_a_1572_);
return v___x_1576_;
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; size_t v_sz_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v___x_1577_ = lean_unsigned_to_nat(1u);
v___x_1578_ = l_Lean_Syntax_getArg(v_x_1570_, v___x_1577_);
v___x_1579_ = l_Lean_Syntax_getArgs(v___x_1578_);
lean_dec(v___x_1578_);
v_sz_1580_ = lean_array_size(v___x_1579_);
v___x_1581_ = ((size_t)0ULL);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__0(v_sz_1580_, v___x_1581_, v___x_1579_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v_x_1570_);
v___x_1583_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_a_1572_);
return v___x_1584_;
}
else
{
lean_object* v_val_1585_; lean_object* v___x_1586_; lean_object* v_solveTk_1587_; size_t v_sz_1588_; lean_object* v_tacticSeqs_1589_; lean_object* v_barTks_1590_; lean_object* v___x_1591_; 
v_val_1585_ = lean_ctor_get(v___x_1582_, 0);
lean_inc_n(v_val_1585_, 2);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1586_ = lean_unsigned_to_nat(0u);
v_solveTk_1587_ = l_Lean_Syntax_getArg(v_x_1570_, v___x_1586_);
lean_dec(v_x_1570_);
v_sz_1588_ = lean_array_size(v_val_1585_);
v_tacticSeqs_1589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__1(v_sz_1588_, v___x_1581_, v_val_1585_);
v_barTks_1590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__2(v_sz_1588_, v___x_1581_, v_val_1585_);
v___x_1591_ = l_Lean_Fmt_fmtAltsTactic___redArg(v_solveTk_1587_, v_barTks_1590_, v_tacticSeqs_1589_, v_a_1571_, v_a_1572_);
lean_dec_ref(v_tacticSeqs_1589_);
lean_dec_ref(v_barTks_1590_);
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSolve___boxed(lean_object* v_x_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Fmt_fmtSolve(v_x_1592_, v_a_1593_, v_a_1594_);
lean_dec_ref(v_a_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1(){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1602_ = l_Lean_Fmt_fmtAttribute;
v___x_1603_ = ((lean_object*)(l_Lean_Fmt_fmtSolve___closed__1));
v___x_1604_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__1));
v___x_1605_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSolve___boxed), 3, 0);
v___x_1606_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1602_, v___x_1603_, v___x_1604_, v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___boxed(lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1();
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStepLike(lean_object* v_pred_1609_, lean_object* v_colonEqTk_x3f_1610_, lean_object* v_proof_x3f_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Fmt_fmt_x3f(v_colonEqTk_x3f_1610_, v_a_1612_, v_a_1613_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v_a_1616_; lean_object* v___x_1617_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
v_a_1616_ = lean_ctor_get(v___x_1614_, 1);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1614_, 2);
v___x_1617_ = l_Lean_Fmt_fmt_x3f(v_proof_x3f_1611_, v_a_1612_, v_a_1616_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v_a_1619_; uint8_t v___x_1620_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
v_a_1619_ = lean_ctor_get(v___x_1617_, 1);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1617_, 2);
v___x_1620_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1615_);
if (v___x_1620_ == 0)
{
uint8_t v___x_1621_; 
v___x_1621_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1618_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1622_ = l_Lean_Syntax_getArgs(v_pred_1609_);
v___x_1623_ = lean_array_get_size(v___x_1622_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = lean_unsigned_to_nat(3u);
v___x_1625_ = lean_nat_dec_eq(v___x_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Fmt_fmt(v_pred_1609_, v_a_1612_, v_a_1619_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1636_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_a_1628_ = lean_ctor_get(v___x_1626_, 1);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1630_ = v___x_1626_;
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1632_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1627_, v_a_1615_, v_a_1618_, v___x_1621_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1632_);
v___x_1634_ = v___x_1630_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_a_1628_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_dec(v_a_1618_);
lean_dec(v_a_1615_);
return v___x_1626_;
}
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = l_Lean_Syntax_getArg(v_pred_1609_, v___x_1637_);
v___x_1639_ = l_Lean_Fmt_fmt(v___x_1638_, v_a_1612_, v_a_1619_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v_a_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
v_a_1641_ = lean_ctor_get(v___x_1639_, 1);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1639_, 2);
v___x_1642_ = lean_unsigned_to_nat(1u);
v___x_1643_ = l_Lean_Syntax_getArg(v_pred_1609_, v___x_1642_);
v___x_1644_ = l_Lean_Fmt_fmt(v___x_1643_, v_a_1612_, v_a_1641_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
v_a_1646_ = lean_ctor_get(v___x_1644_, 1);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1644_, 2);
v___x_1647_ = lean_unsigned_to_nat(2u);
v___x_1648_ = l_Lean_Syntax_getArg(v_pred_1609_, v___x_1647_);
lean_dec(v_pred_1609_);
v___x_1649_ = l_Lean_Fmt_fmt(v___x_1648_, v_a_1612_, v_a_1646_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1683_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_a_1651_ = lean_ctor_get(v___x_1649_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1653_ = v___x_1649_;
v_isShared_1654_ = v_isSharedCheck_1683_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1683_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
lean_inc(v_a_1650_);
v___x_1655_ = l_Lean_Fmt_TaggedDoc_flattened(v_a_1650_);
v___x_1656_ = lean_mk_empty_array_with_capacity(v___x_1624_);
lean_inc_ref(v___x_1656_);
v___x_1657_ = lean_array_push(v___x_1656_, v_a_1640_);
v___x_1658_ = lean_array_push(v___x_1657_, v_a_1645_);
lean_inc_ref(v___x_1658_);
v___x_1659_ = lean_array_push(v___x_1658_, v___x_1655_);
v___x_1660_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_1660_, 0, v___x_1625_);
lean_ctor_set_uint8(v___x_1660_, 1, v___x_1621_);
lean_ctor_set_uint8(v___x_1660_, 2, v___x_1625_);
lean_ctor_set_uint8(v___x_1660_, 3, v___x_1625_);
lean_ctor_set_uint8(v___x_1660_, 4, v___x_1621_);
v___x_1661_ = l_Lean_Fmt_Layouts_infixOperator(v___x_1659_, v___x_1660_);
lean_dec_ref_known(v___x_1660_, 0);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
v___x_1663_ = lean_obj_once(&l_Lean_Fmt_fmtTermMatches___closed__4, &l_Lean_Fmt_fmtTermMatches___closed__4_once, _init_l_Lean_Fmt_fmtTermMatches___closed__4);
v___x_1664_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1662_, v___x_1663_);
lean_inc(v_a_1615_);
v___x_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_a_1615_);
v___x_1666_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1665_, v___x_1663_);
v___x_1667_ = lean_box(0);
lean_inc(v_a_1618_);
v___x_1668_ = l_Lean_Fmt_TaggedDoc_flattened(v_a_1618_);
v___x_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1667_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
lean_ctor_set(v___x_1670_, 2, v___x_1667_);
v___x_1671_ = lean_array_push(v___x_1656_, v___x_1664_);
v___x_1672_ = lean_array_push(v___x_1671_, v___x_1666_);
v___x_1673_ = lean_array_push(v___x_1672_, v___x_1670_);
v___x_1674_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1673_);
lean_dec_ref(v___x_1673_);
v___x_1675_ = lean_array_push(v___x_1658_, v_a_1650_);
v___x_1676_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_1676_, 0, v___x_1625_);
lean_ctor_set_uint8(v___x_1676_, 1, v___x_1621_);
lean_ctor_set_uint8(v___x_1676_, 2, v___x_1625_);
lean_ctor_set_uint8(v___x_1676_, 3, v___x_1621_);
lean_ctor_set_uint8(v___x_1676_, 4, v___x_1621_);
v___x_1677_ = l_Lean_Fmt_Layouts_infixOperator(v___x_1675_, v___x_1676_);
lean_dec_ref_known(v___x_1676_, 0);
v___x_1678_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_1677_, v_a_1615_, v_a_1618_, v___x_1621_);
v___x_1679_ = l_Lean_Fmt_TaggedDoc_fallbackOnOverflow(v___x_1674_, v___x_1678_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1679_);
v___x_1681_ = v___x_1653_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_a_1651_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
else
{
lean_dec(v_a_1645_);
lean_dec(v_a_1640_);
lean_dec(v_a_1618_);
lean_dec(v_a_1615_);
return v___x_1649_;
}
}
else
{
lean_dec(v_a_1640_);
lean_dec(v_a_1618_);
lean_dec(v_a_1615_);
lean_dec(v_pred_1609_);
return v___x_1644_;
}
}
else
{
lean_dec(v_a_1618_);
lean_dec(v_a_1615_);
lean_dec(v_pred_1609_);
return v___x_1639_;
}
}
}
else
{
lean_object* v___x_1684_; 
lean_dec(v_a_1618_);
lean_dec(v_a_1615_);
v___x_1684_ = l_Lean_Fmt_fmt(v_pred_1609_, v_a_1612_, v_a_1619_);
return v___x_1684_;
}
}
else
{
lean_object* v___x_1685_; 
lean_dec(v_a_1618_);
lean_dec(v_a_1615_);
v___x_1685_ = l_Lean_Fmt_fmt(v_pred_1609_, v_a_1612_, v_a_1619_);
return v___x_1685_;
}
}
else
{
lean_dec(v_a_1615_);
lean_dec(v_pred_1609_);
return v___x_1617_;
}
}
else
{
lean_dec(v_proof_x3f_1611_);
lean_dec(v_pred_1609_);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStepLike___boxed(lean_object* v_pred_1686_, lean_object* v_colonEqTk_x3f_1687_, lean_object* v_proof_x3f_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Fmt_fmtCalcStepLike(v_pred_1686_, v_colonEqTk_x3f_1687_, v_proof_x3f_1688_, v_a_1689_, v_a_1690_);
lean_dec_ref(v_a_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcFirstStep(lean_object* v_x_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1699_ = ((lean_object*)(l_Lean_Fmt_fmtCalcFirstStep___closed__1));
lean_inc(v_x_1696_);
v___x_1700_ = l_Lean_Syntax_isOfKind(v_x_1696_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec(v_x_1696_);
v___x_1701_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v_a_1698_);
return v___x_1702_;
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1703_ = lean_unsigned_to_nat(0u);
v___x_1704_ = l_Lean_Syntax_getArg(v_x_1696_, v___x_1703_);
v___x_1705_ = lean_unsigned_to_nat(1u);
v___x_1706_ = l_Lean_Syntax_getArg(v_x_1696_, v___x_1705_);
lean_dec(v_x_1696_);
v___x_1707_ = l_Lean_Syntax_isNone(v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1706_);
v___x_1709_ = l_Lean_Syntax_matchesNull(v___x_1706_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec(v___x_1706_);
lean_dec(v___x_1704_);
v___x_1710_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v_a_1698_);
return v___x_1711_;
}
else
{
lean_object* v_colonEqTk_x3f_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_colonEqTk_x3f_1712_ = l_Lean_Syntax_getArg(v___x_1706_, v___x_1703_);
v___x_1713_ = l_Lean_Syntax_getArg(v___x_1706_, v___x_1705_);
lean_dec(v___x_1706_);
v___x_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_colonEqTk_x3f_1712_);
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
v___x_1716_ = l_Lean_Fmt_fmtCalcStepLike(v___x_1704_, v___x_1714_, v___x_1715_, v_a_1697_, v_a_1698_);
return v___x_1716_;
}
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec(v___x_1706_);
v___x_1717_ = lean_box(0);
v___x_1718_ = l_Lean_Fmt_fmtCalcStepLike(v___x_1704_, v___x_1717_, v___x_1717_, v_a_1697_, v_a_1698_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcFirstStep___boxed(lean_object* v_x_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Fmt_fmtCalcFirstStep(v_x_1719_, v_a_1720_, v_a_1721_);
lean_dec_ref(v_a_1720_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1(){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1729_ = l_Lean_Fmt_fmtAttribute;
v___x_1730_ = ((lean_object*)(l_Lean_Fmt_fmtCalcFirstStep___closed__1));
v___x_1731_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__1));
v___x_1732_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCalcFirstStep___boxed), 3, 0);
v___x_1733_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1729_, v___x_1730_, v___x_1731_, v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___boxed(lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1();
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStep(lean_object* v_x_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = ((lean_object*)(l_Lean_Fmt_fmtCalcStep___closed__1));
lean_inc(v_x_1740_);
v___x_1744_ = l_Lean_Syntax_isOfKind(v_x_1740_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec(v_x_1740_);
v___x_1745_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v_a_1742_);
return v___x_1746_;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v_colonEqTk_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = l_Lean_Syntax_getArg(v_x_1740_, v___x_1747_);
v___x_1749_ = lean_unsigned_to_nat(1u);
v_colonEqTk_1750_ = l_Lean_Syntax_getArg(v_x_1740_, v___x_1749_);
v___x_1751_ = lean_unsigned_to_nat(2u);
v___x_1752_ = l_Lean_Syntax_getArg(v_x_1740_, v___x_1751_);
lean_dec(v_x_1740_);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_colonEqTk_1750_);
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
v___x_1755_ = l_Lean_Fmt_fmtCalcStepLike(v___x_1748_, v___x_1753_, v___x_1754_, v_a_1741_, v_a_1742_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStep___boxed(lean_object* v_x_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Fmt_fmtCalcStep(v_x_1756_, v_a_1757_, v_a_1758_);
lean_dec_ref(v_a_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1(){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1766_ = l_Lean_Fmt_fmtAttribute;
v___x_1767_ = ((lean_object*)(l_Lean_Fmt_fmtCalcStep___closed__1));
v___x_1768_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__1));
v___x_1769_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCalcStep___boxed), 3, 0);
v___x_1770_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1766_, v___x_1767_, v___x_1768_, v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___boxed(lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1();
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCalcSteps_spec__0(size_t v_sz_1773_, size_t v_i_1774_, lean_object* v_bs_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
uint8_t v___x_1778_; 
v___x_1778_ = lean_usize_dec_lt(v_i_1774_, v_sz_1773_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_bs_1775_);
lean_ctor_set(v___x_1779_, 1, v___y_1777_);
return v___x_1779_;
}
else
{
lean_object* v_v_1780_; lean_object* v___x_1781_; 
v_v_1780_ = lean_array_uget_borrowed(v_bs_1775_, v_i_1774_);
lean_inc(v_v_1780_);
v___x_1781_ = l_Lean_Fmt_fmt(v_v_1780_, v___y_1776_, v___y_1777_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v_a_1783_; lean_object* v___x_1784_; lean_object* v_bs_x27_1785_; size_t v___x_1786_; size_t v___x_1787_; lean_object* v___x_1788_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
v_a_1783_ = lean_ctor_get(v___x_1781_, 1);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1781_, 2);
v___x_1784_ = lean_unsigned_to_nat(0u);
v_bs_x27_1785_ = lean_array_uset(v_bs_1775_, v_i_1774_, v___x_1784_);
v___x_1786_ = ((size_t)1ULL);
v___x_1787_ = lean_usize_add(v_i_1774_, v___x_1786_);
v___x_1788_ = lean_array_uset(v_bs_x27_1785_, v_i_1774_, v_a_1782_);
v_i_1774_ = v___x_1787_;
v_bs_1775_ = v___x_1788_;
v___y_1777_ = v_a_1783_;
goto _start;
}
else
{
lean_object* v_a_1790_; lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec_ref(v_bs_1775_);
v_a_1790_ = lean_ctor_get(v___x_1781_, 0);
v_a_1791_ = lean_ctor_get(v___x_1781_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1781_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_inc(v_a_1790_);
lean_dec(v___x_1781_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1790_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCalcSteps_spec__0___boxed(lean_object* v_sz_1799_, lean_object* v_i_1800_, lean_object* v_bs_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
size_t v_sz_boxed_1804_; size_t v_i_boxed_1805_; lean_object* v_res_1806_; 
v_sz_boxed_1804_ = lean_unbox_usize(v_sz_1799_);
lean_dec(v_sz_1799_);
v_i_boxed_1805_ = lean_unbox_usize(v_i_1800_);
lean_dec(v_i_1800_);
v_res_1806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCalcSteps_spec__0(v_sz_boxed_1804_, v_i_boxed_1805_, v_bs_1801_, v___y_1802_, v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcSteps(lean_object* v_calcSteps_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = l_Lean_Fmt_getStxArg_x21___redArg(v_calcSteps_1807_, v___x_1810_, v_a_1809_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v_a_1813_; lean_object* v___x_1814_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
v_a_1813_ = lean_ctor_get(v___x_1811_, 1);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1811_, 2);
v___x_1814_ = l_Lean_Fmt_fmt(v_a_1812_, v_a_1808_, v_a_1813_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v_a_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
v_a_1816_ = lean_ctor_get(v___x_1814_, 1);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1814_, 2);
v___x_1817_ = lean_unsigned_to_nat(1u);
v___x_1818_ = l_Lean_Fmt_getStxArg_x21___redArg(v_calcSteps_1807_, v___x_1817_, v_a_1816_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v_a_1820_; lean_object* v___x_1821_; size_t v_sz_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
v_a_1820_ = lean_ctor_get(v___x_1818_, 1);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1818_, 2);
v___x_1821_ = l_Lean_Syntax_getArgs(v_a_1819_);
lean_dec(v_a_1819_);
v_sz_1822_ = lean_array_size(v___x_1821_);
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCalcSteps_spec__0(v_sz_1822_, v___x_1823_, v___x_1821_, v_a_1808_, v_a_1820_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1836_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_a_1826_ = lean_ctor_get(v___x_1824_, 1);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1828_ = v___x_1824_;
v_isShared_1829_ = v_isSharedCheck_1836_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1836_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1830_ = lean_mk_empty_array_with_capacity(v___x_1817_);
v___x_1831_ = lean_array_push(v___x_1830_, v_a_1815_);
v___x_1832_ = l_Array_append___redArg(v___x_1831_, v_a_1825_);
lean_dec(v_a_1825_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1832_);
v___x_1834_ = v___x_1828_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_a_1826_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
else
{
lean_dec(v_a_1815_);
return v___x_1824_;
}
}
else
{
lean_object* v_a_1837_; lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_a_1815_);
v_a_1837_ = lean_ctor_get(v___x_1818_, 0);
v_a_1838_ = lean_ctor_get(v___x_1818_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1818_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_inc(v_a_1837_);
lean_dec(v___x_1818_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1837_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1846_ = lean_ctor_get(v___x_1814_, 0);
v_a_1847_ = lean_ctor_get(v___x_1814_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1814_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_inc(v_a_1846_);
lean_dec(v___x_1814_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1846_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_a_1855_ = lean_ctor_get(v___x_1811_, 0);
v_a_1856_ = lean_ctor_get(v___x_1811_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1811_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_inc(v_a_1855_);
lean_dec(v___x_1811_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1855_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_a_1856_);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcSteps___boxed(lean_object* v_calcSteps_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_Fmt_fmtCalcSteps(v_calcSteps_1864_, v_a_1865_, v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_calcSteps_1864_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalc(lean_object* v_calcTk_1868_, lean_object* v_calcSteps_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_Fmt_fmt(v_calcTk_1868_, v_a_1870_, v_a_1871_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v_a_1874_; lean_object* v___x_1875_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
v_a_1874_ = lean_ctor_get(v___x_1872_, 1);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1872_, 2);
v___x_1875_ = l_Lean_Fmt_fmtCalcSteps(v_calcSteps_1869_, v_a_1870_, v_a_1874_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1888_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_a_1877_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1879_ = v___x_1875_;
v_isShared_1880_ = v_isSharedCheck_1888_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1888_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1881_ = l_Lean_Fmt_Layouts_lines(v_a_1876_);
lean_dec(v_a_1876_);
v___x_1882_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_1881_);
v___x_1883_ = 1;
v___x_1884_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_1873_, v___x_1882_, v___x_1883_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1884_);
v___x_1886_ = v___x_1879_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_a_1877_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_a_1873_);
v_a_1889_ = lean_ctor_get(v___x_1875_, 0);
v_a_1890_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1875_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_inc(v_a_1889_);
lean_dec(v___x_1875_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1889_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalc___boxed(lean_object* v_calcTk_1898_, lean_object* v_calcSteps_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Fmt_fmtCalc(v_calcTk_1898_, v_calcSteps_1899_, v_a_1900_, v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_calcSteps_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTerm(lean_object* v_x_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTerm___closed__1));
lean_inc(v_x_1911_);
v___x_1915_ = l_Lean_Syntax_isOfKind(v_x_1911_, v___x_1914_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec(v_x_1911_);
v___x_1916_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v_a_1913_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; lean_object* v_steps_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1918_ = lean_unsigned_to_nat(1u);
v_steps_1919_ = l_Lean_Syntax_getArg(v_x_1911_, v___x_1918_);
v___x_1920_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTerm___closed__3));
lean_inc(v_steps_1919_);
v___x_1921_ = l_Lean_Syntax_isOfKind(v_steps_1919_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_dec(v_steps_1919_);
lean_dec(v_x_1911_);
v___x_1922_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v_a_1913_);
return v___x_1923_;
}
else
{
lean_object* v___x_1924_; lean_object* v_calcTk_1925_; lean_object* v___x_1926_; 
v___x_1924_ = lean_unsigned_to_nat(0u);
v_calcTk_1925_ = l_Lean_Syntax_getArg(v_x_1911_, v___x_1924_);
lean_dec(v_x_1911_);
v___x_1926_ = l_Lean_Fmt_fmtCalc(v_calcTk_1925_, v_steps_1919_, v_a_1912_, v_a_1913_);
lean_dec(v_steps_1919_);
return v___x_1926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTerm___boxed(lean_object* v_x_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_Fmt_fmtCalcTerm(v_x_1927_, v_a_1928_, v_a_1929_);
lean_dec_ref(v_a_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1(){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1937_ = l_Lean_Fmt_fmtAttribute;
v___x_1938_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTerm___closed__1));
v___x_1939_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__1));
v___x_1940_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCalcTerm___boxed), 3, 0);
v___x_1941_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1937_, v___x_1938_, v___x_1939_, v___x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___boxed(lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1();
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTactic(lean_object* v_x_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTactic___closed__1));
lean_inc(v_x_1948_);
v___x_1952_ = l_Lean_Syntax_isOfKind(v_x_1948_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec(v_x_1948_);
v___x_1953_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v_a_1950_);
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; lean_object* v_steps_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1955_ = lean_unsigned_to_nat(1u);
v_steps_1956_ = l_Lean_Syntax_getArg(v_x_1948_, v___x_1955_);
v___x_1957_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTerm___closed__3));
lean_inc(v_steps_1956_);
v___x_1958_ = l_Lean_Syntax_isOfKind(v_steps_1956_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
lean_dec(v_steps_1956_);
lean_dec(v_x_1948_);
v___x_1959_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v_a_1950_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v_calcTk_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_unsigned_to_nat(0u);
v_calcTk_1962_ = l_Lean_Syntax_getArg(v_x_1948_, v___x_1961_);
lean_dec(v_x_1948_);
v___x_1963_ = l_Lean_Fmt_fmtCalc(v_calcTk_1962_, v_steps_1956_, v_a_1949_, v_a_1950_);
lean_dec(v_steps_1956_);
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTactic___boxed(lean_object* v_x_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Fmt_fmtCalcTactic(v_x_1964_, v_a_1965_, v_a_1966_);
lean_dec_ref(v_a_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1(){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1974_ = l_Lean_Fmt_fmtAttribute;
v___x_1975_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTactic___closed__1));
v___x_1976_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__1));
v___x_1977_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCalcTactic___boxed), 3, 0);
v___x_1978_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1974_, v___x_1975_, v___x_1976_, v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___boxed(lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1();
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCalc(lean_object* v_x_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Fmt_fmtConvCalc___closed__1));
lean_inc(v_x_1985_);
v___x_1989_ = l_Lean_Syntax_isOfKind(v_x_1985_, v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec(v_x_1985_);
v___x_1990_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v_a_1987_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v_steps_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1992_ = lean_unsigned_to_nat(1u);
v_steps_1993_ = l_Lean_Syntax_getArg(v_x_1985_, v___x_1992_);
v___x_1994_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTerm___closed__3));
lean_inc(v_steps_1993_);
v___x_1995_ = l_Lean_Syntax_isOfKind(v_steps_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_dec(v_steps_1993_);
lean_dec(v_x_1985_);
v___x_1996_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_a_1987_);
return v___x_1997_;
}
else
{
lean_object* v___x_1998_; lean_object* v_calcTk_1999_; lean_object* v___x_2000_; 
v___x_1998_ = lean_unsigned_to_nat(0u);
v_calcTk_1999_ = l_Lean_Syntax_getArg(v_x_1985_, v___x_1998_);
lean_dec(v_x_1985_);
v___x_2000_ = l_Lean_Fmt_fmtCalc(v_calcTk_1999_, v_steps_1993_, v_a_1986_, v_a_1987_);
lean_dec(v_steps_1993_);
return v___x_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCalc___boxed(lean_object* v_x_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_Fmt_fmtConvCalc(v_x_2001_, v_a_2002_, v_a_2003_);
lean_dec_ref(v_a_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1(){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2011_ = l_Lean_Fmt_fmtAttribute;
v___x_2012_ = ((lean_object*)(l_Lean_Fmt_fmtConvCalc___closed__1));
v___x_2013_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__1));
v___x_2014_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvCalc___boxed), 3, 0);
v___x_2015_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2011_, v___x_2012_, v___x_2013_, v___x_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___boxed(lean_object* v_a_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1();
return v_res_2017_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_NotationExtra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtTimes = _init_l_Lean_Fmt_fmtTimes();
lean_mark_persistent(l_Lean_Fmt_fmtTimes);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtSigmaTimes = _init_l_Lean_Fmt_fmtSigmaTimes();
lean_mark_persistent(l_Lean_Fmt_fmtSigmaTimes);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtTimes_x27 = _init_l_Lean_Fmt_fmtTimes_x27();
lean_mark_persistent(l_Lean_Fmt_fmtTimes_x27);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtPSigmaTimes = _init_l_Lean_Fmt_fmtPSigmaTimes();
lean_mark_persistent(l_Lean_Fmt_fmtPSigmaTimes);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtUnifConstraint = _init_l_Lean_Fmt_fmtUnifConstraint();
lean_mark_persistent(l_Lean_Fmt_fmtUnifConstraint);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_NotationExtra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Util_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_NotationExtra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Util_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_NotationExtra(builtin);
}
#ifdef __cplusplus
}
#endif
