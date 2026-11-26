// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.NotationExtra
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Lean.Parser.Term meta import Init.NotationExtra meta import Init.Notation import Lean.Fmt.FmtM.CommonFormatters import Init.Data import Init.While
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
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__2_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(lean_object* v_as_10_, size_t v_i_11_, size_t v_stop_12_, lean_object* v_b_13_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = lean_usize_dec_eq(v_i_11_, v_stop_12_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v_fst_16_; lean_object* v_snd_17_; lean_object* v___y_19_; 
v___x_15_ = lean_array_uget_borrowed(v_as_10_, v_i_11_);
v_fst_16_ = lean_ctor_get(v___x_15_, 0);
v_snd_17_ = lean_ctor_get(v___x_15_, 1);
if (lean_obj_tag(v_snd_17_) == 0)
{
lean_object* v___x_28_; 
v___x_28_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__3));
v___y_19_ = v___x_28_;
goto v___jp_18_;
}
else
{
lean_object* v_val_29_; 
v_val_29_ = lean_ctor_get(v_snd_17_, 0);
lean_inc(v_val_29_);
v___y_19_ = v_val_29_;
goto v___jp_18_;
}
v___jp_18_:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; size_t v___x_25_; size_t v___x_26_; 
v___x_20_ = lean_unsigned_to_nat(2u);
v___x_21_ = lean_mk_empty_array_with_capacity(v___x_20_);
lean_inc(v_fst_16_);
v___x_22_ = lean_array_push(v___x_21_, v_fst_16_);
v___x_23_ = lean_array_push(v___x_22_, v___y_19_);
v___x_24_ = l_Array_append___redArg(v_b_13_, v___x_23_);
lean_dec_ref(v___x_23_);
v___x_25_ = ((size_t)1ULL);
v___x_26_ = lean_usize_add(v_i_11_, v___x_25_);
v_i_11_ = v___x_26_;
v_b_13_ = v___x_24_;
goto _start;
}
}
else
{
return v_b_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___boxed(lean_object* v_as_30_, lean_object* v_i_31_, lean_object* v_stop_32_, lean_object* v_b_33_){
_start:
{
size_t v_i_boxed_34_; size_t v_stop_boxed_35_; lean_object* v_res_36_; 
v_i_boxed_34_ = lean_unbox_usize(v_i_31_);
lean_dec(v_i_31_);
v_stop_boxed_35_ = lean_unbox_usize(v_stop_32_);
lean_dec(v_stop_32_);
v_res_36_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(v_as_30_, v_i_boxed_34_, v_stop_boxed_35_, v_b_33_);
lean_dec_ref(v_as_30_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(lean_object* v_elems_37_, lean_object* v_seps_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_39_ = l_Array_zip___redArg(v_elems_37_, v_seps_38_);
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0___closed__0));
v___x_42_ = lean_array_get_size(v___x_39_);
v___x_43_ = lean_nat_dec_lt(v___x_40_, v___x_42_);
if (v___x_43_ == 0)
{
lean_dec_ref(v___x_39_);
return v___x_41_;
}
else
{
size_t v___x_44_; size_t v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((size_t)0ULL);
v___x_45_ = lean_usize_of_nat(v___x_42_);
v___x_46_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps_spec__0(v___x_39_, v___x_44_, v___x_45_, v___x_41_);
lean_dec_ref(v___x_39_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps___redArg___boxed(lean_object* v_elems_47_, lean_object* v_seps_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(v_elems_47_, v_seps_48_);
lean_dec_ref(v_seps_48_);
lean_dec_ref(v_elems_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps(lean_object* v_kinds_50_, lean_object* v_elems_51_, lean_object* v_seps_52_, lean_object* v_sep_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(v_elems_51_, v_seps_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps___boxed(lean_object* v_kinds_55_, lean_object* v_elems_56_, lean_object* v_seps_57_, lean_object* v_sep_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps(v_kinds_55_, v_elems_56_, v_seps_57_, v_sep_58_);
lean_dec_ref(v_sep_58_);
lean_dec_ref(v_seps_57_);
lean_dec_ref(v_elems_56_);
lean_dec(v_kinds_55_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg(lean_object* v_secondaryPats_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_fst_62_; lean_object* v_snd_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_89_; 
v_fst_62_ = lean_ctor_get(v_a_61_, 0);
v_snd_63_ = lean_ctor_get(v_a_61_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_a_61_);
if (v_isSharedCheck_89_ == 0)
{
v___x_65_ = v_a_61_;
v_isShared_66_ = v_isSharedCheck_89_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_snd_63_);
lean_inc(v_fst_62_);
lean_dec(v_a_61_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_89_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_array_get_size(v_secondaryPats_60_);
v___x_68_ = lean_nat_dec_lt(v_fst_62_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_70_; 
if (v_isShared_66_ == 0)
{
v___x_70_ = v___x_65_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_fst_62_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_snd_63_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_72_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_73_ = lean_array_get_borrowed(v___x_72_, v_secondaryPats_60_, v_fst_62_);
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_add(v_fst_62_, v___x_74_);
v___x_76_ = lean_array_get_borrowed(v___x_72_, v_secondaryPats_60_, v___x_75_);
lean_dec(v___x_75_);
v___x_77_ = lean_unsigned_to_nat(2u);
v___x_78_ = lean_mk_empty_array_with_capacity(v___x_77_);
lean_inc(v___x_73_);
v___x_79_ = lean_array_push(v___x_78_, v___x_73_);
lean_inc(v___x_76_);
v___x_80_ = lean_array_push(v___x_79_, v___x_76_);
v___x_81_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v___x_80_);
lean_dec_ref(v___x_80_);
v___x_82_ = l_Lean_Fmt_TaggedDoc_nested(v___x_81_);
v___x_83_ = lean_array_push(v_snd_63_, v___x_82_);
v___x_84_ = lean_nat_add(v_fst_62_, v___x_77_);
lean_dec(v_fst_62_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_83_);
lean_ctor_set(v___x_65_, 0, v___x_84_);
v___x_86_ = v___x_65_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_83_);
v___x_86_ = v_reuseFailAlloc_88_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
v_a_61_ = v___x_86_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg___boxed(lean_object* v_secondaryPats_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg(v_secondaryPats_90_, v_a_91_);
lean_dec_ref(v_secondaryPats_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___lam__0(lean_object* v___y_93_){
_start:
{
lean_inc_ref(v___y_93_);
return v___y_93_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___lam__0___boxed(lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___lam__0(v___y_94_);
lean_dec_ref(v___y_94_);
return v_res_95_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__1(void){
_start:
{
lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___f_97_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__0));
v___x_98_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___f_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1(size_t v_sz_100_, size_t v_i_101_, lean_object* v_bs_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_lt(v_i_101_, v_sz_100_);
if (v___x_103_ == 0)
{
return v_bs_102_;
}
else
{
lean_object* v_v_104_; lean_object* v___x_105_; lean_object* v_bs_x27_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; size_t v___x_110_; size_t v___x_111_; lean_object* v___x_112_; 
v_v_104_ = lean_array_uget(v_bs_102_, v_i_101_);
v___x_105_ = lean_unsigned_to_nat(0u);
v_bs_x27_106_ = lean_array_uset(v_bs_102_, v_i_101_, v___x_105_);
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v_v_104_);
v___x_108_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___closed__1);
v___x_109_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_107_, v___x_108_);
v___x_110_ = ((size_t)1ULL);
v___x_111_ = lean_usize_add(v_i_101_, v___x_110_);
v___x_112_ = lean_array_uset(v_bs_x27_106_, v_i_101_, v___x_109_);
v_i_101_ = v___x_111_;
v_bs_102_ = v___x_112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1___boxed(lean_object* v_sz_114_, lean_object* v_i_115_, lean_object* v_bs_116_){
_start:
{
size_t v_sz_boxed_117_; size_t v_i_boxed_118_; lean_object* v_res_119_; 
v_sz_boxed_117_ = lean_unbox_usize(v_sz_114_);
lean_dec(v_sz_114_);
v_i_boxed_118_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_res_119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1(v_sz_boxed_117_, v_i_boxed_118_, v_bs_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats(lean_object* v_secondaryPats_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v_snd_128_; size_t v_sz_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_126_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__1));
v___x_127_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg(v_secondaryPats_125_, v___x_126_);
v_snd_128_ = lean_ctor_get(v___x_127_, 1);
lean_inc(v_snd_128_);
lean_dec_ref(v___x_127_);
v_sz_129_ = lean_array_size(v_snd_128_);
v___x_130_ = ((size_t)0ULL);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__1(v_sz_129_, v___x_130_, v_snd_128_);
v___x_132_ = l_Lean_Fmt_TaggedDoc_combine(v___x_131_);
lean_dec_ref(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___boxed(lean_object* v_secondaryPats_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats(v_secondaryPats_133_);
lean_dec_ref(v_secondaryPats_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0(lean_object* v_secondaryPats_135_, lean_object* v_inst_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___redArg(v_secondaryPats_135_, v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0___boxed(lean_object* v_secondaryPats_139_, lean_object* v_inst_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats_spec__0(v_secondaryPats_139_, v_inst_140_, v_a_141_);
lean_dec_ref(v_secondaryPats_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches___lam__0(lean_object* v___y_143_){
_start:
{
lean_inc_ref(v___y_143_);
return v___y_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches___lam__0___boxed(lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Fmt_fmtTermMatches___lam__0(v___y_144_);
lean_dec_ref(v___y_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtTermMatches_spec__0___redArg(lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
lean_object* v_array_148_; lean_object* v_start_149_; lean_object* v_stop_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_163_; 
v_array_148_ = lean_ctor_get(v_a_146_, 0);
v_start_149_ = lean_ctor_get(v_a_146_, 1);
v_stop_150_ = lean_ctor_get(v_a_146_, 2);
v_isSharedCheck_163_ = !lean_is_exclusive(v_a_146_);
if (v_isSharedCheck_163_ == 0)
{
v___x_152_ = v_a_146_;
v_isShared_153_ = v_isSharedCheck_163_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_stop_150_);
lean_inc(v_start_149_);
lean_inc(v_array_148_);
lean_dec(v_a_146_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_163_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
uint8_t v___x_154_; 
v___x_154_ = lean_nat_dec_lt(v_start_149_, v_stop_150_);
if (v___x_154_ == 0)
{
lean_del_object(v___x_152_);
lean_dec(v_stop_150_);
lean_dec(v_start_149_);
lean_dec_ref(v_array_148_);
return v_b_147_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_nat_add(v_start_149_, v___x_155_);
lean_inc_ref(v_array_148_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___x_156_);
v___x_158_ = v___x_152_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_array_148_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v_stop_150_);
v___x_158_ = v_reuseFailAlloc_162_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_array_fget(v_array_148_, v_start_149_);
lean_dec(v_start_149_);
lean_dec_ref(v_array_148_);
v___x_160_ = lean_array_push(v_b_147_, v___x_159_);
v_a_146_ = v___x_158_;
v_b_147_ = v___x_160_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermMatches___closed__4(void){
_start:
{
lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___f_170_ = ((lean_object*)(l_Lean_Fmt_fmtTermMatches___closed__3));
v___x_171_ = l_Lean_Fmt_TaggedDoc_space;
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___f_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermMatches___closed__6(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = ((lean_object*)(l_Lean_Fmt_fmtTermMatches___closed__5));
v___x_175_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermMatches___closed__7(void){
_start:
{
lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___f_177_ = ((lean_object*)(l_Lean_Fmt_fmtTermMatches___closed__3));
v___x_178_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___f_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches(lean_object* v_x_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = ((lean_object*)(l_Lean_Fmt_fmtTermMatches___closed__2));
lean_inc(v_x_180_);
v___x_184_ = l_Lean_Syntax_isOfKind(v_x_180_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_x_180_);
v___x_185_ = l_Lean_Fmt_Error_partialFormatter;
v___x_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_a_182_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = l_Lean_Syntax_getArg(v_x_180_, v___x_187_);
v___x_189_ = l_Lean_Fmt_fmt(v___x_188_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v_a_191_; lean_object* v___x_192_; lean_object* v_matchesTk_193_; lean_object* v___x_194_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
v_a_191_ = lean_ctor_get(v___x_189_, 1);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_189_, 2);
v___x_192_ = lean_unsigned_to_nat(1u);
v_matchesTk_193_ = l_Lean_Syntax_getArg(v_x_180_, v___x_192_);
v___x_194_ = l_Lean_Fmt_fmt(v_matchesTk_193_, v_a_181_, v_a_191_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_pats_199_; lean_object* v___x_200_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
v_a_196_ = lean_ctor_get(v___x_194_, 1);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_194_, 2);
v___x_197_ = lean_unsigned_to_nat(2u);
v___x_198_ = l_Lean_Syntax_getArg(v_x_180_, v___x_197_);
lean_dec(v_x_180_);
v_pats_199_ = l_Lean_Syntax_getArgs(v___x_198_);
lean_dec(v___x_198_);
v___x_200_ = l_Lean_Fmt_fmtTSepArray___redArg(v_pats_199_, v_a_181_, v_a_196_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_257_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_a_202_ = lean_ctor_get(v___x_200_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_257_ == 0)
{
v___x_204_ = v___x_200_;
v_isShared_205_ = v_isSharedCheck_257_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_257_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_array_get_size(v_a_201_);
v___x_207_ = lean_nat_dec_eq(v___x_206_, v___x_192_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_208_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_209_ = lean_array_get_borrowed(v___x_208_, v_a_201_, v___x_187_);
lean_inc(v___x_209_);
v___x_210_ = l_Lean_Fmt_TaggedDoc_nested(v___x_209_);
v___x_211_ = l_Array_toSubarray___redArg(v_a_201_, v___x_192_, v___x_206_);
v___x_212_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats___closed__0));
v___x_213_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtTermMatches_spec__0___redArg(v___x_211_, v___x_212_);
v___x_214_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches_fmtSecondaryPats(v___x_213_);
lean_dec_ref(v___x_213_);
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v_a_195_);
v___x_216_ = lean_obj_once(&l_Lean_Fmt_fmtTermMatches___closed__4, &l_Lean_Fmt_fmtTermMatches___closed__4_once, _init_l_Lean_Fmt_fmtTermMatches___closed__4);
lean_inc_ref(v___x_215_);
v___x_217_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_215_, v___x_216_);
lean_inc_ref(v___x_210_);
v___x_218_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_210_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
v___x_220_ = lean_obj_once(&l_Lean_Fmt_fmtTermMatches___closed__6, &l_Lean_Fmt_fmtTermMatches___closed__6_once, _init_l_Lean_Fmt_fmtTermMatches___closed__6);
v___x_221_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_219_, v___x_220_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_214_);
v___x_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
lean_ctor_set(v___x_224_, 2, v___x_222_);
v___x_225_ = lean_unsigned_to_nat(3u);
v___x_226_ = lean_mk_empty_array_with_capacity(v___x_225_);
lean_inc_ref(v___x_226_);
v___x_227_ = lean_array_push(v___x_226_, v___x_217_);
v___x_228_ = lean_array_push(v___x_227_, v___x_221_);
lean_inc_ref(v___x_224_);
v___x_229_ = lean_array_push(v___x_228_, v___x_224_);
v___x_230_ = l_Lean_Fmt_TaggedDoc_combine(v___x_229_);
lean_dec_ref(v___x_229_);
v___x_231_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_215_, v___x_220_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_210_);
v___x_233_ = lean_obj_once(&l_Lean_Fmt_fmtTermMatches___closed__7, &l_Lean_Fmt_fmtTermMatches___closed__7_once, _init_l_Lean_Fmt_fmtTermMatches___closed__7);
v___x_234_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_232_, v___x_233_);
v___x_235_ = lean_array_push(v___x_226_, v___x_231_);
v___x_236_ = lean_array_push(v___x_235_, v___x_234_);
v___x_237_ = lean_array_push(v___x_236_, v___x_224_);
v___x_238_ = l_Lean_Fmt_TaggedDoc_combine(v___x_237_);
lean_dec_ref(v___x_237_);
v___x_239_ = lean_mk_empty_array_with_capacity(v___x_197_);
lean_inc_ref(v___x_239_);
v___x_240_ = lean_array_push(v___x_239_, v___x_230_);
v___x_241_ = lean_array_push(v___x_240_, v___x_238_);
v___x_242_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_241_);
v___x_243_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_242_);
v___x_244_ = l_Lean_Fmt_TaggedDoc_hardNested(v_a_190_);
v___x_245_ = lean_array_push(v___x_239_, v___x_244_);
v___x_246_ = lean_array_push(v___x_245_, v___x_243_);
v___x_247_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_246_);
lean_dec_ref(v___x_246_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_247_);
v___x_249_ = v___x_204_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_a_202_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_251_ = lean_array_fget(v_a_201_, v___x_187_);
lean_dec(v_a_201_);
v___x_252_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_252_, 0, v___x_207_);
lean_ctor_set_uint8(v___x_252_, 1, v___x_207_);
v___x_253_ = l_Lean_Fmt_Layouts_keywordSeparated(v_a_190_, v_a_195_, v___x_251_, v___x_252_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_253_);
v___x_255_ = v___x_204_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_a_202_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
else
{
lean_object* v_a_258_; lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec(v_a_195_);
lean_dec(v_a_190_);
v_a_258_ = lean_ctor_get(v___x_200_, 0);
v_a_259_ = lean_ctor_get(v___x_200_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_200_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_inc(v_a_258_);
lean_dec(v___x_200_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_258_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_dec(v_a_190_);
lean_dec(v_x_180_);
return v___x_194_;
}
}
else
{
lean_dec(v_x_180_);
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMatches___boxed(lean_object* v_x_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Fmt_fmtTermMatches(v_x_267_, v_a_268_, v_a_269_);
lean_dec_ref(v_a_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtTermMatches_spec__0(lean_object* v_inst_271_, lean_object* v_R_272_, lean_object* v_a_273_, lean_object* v_b_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtTermMatches_spec__0___redArg(v_a_273_, v_b_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1(){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_283_ = l_Lean_Fmt_fmtAttribute;
v___x_284_ = ((lean_object*)(l_Lean_Fmt_fmtTermMatches___closed__2));
v___x_285_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___closed__2));
v___x_286_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermMatches___boxed), 3, 0);
v___x_287_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_283_, v___x_284_, v___x_285_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1___boxed(lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTermMatches___regBuiltin_Lean_Fmt_fmtTermMatches__1();
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnbracketedExplicitBinders(lean_object* v_x_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1));
lean_inc(v_x_298_);
v___x_302_ = l_Lean_Syntax_isOfKind(v_x_298_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v_x_298_);
v___x_303_ = l_Lean_Fmt_Error_partialFormatter;
v___x_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v_a_300_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_typeAscriptionTk_x3f_308_; lean_object* v_type_x3f_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = l_Lean_Syntax_getArg(v_x_298_, v___x_305_);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = l_Lean_Syntax_getArg(v_x_298_, v___x_317_);
lean_dec(v_x_298_);
v___x_319_ = l_Lean_Syntax_isNone(v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_318_);
v___x_321_ = l_Lean_Syntax_matchesNull(v___x_318_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v___x_318_);
lean_dec(v___x_306_);
v___x_322_ = l_Lean_Fmt_Error_partialFormatter;
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_a_300_);
return v___x_323_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_324_; lean_object* v_type_x3f_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_typeAscriptionTk_x3f_324_ = l_Lean_Syntax_getArg(v___x_318_, v___x_305_);
v_type_x3f_325_ = l_Lean_Syntax_getArg(v___x_318_, v___x_317_);
lean_dec(v___x_318_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_typeAscriptionTk_x3f_324_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v_type_x3f_325_);
v_typeAscriptionTk_x3f_308_ = v___x_326_;
v_type_x3f_309_ = v___x_327_;
v___y_310_ = v_a_299_;
v___y_311_ = v_a_300_;
goto v___jp_307_;
}
}
else
{
lean_object* v___x_328_; 
lean_dec(v___x_318_);
v___x_328_ = lean_box(0);
v_typeAscriptionTk_x3f_308_ = v___x_328_;
v_type_x3f_309_ = v___x_328_;
v___y_310_ = v_a_299_;
v___y_311_ = v_a_300_;
goto v___jp_307_;
}
v___jp_307_:
{
lean_object* v_ids_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_ids_312_ = l_Lean_Syntax_getArgs(v___x_306_);
lean_dec(v___x_306_);
v___x_313_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2));
v___x_314_ = lean_box(0);
v___x_315_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__3));
v___x_316_ = l_Lean_Fmt_fmtBinder(v___x_313_, v_ids_312_, v___x_313_, v_typeAscriptionTk_x3f_308_, v_type_x3f_309_, v___x_314_, v___x_313_, v___x_315_, v___y_310_, v___y_311_);
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnbracketedExplicitBinders___boxed(lean_object* v_x_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Fmt_fmtUnbracketedExplicitBinders(v_x_329_, v_a_330_, v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1(){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_339_ = l_Lean_Fmt_fmtAttribute;
v___x_340_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1));
v___x_341_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___closed__1));
v___x_342_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___boxed), 3, 0);
v___x_343_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_339_, v___x_340_, v___x_341_, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1___boxed(lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnbracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtUnbracketedExplicitBinders__1();
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBracketedExplicitBinders(lean_object* v_x_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1));
lean_inc(v_x_350_);
v___x_354_ = l_Lean_Syntax_isOfKind(v_x_350_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v_x_350_);
v___x_355_ = l_Lean_Fmt_Error_partialFormatter;
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_a_352_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v_lbTk_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_typeAscriptionTk_362_; lean_object* v___x_363_; lean_object* v_type_364_; lean_object* v___x_365_; lean_object* v_rbTk_366_; lean_object* v_ids_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_357_ = lean_unsigned_to_nat(0u);
v_lbTk_358_ = l_Lean_Syntax_getArg(v_x_350_, v___x_357_);
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = l_Lean_Syntax_getArg(v_x_350_, v___x_359_);
v___x_361_ = lean_unsigned_to_nat(2u);
v_typeAscriptionTk_362_ = l_Lean_Syntax_getArg(v_x_350_, v___x_361_);
v___x_363_ = lean_unsigned_to_nat(3u);
v_type_364_ = l_Lean_Syntax_getArg(v_x_350_, v___x_363_);
v___x_365_ = lean_unsigned_to_nat(4u);
v_rbTk_366_ = l_Lean_Syntax_getArg(v_x_350_, v___x_365_);
lean_dec(v_x_350_);
v_ids_367_ = l_Lean_Syntax_getArgs(v___x_360_);
lean_dec(v___x_360_);
v___x_368_ = lean_mk_empty_array_with_capacity(v___x_359_);
lean_inc_ref(v___x_368_);
v___x_369_ = lean_array_push(v___x_368_, v_lbTk_358_);
v___x_370_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2));
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v_typeAscriptionTk_362_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v_type_364_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_array_push(v___x_368_, v_rbTk_366_);
v___x_375_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__3));
v___x_376_ = l_Lean_Fmt_fmtBinder(v___x_369_, v_ids_367_, v___x_370_, v___x_371_, v___x_372_, v___x_373_, v___x_374_, v___x_375_, v_a_351_, v_a_352_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBracketedExplicitBinders___boxed(lean_object* v_x_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Fmt_fmtBracketedExplicitBinders(v_x_377_, v_a_378_, v_a_379_);
lean_dec_ref(v_a_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1(){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_387_ = l_Lean_Fmt_fmtAttribute;
v___x_388_ = ((lean_object*)(l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1));
v___x_389_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___closed__1));
v___x_390_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBracketedExplicitBinders___boxed), 3, 0);
v___x_391_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_387_, v___x_388_, v___x_389_, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1___boxed(lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtBracketedExplicitBinders___regBuiltin_Lean_Fmt_fmtBracketedExplicitBinders__1();
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_explicitBindersToGroup_spec__0(size_t v_sz_394_, size_t v_i_395_, lean_object* v_bs_396_){
_start:
{
uint8_t v___x_397_; 
v___x_397_ = lean_usize_dec_lt(v_i_395_, v_sz_394_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v_bs_396_);
return v___x_398_;
}
else
{
lean_object* v_v_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_v_399_ = lean_array_uget(v_bs_396_, v_i_395_);
v___x_400_ = ((lean_object*)(l_Lean_Fmt_fmtBracketedExplicitBinders___closed__1));
lean_inc(v_v_399_);
v___x_401_ = l_Lean_Syntax_isOfKind(v_v_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec(v_v_399_);
lean_dec_ref(v_bs_396_);
v___x_402_ = lean_box(0);
return v___x_402_;
}
else
{
lean_object* v___x_403_; lean_object* v_bs_x27_404_; size_t v___x_405_; size_t v___x_406_; lean_object* v___x_407_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v_bs_x27_404_ = lean_array_uset(v_bs_396_, v_i_395_, v___x_403_);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_add(v_i_395_, v___x_405_);
v___x_407_ = lean_array_uset(v_bs_x27_404_, v_i_395_, v_v_399_);
v_i_395_ = v___x_406_;
v_bs_396_ = v___x_407_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_explicitBindersToGroup_spec__0___boxed(lean_object* v_sz_409_, lean_object* v_i_410_, lean_object* v_bs_411_){
_start:
{
size_t v_sz_boxed_412_; size_t v_i_boxed_413_; lean_object* v_res_414_; 
v_sz_boxed_412_ = lean_unbox_usize(v_sz_409_);
lean_dec(v_sz_409_);
v_i_boxed_413_ = lean_unbox_usize(v_i_410_);
lean_dec(v_i_410_);
v_res_414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_explicitBindersToGroup_spec__0(v_sz_boxed_412_, v_i_boxed_413_, v_bs_411_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_explicitBindersToGroup(lean_object* v_bs_419_){
_start:
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Fmt_explicitBindersToGroup___closed__1));
lean_inc(v_bs_419_);
v___x_421_ = l_Lean_Syntax_isOfKind(v_bs_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec(v_bs_419_);
v___x_422_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2));
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = l_Lean_Syntax_getArg(v_bs_419_, v___x_423_);
lean_dec(v_bs_419_);
v___x_425_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__1));
lean_inc(v___x_424_);
v___x_426_ = l_Lean_Syntax_isOfKind(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; size_t v_sz_428_; size_t v___x_429_; lean_object* v___x_430_; 
v___x_427_ = l_Lean_Syntax_getArgs(v___x_424_);
lean_dec(v___x_424_);
v_sz_428_ = lean_array_size(v___x_427_);
v___x_429_ = ((size_t)0ULL);
v___x_430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_explicitBindersToGroup_spec__0(v_sz_428_, v___x_429_, v___x_427_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v___x_431_; 
v___x_431_ = ((lean_object*)(l_Lean_Fmt_fmtUnbracketedExplicitBinders___closed__2));
return v___x_431_;
}
else
{
lean_object* v_val_432_; 
v_val_432_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_val_432_);
lean_dec_ref_known(v___x_430_, 1);
return v_val_432_;
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_mk_empty_array_with_capacity(v___x_433_);
v___x_435_ = lean_array_push(v___x_434_, v___x_424_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExists(lean_object* v_x_439_){
_start:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Fmt_fmtExists___closed__1));
lean_inc(v_x_439_);
v___x_441_ = l_Lean_Syntax_isOfKind(v_x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
lean_dec(v_x_439_);
v___x_442_ = lean_box(0);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v_bs_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v_bs_444_ = l_Lean_Syntax_getArg(v_x_439_, v___x_443_);
v___x_445_ = ((lean_object*)(l_Lean_Fmt_explicitBindersToGroup___closed__1));
lean_inc(v_bs_444_);
v___x_446_ = l_Lean_Syntax_isOfKind(v_bs_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec(v_bs_444_);
lean_dec(v_x_439_);
v___x_447_ = lean_box(0);
return v___x_447_;
}
else
{
lean_object* v___x_448_; lean_object* v_exTk_449_; lean_object* v___x_450_; lean_object* v_commaTk_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v_exTk_449_ = l_Lean_Syntax_getArg(v_x_439_, v___x_448_);
v___x_450_ = lean_unsigned_to_nat(2u);
v_commaTk_451_ = l_Lean_Syntax_getArg(v_x_439_, v___x_450_);
v___x_452_ = lean_unsigned_to_nat(3u);
v___x_453_ = l_Lean_Syntax_getArg(v_x_439_, v___x_452_);
lean_dec(v_x_439_);
v___x_454_ = l_Lean_Fmt_explicitBindersToGroup(v_bs_444_);
v___x_455_ = lean_mk_empty_array_with_capacity(v___x_443_);
lean_inc_ref(v___x_455_);
v___x_456_ = lean_array_push(v___x_455_, v___x_454_);
v___x_457_ = lean_array_push(v___x_455_, v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
v___x_459_ = lean_box(0);
v___x_460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_460_, 0, v_exTk_449_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
lean_ctor_set(v___x_460_, 2, v___x_459_);
lean_ctor_set(v___x_460_, 3, v___x_459_);
lean_ctor_set(v___x_460_, 4, v_commaTk_451_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_453_);
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1(){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_469_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_470_ = ((lean_object*)(l_Lean_Fmt_fmtExists___closed__1));
v___x_471_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___closed__1));
v___x_472_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExists), 1, 0);
v___x_473_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_469_, v___x_470_, v___x_471_, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1___boxed(lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExists___regBuiltin_Lean_Fmt_fmtExists__1();
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExistsKeyword(lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Fmt_fmtExistsKeyword___closed__1));
lean_inc(v_x_479_);
v___x_481_ = l_Lean_Syntax_isOfKind(v_x_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
lean_dec(v_x_479_);
v___x_482_ = lean_box(0);
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v_bs_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v_bs_484_ = l_Lean_Syntax_getArg(v_x_479_, v___x_483_);
v___x_485_ = ((lean_object*)(l_Lean_Fmt_explicitBindersToGroup___closed__1));
lean_inc(v_bs_484_);
v___x_486_ = l_Lean_Syntax_isOfKind(v_bs_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec(v_bs_484_);
lean_dec(v_x_479_);
v___x_487_ = lean_box(0);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v_existsTk_489_; lean_object* v___x_490_; lean_object* v_commaTk_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_488_ = lean_unsigned_to_nat(0u);
v_existsTk_489_ = l_Lean_Syntax_getArg(v_x_479_, v___x_488_);
v___x_490_ = lean_unsigned_to_nat(2u);
v_commaTk_491_ = l_Lean_Syntax_getArg(v_x_479_, v___x_490_);
v___x_492_ = lean_unsigned_to_nat(3u);
v___x_493_ = l_Lean_Syntax_getArg(v_x_479_, v___x_492_);
lean_dec(v_x_479_);
v___x_494_ = l_Lean_Fmt_explicitBindersToGroup(v_bs_484_);
v___x_495_ = lean_mk_empty_array_with_capacity(v___x_483_);
lean_inc_ref(v___x_495_);
v___x_496_ = lean_array_push(v___x_495_, v___x_494_);
v___x_497_ = lean_array_push(v___x_495_, v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
v___x_499_ = lean_box(0);
v___x_500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_500_, 0, v_existsTk_489_);
lean_ctor_set(v___x_500_, 1, v___x_498_);
lean_ctor_set(v___x_500_, 2, v___x_499_);
lean_ctor_set(v___x_500_, 3, v___x_499_);
lean_ctor_set(v___x_500_, 4, v_commaTk_491_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_493_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1(){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_509_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_510_ = ((lean_object*)(l_Lean_Fmt_fmtExistsKeyword___closed__1));
v___x_511_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___closed__1));
v___x_512_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExistsKeyword), 1, 0);
v___x_513_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_509_, v___x_510_, v___x_511_, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1___boxed(lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtExistsKeyword___regBuiltin_Lean_Fmt_fmtExistsKeyword__1();
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSigma(lean_object* v_x_519_){
_start:
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_Fmt_fmtSigma___closed__1));
lean_inc(v_x_519_);
v___x_521_ = l_Lean_Syntax_isOfKind(v_x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec(v_x_519_);
v___x_522_ = lean_box(0);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v_bs_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v_bs_524_ = l_Lean_Syntax_getArg(v_x_519_, v___x_523_);
v___x_525_ = ((lean_object*)(l_Lean_Fmt_explicitBindersToGroup___closed__1));
lean_inc(v_bs_524_);
v___x_526_ = l_Lean_Syntax_isOfKind(v_bs_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_dec(v_bs_524_);
lean_dec(v_x_519_);
v___x_527_ = lean_box(0);
return v___x_527_;
}
else
{
lean_object* v___x_528_; lean_object* v_sigmaTk_529_; lean_object* v___x_530_; lean_object* v_commaTk_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v_sigmaTk_529_ = l_Lean_Syntax_getArg(v_x_519_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(2u);
v_commaTk_531_ = l_Lean_Syntax_getArg(v_x_519_, v___x_530_);
v___x_532_ = lean_unsigned_to_nat(3u);
v___x_533_ = l_Lean_Syntax_getArg(v_x_519_, v___x_532_);
lean_dec(v_x_519_);
v___x_534_ = l_Lean_Fmt_explicitBindersToGroup(v_bs_524_);
v___x_535_ = lean_mk_empty_array_with_capacity(v___x_523_);
lean_inc_ref(v___x_535_);
v___x_536_ = lean_array_push(v___x_535_, v___x_534_);
v___x_537_ = lean_array_push(v___x_535_, v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
v___x_539_ = lean_box(0);
v___x_540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_540_, 0, v_sigmaTk_529_);
lean_ctor_set(v___x_540_, 1, v___x_538_);
lean_ctor_set(v___x_540_, 2, v___x_539_);
lean_ctor_set(v___x_540_, 3, v___x_539_);
lean_ctor_set(v___x_540_, 4, v_commaTk_531_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___x_533_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1(){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_549_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_550_ = ((lean_object*)(l_Lean_Fmt_fmtSigma___closed__1));
v___x_551_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___closed__1));
v___x_552_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSigma), 1, 0);
v___x_553_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_549_, v___x_550_, v___x_551_, v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1___boxed(lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigma___regBuiltin_Lean_Fmt_fmtSigma__1();
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPSigma(lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_Fmt_fmtPSigma___closed__1));
lean_inc(v_x_559_);
v___x_561_ = l_Lean_Syntax_isOfKind(v_x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
lean_dec(v_x_559_);
v___x_562_ = lean_box(0);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v_bs_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_563_ = lean_unsigned_to_nat(1u);
v_bs_564_ = l_Lean_Syntax_getArg(v_x_559_, v___x_563_);
v___x_565_ = ((lean_object*)(l_Lean_Fmt_explicitBindersToGroup___closed__1));
lean_inc(v_bs_564_);
v___x_566_ = l_Lean_Syntax_isOfKind(v_bs_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; 
lean_dec(v_bs_564_);
lean_dec(v_x_559_);
v___x_567_ = lean_box(0);
return v___x_567_;
}
else
{
lean_object* v___x_568_; lean_object* v_psigmaTk_569_; lean_object* v___x_570_; lean_object* v_commaTk_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v_psigmaTk_569_ = l_Lean_Syntax_getArg(v_x_559_, v___x_568_);
v___x_570_ = lean_unsigned_to_nat(2u);
v_commaTk_571_ = l_Lean_Syntax_getArg(v_x_559_, v___x_570_);
v___x_572_ = lean_unsigned_to_nat(3u);
v___x_573_ = l_Lean_Syntax_getArg(v_x_559_, v___x_572_);
lean_dec(v_x_559_);
v___x_574_ = l_Lean_Fmt_explicitBindersToGroup(v_bs_564_);
v___x_575_ = lean_mk_empty_array_with_capacity(v___x_563_);
lean_inc_ref(v___x_575_);
v___x_576_ = lean_array_push(v___x_575_, v___x_574_);
v___x_577_ = lean_array_push(v___x_575_, v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_580_, 0, v_psigmaTk_569_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_579_);
lean_ctor_set(v___x_580_, 3, v___x_579_);
lean_ctor_set(v___x_580_, 4, v_commaTk_571_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_573_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1(){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_589_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_590_ = ((lean_object*)(l_Lean_Fmt_fmtPSigma___closed__1));
v___x_591_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___closed__1));
v___x_592_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPSigma), 1, 0);
v___x_593_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_589_, v___x_590_, v___x_591_, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1___boxed(lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigma___regBuiltin_Lean_Fmt_fmtPSigma__1();
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
return v_x_596_;
}
else
{
lean_object* v_key_598_; lean_object* v_value_599_; lean_object* v_tail_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_626_; 
v_key_598_ = lean_ctor_get(v_x_597_, 0);
v_value_599_ = lean_ctor_get(v_x_597_, 1);
v_tail_600_ = lean_ctor_get(v_x_597_, 2);
v_isSharedCheck_626_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_626_ == 0)
{
v___x_602_ = v_x_597_;
v_isShared_603_ = v_isSharedCheck_626_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_tail_600_);
lean_inc(v_value_599_);
lean_inc(v_key_598_);
lean_dec(v_x_597_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_626_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; uint64_t v___y_606_; 
v___x_604_ = lean_array_get_size(v_x_596_);
if (lean_obj_tag(v_key_598_) == 0)
{
uint64_t v___x_624_; 
v___x_624_ = 1723ULL;
v___y_606_ = v___x_624_;
goto v___jp_605_;
}
else
{
uint64_t v_hash_625_; 
v_hash_625_ = lean_ctor_get_uint64(v_key_598_, sizeof(void*)*2);
v___y_606_ = v_hash_625_;
goto v___jp_605_;
}
v___jp_605_:
{
uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v_fold_609_; uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_607_ = 32ULL;
v___x_608_ = lean_uint64_shift_right(v___y_606_, v___x_607_);
v_fold_609_ = lean_uint64_xor(v___y_606_, v___x_608_);
v___x_610_ = 16ULL;
v___x_611_ = lean_uint64_shift_right(v_fold_609_, v___x_610_);
v___x_612_ = lean_uint64_xor(v_fold_609_, v___x_611_);
v___x_613_ = lean_uint64_to_usize(v___x_612_);
v___x_614_ = lean_usize_of_nat(v___x_604_);
v___x_615_ = ((size_t)1ULL);
v___x_616_ = lean_usize_sub(v___x_614_, v___x_615_);
v___x_617_ = lean_usize_land(v___x_613_, v___x_616_);
v___x_618_ = lean_array_uget_borrowed(v_x_596_, v___x_617_);
lean_inc(v___x_618_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 2, v___x_618_);
v___x_620_ = v___x_602_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_key_598_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_value_599_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v___x_618_);
v___x_620_ = v_reuseFailAlloc_623_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_array_uset(v_x_596_, v___x_617_, v___x_620_);
v_x_596_ = v___x_621_;
v_x_597_ = v_tail_600_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2___redArg(lean_object* v_i_627_, lean_object* v_source_628_, lean_object* v_target_629_){
_start:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_array_get_size(v_source_628_);
v___x_631_ = lean_nat_dec_lt(v_i_627_, v___x_630_);
if (v___x_631_ == 0)
{
lean_dec_ref(v_source_628_);
lean_dec(v_i_627_);
return v_target_629_;
}
else
{
lean_object* v_es_632_; lean_object* v___x_633_; lean_object* v_source_634_; lean_object* v_target_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_es_632_ = lean_array_fget(v_source_628_, v_i_627_);
v___x_633_ = lean_box(0);
v_source_634_ = lean_array_fset(v_source_628_, v_i_627_, v___x_633_);
v_target_635_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2_spec__3___redArg(v_target_629_, v_es_632_);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_nat_add(v_i_627_, v___x_636_);
lean_dec(v_i_627_);
v_i_627_ = v___x_637_;
v_source_628_ = v_source_634_;
v_target_629_ = v_target_635_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1___redArg(lean_object* v_data_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v_nbuckets_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_640_ = lean_array_get_size(v_data_639_);
v___x_641_ = lean_unsigned_to_nat(2u);
v_nbuckets_642_ = lean_nat_mul(v___x_640_, v___x_641_);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_box(0);
v___x_645_ = lean_mk_array(v_nbuckets_642_, v___x_644_);
v___x_646_ = lean_array_propagate_mark(v_data_639_, v___x_645_);
v___x_647_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2___redArg(v___x_643_, v_data_639_, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg(lean_object* v_a_648_, lean_object* v_x_649_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
uint8_t v___x_650_; 
v___x_650_ = 0;
return v___x_650_;
}
else
{
lean_object* v_key_651_; lean_object* v_tail_652_; uint8_t v___x_653_; 
v_key_651_ = lean_ctor_get(v_x_649_, 0);
v_tail_652_ = lean_ctor_get(v_x_649_, 2);
v___x_653_ = lean_name_eq(v_key_651_, v_a_648_);
if (v___x_653_ == 0)
{
v_x_649_ = v_tail_652_;
goto _start;
}
else
{
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg___boxed(lean_object* v_a_655_, lean_object* v_x_656_){
_start:
{
uint8_t v_res_657_; lean_object* v_r_658_; 
v_res_657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg(v_a_655_, v_x_656_);
lean_dec(v_x_656_);
lean_dec(v_a_655_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(lean_object* v_m_659_, lean_object* v_a_660_, lean_object* v_b_661_){
_start:
{
lean_object* v_size_662_; lean_object* v_buckets_663_; lean_object* v___x_664_; uint64_t v___y_666_; 
v_size_662_ = lean_ctor_get(v_m_659_, 0);
v_buckets_663_ = lean_ctor_get(v_m_659_, 1);
v___x_664_ = lean_array_get_size(v_buckets_663_);
if (lean_obj_tag(v_a_660_) == 0)
{
uint64_t v___x_703_; 
v___x_703_ = 1723ULL;
v___y_666_ = v___x_703_;
goto v___jp_665_;
}
else
{
uint64_t v_hash_704_; 
v_hash_704_ = lean_ctor_get_uint64(v_a_660_, sizeof(void*)*2);
v___y_666_ = v_hash_704_;
goto v___jp_665_;
}
v___jp_665_:
{
uint64_t v___x_667_; uint64_t v___x_668_; uint64_t v_fold_669_; uint64_t v___x_670_; uint64_t v___x_671_; uint64_t v___x_672_; size_t v___x_673_; size_t v___x_674_; size_t v___x_675_; size_t v___x_676_; size_t v___x_677_; lean_object* v_bkt_678_; uint8_t v___x_679_; 
v___x_667_ = 32ULL;
v___x_668_ = lean_uint64_shift_right(v___y_666_, v___x_667_);
v_fold_669_ = lean_uint64_xor(v___y_666_, v___x_668_);
v___x_670_ = 16ULL;
v___x_671_ = lean_uint64_shift_right(v_fold_669_, v___x_670_);
v___x_672_ = lean_uint64_xor(v_fold_669_, v___x_671_);
v___x_673_ = lean_uint64_to_usize(v___x_672_);
v___x_674_ = lean_usize_of_nat(v___x_664_);
v___x_675_ = ((size_t)1ULL);
v___x_676_ = lean_usize_sub(v___x_674_, v___x_675_);
v___x_677_ = lean_usize_land(v___x_673_, v___x_676_);
v_bkt_678_ = lean_array_uget_borrowed(v_buckets_663_, v___x_677_);
v___x_679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg(v_a_660_, v_bkt_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_700_; 
lean_inc_ref(v_buckets_663_);
lean_inc(v_size_662_);
v_isSharedCheck_700_ = !lean_is_exclusive(v_m_659_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; lean_object* v_unused_702_; 
v_unused_701_ = lean_ctor_get(v_m_659_, 1);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v_m_659_, 0);
lean_dec(v_unused_702_);
v___x_681_ = v_m_659_;
v_isShared_682_ = v_isSharedCheck_700_;
goto v_resetjp_680_;
}
else
{
lean_dec(v_m_659_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_700_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v_size_x27_684_; lean_object* v___x_685_; lean_object* v_buckets_x27_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_683_ = lean_unsigned_to_nat(1u);
v_size_x27_684_ = lean_nat_add(v_size_662_, v___x_683_);
lean_dec(v_size_662_);
lean_inc(v_bkt_678_);
v___x_685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_685_, 0, v_a_660_);
lean_ctor_set(v___x_685_, 1, v_b_661_);
lean_ctor_set(v___x_685_, 2, v_bkt_678_);
v_buckets_x27_686_ = lean_array_uset(v_buckets_663_, v___x_677_, v___x_685_);
v___x_687_ = lean_unsigned_to_nat(4u);
v___x_688_ = lean_nat_mul(v_size_x27_684_, v___x_687_);
v___x_689_ = lean_unsigned_to_nat(3u);
v___x_690_ = lean_nat_div(v___x_688_, v___x_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_array_get_size(v_buckets_x27_686_);
v___x_692_ = lean_nat_dec_le(v___x_690_, v___x_691_);
lean_dec(v___x_690_);
if (v___x_692_ == 0)
{
lean_object* v_val_693_; lean_object* v___x_695_; 
v_val_693_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1___redArg(v_buckets_x27_686_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v_val_693_);
lean_ctor_set(v___x_681_, 0, v_size_x27_684_);
v___x_695_ = v___x_681_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_size_x27_684_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_val_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
else
{
lean_object* v___x_698_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v_buckets_x27_686_);
lean_ctor_set(v___x_681_, 0, v_size_x27_684_);
v___x_698_ = v___x_681_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_size_x27_684_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_buckets_x27_686_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_dec(v_b_661_);
lean_dec(v_a_660_);
return v_m_659_;
}
}
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes___closed__4(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = lean_box(0);
v___x_714_ = lean_unsigned_to_nat(16u);
v___x_715_ = lean_mk_array(v___x_714_, v___x_713_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes___closed__5(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__4, &l_Lean_Fmt_fmtTimes___closed__4_once, _init_l_Lean_Fmt_fmtTimes___closed__4);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes___closed__6(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_719_ = lean_box(0);
v___x_720_ = ((lean_object*)(l_Lean_Fmt_fmtTimes___closed__3));
v___x_721_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__5, &l_Lean_Fmt_fmtTimes___closed__5_once, _init_l_Lean_Fmt_fmtTimes___closed__5);
v___x_722_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(v___x_721_, v___x_720_, v___x_719_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes___closed__7(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; 
v___x_723_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__6, &l_Lean_Fmt_fmtTimes___closed__6_once, _init_l_Lean_Fmt_fmtTimes___closed__6);
v___x_724_ = ((lean_object*)(l_Lean_Fmt_fmtTimes___closed__1));
v___x_725_ = 0;
v___x_726_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_723_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*2, v___x_725_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*2 + 1, v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes(void){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__7, &l_Lean_Fmt_fmtTimes___closed__7_once, _init_l_Lean_Fmt_fmtTimes___closed__7);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0(lean_object* v_00_u03b2_728_, lean_object* v_m_729_, lean_object* v_a_730_, lean_object* v_b_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(v_m_729_, v_a_730_, v_b_731_);
return v___x_732_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0(lean_object* v_00_u03b2_733_, lean_object* v_a_734_, lean_object* v_x_735_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___redArg(v_a_734_, v_x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0___boxed(lean_object* v_00_u03b2_737_, lean_object* v_a_738_, lean_object* v_x_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__0(v_00_u03b2_737_, v_a_738_, v_x_739_);
lean_dec(v_x_739_);
lean_dec(v_a_738_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1(lean_object* v_00_u03b2_742_, lean_object* v_data_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1___redArg(v_data_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_745_, lean_object* v_i_746_, lean_object* v_source_747_, lean_object* v_target_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2___redArg(v_i_746_, v_source_747_, v_target_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0_spec__1_spec__2_spec__3___redArg(v_x_751_, v_x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1(){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_763_ = l_Lean_Fmt_infixFmtAttribute;
v___x_764_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__1));
v___x_765_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__3));
v___x_766_ = l_Lean_Fmt_fmtTimes;
v___x_767_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_763_, v___x_764_, v___x_765_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___boxed(lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1();
return v_res_769_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSigmaTimes___closed__2(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_box(0);
v___x_776_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes___regBuiltin_Lean_Fmt_fmtTimes__1___closed__1));
v___x_777_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__5, &l_Lean_Fmt_fmtTimes___closed__5_once, _init_l_Lean_Fmt_fmtTimes___closed__5);
v___x_778_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(v___x_777_, v___x_776_, v___x_775_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSigmaTimes___closed__3(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; 
v___x_779_ = lean_obj_once(&l_Lean_Fmt_fmtSigmaTimes___closed__2, &l_Lean_Fmt_fmtSigmaTimes___closed__2_once, _init_l_Lean_Fmt_fmtSigmaTimes___closed__2);
v___x_780_ = ((lean_object*)(l_Lean_Fmt_fmtSigmaTimes___closed__1));
v___x_781_ = 0;
v___x_782_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_779_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*2, v___x_781_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*2 + 1, v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSigmaTimes(void){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = lean_obj_once(&l_Lean_Fmt_fmtSigmaTimes___closed__3, &l_Lean_Fmt_fmtSigmaTimes___closed__3_once, _init_l_Lean_Fmt_fmtSigmaTimes___closed__3);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1(){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_790_ = l_Lean_Fmt_infixFmtAttribute;
v___x_791_ = ((lean_object*)(l_Lean_Fmt_fmtTimes___closed__3));
v___x_792_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___closed__1));
v___x_793_ = l_Lean_Fmt_fmtSigmaTimes;
v___x_794_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_790_, v___x_791_, v___x_792_, v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1___boxed(lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSigmaTimes___regBuiltin_Lean_Fmt_fmtSigmaTimes__1();
return v_res_796_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes_x27___closed__2(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_800_ = lean_box(0);
v___x_801_ = ((lean_object*)(l_Lean_Fmt_fmtTimes_x27___closed__1));
v___x_802_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__5, &l_Lean_Fmt_fmtTimes___closed__5_once, _init_l_Lean_Fmt_fmtTimes___closed__5);
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(v___x_802_, v___x_801_, v___x_800_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes_x27___closed__3(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; lean_object* v___x_807_; 
v___x_804_ = lean_obj_once(&l_Lean_Fmt_fmtTimes_x27___closed__2, &l_Lean_Fmt_fmtTimes_x27___closed__2_once, _init_l_Lean_Fmt_fmtTimes_x27___closed__2);
v___x_805_ = ((lean_object*)(l_Lean_Fmt_fmtTimes___closed__1));
v___x_806_ = 0;
v___x_807_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set(v___x_807_, 1, v___x_804_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*2, v___x_806_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*2 + 1, v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTimes_x27(void){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = lean_obj_once(&l_Lean_Fmt_fmtTimes_x27___closed__3, &l_Lean_Fmt_fmtTimes_x27___closed__3_once, _init_l_Lean_Fmt_fmtTimes_x27___closed__3);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1(){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_818_ = l_Lean_Fmt_infixFmtAttribute;
v___x_819_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__1));
v___x_820_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__3));
v___x_821_ = l_Lean_Fmt_fmtTimes_x27;
v___x_822_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_818_, v___x_819_, v___x_820_, v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___boxed(lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1();
return v_res_824_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPSigmaTimes___closed__0(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_825_ = lean_box(0);
v___x_826_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtTimes_x27___regBuiltin_Lean_Fmt_fmtTimes_x27__1___closed__1));
v___x_827_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__5, &l_Lean_Fmt_fmtTimes___closed__5_once, _init_l_Lean_Fmt_fmtTimes___closed__5);
v___x_828_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtTimes_spec__0___redArg(v___x_827_, v___x_826_, v___x_825_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPSigmaTimes___closed__1(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_obj_once(&l_Lean_Fmt_fmtPSigmaTimes___closed__0, &l_Lean_Fmt_fmtPSigmaTimes___closed__0_once, _init_l_Lean_Fmt_fmtPSigmaTimes___closed__0);
v___x_830_ = ((lean_object*)(l_Lean_Fmt_fmtSigmaTimes___closed__1));
v___x_831_ = 0;
v___x_832_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_829_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*2, v___x_831_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*2 + 1, v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPSigmaTimes(void){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = lean_obj_once(&l_Lean_Fmt_fmtPSigmaTimes___closed__1, &l_Lean_Fmt_fmtPSigmaTimes___closed__1_once, _init_l_Lean_Fmt_fmtPSigmaTimes___closed__1);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1(){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_840_ = l_Lean_Fmt_infixFmtAttribute;
v___x_841_ = ((lean_object*)(l_Lean_Fmt_fmtTimes_x27___closed__1));
v___x_842_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___closed__1));
v___x_843_ = l_Lean_Fmt_fmtPSigmaTimes;
v___x_844_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_840_, v___x_841_, v___x_842_, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1___boxed(lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtPSigmaTimes___regBuiltin_Lean_Fmt_fmtPSigmaTimes__1();
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSetNotation(lean_object* v_x_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_Fmt_fmtSetNotation___closed__1));
lean_inc(v_x_850_);
v___x_854_ = l_Lean_Syntax_isOfKind(v_x_850_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v_x_850_);
v___x_855_ = l_Lean_Fmt_Error_partialFormatter;
v___x_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v_a_852_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; lean_object* v_lbTk_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_rbTk_862_; lean_object* v_elems_863_; lean_object* v___x_864_; 
v___x_857_ = lean_unsigned_to_nat(0u);
v_lbTk_858_ = l_Lean_Syntax_getArg(v_x_850_, v___x_857_);
v___x_859_ = lean_unsigned_to_nat(1u);
v___x_860_ = l_Lean_Syntax_getArg(v_x_850_, v___x_859_);
v___x_861_ = lean_unsigned_to_nat(2u);
v_rbTk_862_ = l_Lean_Syntax_getArg(v_x_850_, v___x_861_);
lean_dec(v_x_850_);
v_elems_863_ = l_Lean_Syntax_getArgs(v___x_860_);
lean_dec(v___x_860_);
v___x_864_ = l_Lean_Fmt_fmtArrayLit___redArg(v_lbTk_858_, v_elems_863_, v_rbTk_862_, v_a_851_, v_a_852_);
lean_dec_ref(v_elems_863_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSetNotation___boxed(lean_object* v_x_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Fmt_fmtSetNotation(v_x_865_, v_a_866_, v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1(){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_875_ = l_Lean_Fmt_fmtAttribute;
v___x_876_ = ((lean_object*)(l_Lean_Fmt_fmtSetNotation___closed__1));
v___x_877_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___closed__1));
v___x_878_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSetNotation___boxed), 3, 0);
v___x_879_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_875_, v___x_876_, v___x_877_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1___boxed(lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSetNotation___regBuiltin_Lean_Fmt_fmtSetNotation__1();
return v_res_881_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtUnifConstraint___closed__2(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; 
v___x_886_ = lean_obj_once(&l_Lean_Fmt_fmtTimes___closed__5, &l_Lean_Fmt_fmtTimes___closed__5_once, _init_l_Lean_Fmt_fmtTimes___closed__5);
v___x_887_ = ((lean_object*)(l_Lean_Fmt_fmtUnifConstraint___closed__1));
v___x_888_ = 0;
v___x_889_ = 1;
v___x_890_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_890_, 0, v___x_887_);
lean_ctor_set(v___x_890_, 1, v___x_886_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*2, v___x_889_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*2 + 1, v___x_888_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtUnifConstraint(void){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = lean_obj_once(&l_Lean_Fmt_fmtUnifConstraint___closed__2, &l_Lean_Fmt_fmtUnifConstraint___closed__2_once, _init_l_Lean_Fmt_fmtUnifConstraint___closed__2);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1(){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_902_ = l_Lean_Fmt_infixFmtAttribute;
v___x_903_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1));
v___x_904_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__3));
v___x_905_ = l_Lean_Fmt_fmtUnifConstraint;
v___x_906_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_902_, v___x_903_, v___x_904_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___boxed(lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1();
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4(size_t v_sz_909_, size_t v_i_910_, lean_object* v_bs_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_lt(v_i_910_, v_sz_909_);
if (v___x_912_ == 0)
{
return v_bs_911_;
}
else
{
lean_object* v_v_913_; lean_object* v___x_914_; lean_object* v_bs_x27_915_; size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; 
v_v_913_ = lean_array_uget(v_bs_911_, v_i_910_);
v___x_914_ = lean_unsigned_to_nat(0u);
v_bs_x27_915_ = lean_array_uset(v_bs_911_, v_i_910_, v___x_914_);
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_add(v_i_910_, v___x_916_);
v___x_918_ = lean_array_uset(v_bs_x27_915_, v_i_910_, v_v_913_);
v_i_910_ = v___x_917_;
v_bs_911_ = v___x_918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4___boxed(lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_bs_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_924_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4(v_sz_boxed_923_, v_i_boxed_924_, v_bs_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2(size_t v_sz_926_, size_t v_i_927_, lean_object* v_bs_928_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = lean_usize_dec_lt(v_i_927_, v_sz_926_);
if (v___x_929_ == 0)
{
return v_bs_928_;
}
else
{
lean_object* v_v_930_; lean_object* v_fst_931_; lean_object* v___x_932_; lean_object* v_bs_x27_933_; size_t v___x_934_; size_t v___x_935_; lean_object* v___x_936_; 
v_v_930_ = lean_array_uget_borrowed(v_bs_928_, v_i_927_);
v_fst_931_ = lean_ctor_get(v_v_930_, 0);
lean_inc(v_fst_931_);
v___x_932_ = lean_unsigned_to_nat(0u);
v_bs_x27_933_ = lean_array_uset(v_bs_928_, v_i_927_, v___x_932_);
v___x_934_ = ((size_t)1ULL);
v___x_935_ = lean_usize_add(v_i_927_, v___x_934_);
v___x_936_ = lean_array_uset(v_bs_x27_933_, v_i_927_, v_fst_931_);
v_i_927_ = v___x_935_;
v_bs_928_ = v___x_936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2___boxed(lean_object* v_sz_938_, lean_object* v_i_939_, lean_object* v_bs_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_938_);
lean_dec(v_sz_938_);
v_i_boxed_942_ = lean_unbox_usize(v_i_939_);
lean_dec(v_i_939_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2(v_sz_boxed_941_, v_i_boxed_942_, v_bs_940_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1(size_t v_sz_944_, size_t v_i_945_, lean_object* v_bs_946_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_lt(v_i_945_, v_sz_944_);
if (v___x_947_ == 0)
{
return v_bs_946_;
}
else
{
lean_object* v_v_948_; lean_object* v_snd_949_; lean_object* v___x_950_; lean_object* v_bs_x27_951_; size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v_v_948_ = lean_array_uget_borrowed(v_bs_946_, v_i_945_);
v_snd_949_ = lean_ctor_get(v_v_948_, 1);
lean_inc(v_snd_949_);
v___x_950_ = lean_unsigned_to_nat(0u);
v_bs_x27_951_ = lean_array_uset(v_bs_946_, v_i_945_, v___x_950_);
v___x_952_ = ((size_t)1ULL);
v___x_953_ = lean_usize_add(v_i_945_, v___x_952_);
v___x_954_ = lean_array_uset(v_bs_x27_951_, v_i_945_, v_snd_949_);
v_i_945_ = v___x_953_;
v_bs_946_ = v___x_954_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1___boxed(lean_object* v_sz_956_, lean_object* v_i_957_, lean_object* v_bs_958_){
_start:
{
size_t v_sz_boxed_959_; size_t v_i_boxed_960_; lean_object* v_res_961_; 
v_sz_boxed_959_ = lean_unbox_usize(v_sz_956_);
lean_dec(v_sz_956_);
v_i_boxed_960_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1(v_sz_boxed_959_, v_i_boxed_960_, v_bs_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0(size_t v_sz_966_, size_t v_i_967_, lean_object* v_bs_968_){
_start:
{
uint8_t v___x_969_; 
v___x_969_ = lean_usize_dec_lt(v_i_967_, v_sz_966_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v_bs_968_);
return v___x_970_;
}
else
{
lean_object* v_v_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v_v_971_ = lean_array_uget(v_bs_968_, v_i_967_);
v___x_972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___closed__1));
lean_inc(v_v_971_);
v___x_973_ = l_Lean_Syntax_isOfKind(v_v_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec(v_v_971_);
lean_dec_ref(v_bs_968_);
v___x_974_ = lean_box(0);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v_constraints_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v_constraints_976_ = l_Lean_Syntax_getArg(v_v_971_, v___x_975_);
v___x_977_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1));
lean_inc(v_constraints_976_);
v___x_978_ = l_Lean_Syntax_isOfKind(v_constraints_976_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_dec(v_constraints_976_);
lean_dec(v_v_971_);
lean_dec_ref(v_bs_968_);
v___x_979_ = lean_box(0);
return v___x_979_;
}
else
{
lean_object* v___x_980_; lean_object* v_bs_x27_981_; lean_object* v_commaTks_983_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_980_ = lean_unsigned_to_nat(1u);
v_bs_x27_981_ = lean_array_uset(v_bs_968_, v_i_967_, v___x_975_);
v___x_989_ = l_Lean_Syntax_getArg(v_v_971_, v___x_980_);
lean_dec(v_v_971_);
v___x_990_ = l_Lean_Syntax_isNone(v___x_989_);
if (v___x_990_ == 0)
{
uint8_t v___x_991_; 
lean_inc(v___x_989_);
v___x_991_ = l_Lean_Syntax_matchesNull(v___x_989_, v___x_980_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_dec(v___x_989_);
lean_dec_ref(v_bs_x27_981_);
lean_dec(v_constraints_976_);
v___x_992_ = lean_box(0);
return v___x_992_;
}
else
{
lean_object* v_commaTks_993_; lean_object* v___x_994_; 
v_commaTks_993_ = l_Lean_Syntax_getArg(v___x_989_, v___x_975_);
lean_dec(v___x_989_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_commaTks_993_);
v_commaTks_983_ = v___x_994_;
goto v___jp_982_;
}
}
else
{
lean_object* v___x_995_; 
lean_dec(v___x_989_);
v___x_995_ = lean_box(0);
v_commaTks_983_ = v___x_995_;
goto v___jp_982_;
}
v___jp_982_:
{
lean_object* v___x_984_; size_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; 
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_constraints_976_);
lean_ctor_set(v___x_984_, 1, v_commaTks_983_);
v___x_985_ = ((size_t)1ULL);
v___x_986_ = lean_usize_add(v_i_967_, v___x_985_);
v___x_987_ = lean_array_uset(v_bs_x27_981_, v_i_967_, v___x_984_);
v_i_967_ = v___x_986_;
v_bs_968_ = v___x_987_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0___boxed(lean_object* v_sz_996_, lean_object* v_i_997_, lean_object* v_bs_998_){
_start:
{
size_t v_sz_boxed_999_; size_t v_i_boxed_1000_; lean_object* v_res_1001_; 
v_sz_boxed_999_ = lean_unbox_usize(v_sz_996_);
lean_dec(v_sz_996_);
v_i_boxed_1000_ = lean_unbox_usize(v_i_997_);
lean_dec(v_i_997_);
v_res_1001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0(v_sz_boxed_999_, v_i_boxed_1000_, v_bs_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3(size_t v_sz_1002_, size_t v_i_1003_, lean_object* v_bs_1004_){
_start:
{
uint8_t v___x_1005_; 
v___x_1005_ = lean_usize_dec_lt(v_i_1003_, v_sz_1002_);
if (v___x_1005_ == 0)
{
return v_bs_1004_;
}
else
{
lean_object* v_v_1006_; lean_object* v___x_1007_; lean_object* v_bs_x27_1008_; size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; 
v_v_1006_ = lean_array_uget(v_bs_1004_, v_i_1003_);
v___x_1007_ = lean_unsigned_to_nat(0u);
v_bs_x27_1008_ = lean_array_uset(v_bs_1004_, v_i_1003_, v___x_1007_);
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_add(v_i_1003_, v___x_1009_);
v___x_1011_ = lean_array_uset(v_bs_x27_1008_, v_i_1003_, v_v_1006_);
v_i_1003_ = v___x_1010_;
v_bs_1004_ = v___x_1011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3___boxed(lean_object* v_sz_1013_, lean_object* v_i_1014_, lean_object* v_bs_1015_){
_start:
{
size_t v_sz_boxed_1016_; size_t v_i_boxed_1017_; lean_object* v_res_1018_; 
v_sz_boxed_1016_ = lean_unbox_usize(v_sz_1013_);
lean_dec(v_sz_1013_);
v_i_boxed_1017_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_res_1018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3(v_sz_boxed_1016_, v_i_boxed_1017_, v_bs_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnifHint(lean_object* v_x_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1045_; uint8_t v___x_1046_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; size_t v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; size_t v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v_declId_x3f_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; 
v___x_1045_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__1));
lean_inc(v_x_1042_);
v___x_1046_ = l_Lean_Syntax_isOfKind(v_x_1042_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec(v_x_1042_);
v___x_1184_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v_a_1044_);
return v___x_1185_;
}
else
{
lean_object* v___x_1186_; lean_object* v_docComment_x3f_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1212_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1186_);
v___x_1213_ = l_Lean_Syntax_isNone(v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1212_);
v___x_1215_ = l_Lean_Syntax_matchesNull(v___x_1212_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec(v___x_1212_);
lean_dec(v_x_1042_);
v___x_1216_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_a_1044_);
return v___x_1217_;
}
else
{
lean_object* v_docComment_x3f_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_docComment_x3f_1218_ = l_Lean_Syntax_getArg(v___x_1212_, v___x_1186_);
lean_dec(v___x_1212_);
v___x_1219_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__11));
lean_inc(v_docComment_x3f_1218_);
v___x_1220_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec(v_docComment_x3f_1218_);
lean_dec(v_x_1042_);
v___x_1221_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_a_1044_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_docComment_x3f_1218_);
v_docComment_x3f_1188_ = v___x_1223_;
v___y_1189_ = v_a_1043_;
v___y_1190_ = v_a_1044_;
goto v___jp_1187_;
}
}
}
else
{
lean_object* v___x_1224_; 
lean_dec(v___x_1212_);
v___x_1224_ = lean_box(0);
v_docComment_x3f_1188_ = v___x_1224_;
v___y_1189_ = v_a_1043_;
v___y_1190_ = v_a_1044_;
goto v___jp_1187_;
}
v___jp_1187_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__6));
lean_inc(v___x_1192_);
v___x_1194_ = l_Lean_Syntax_isOfKind(v___x_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec(v___x_1192_);
lean_dec(v_docComment_x3f_1188_);
lean_dec(v_x_1042_);
v___x_1195_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___y_1190_);
return v___x_1196_;
}
else
{
lean_object* v___x_1197_; lean_object* v_unifHintTk_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1197_ = lean_unsigned_to_nat(2u);
v_unifHintTk_1198_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1197_);
v___x_1199_ = lean_unsigned_to_nat(3u);
v___x_1200_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1199_);
v___x_1201_ = l_Lean_Syntax_isNone(v___x_1200_);
if (v___x_1201_ == 0)
{
uint8_t v___x_1202_; 
lean_inc(v___x_1200_);
v___x_1202_ = l_Lean_Syntax_matchesNull(v___x_1200_, v___x_1191_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec(v___x_1200_);
lean_dec(v_unifHintTk_1198_);
lean_dec(v___x_1192_);
lean_dec(v_docComment_x3f_1188_);
lean_dec(v_x_1042_);
v___x_1203_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v___y_1190_);
return v___x_1204_;
}
else
{
lean_object* v_declId_x3f_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v_declId_x3f_1205_ = l_Lean_Syntax_getArg(v___x_1200_, v___x_1186_);
lean_dec(v___x_1200_);
v___x_1206_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__8));
lean_inc(v_declId_x3f_1205_);
v___x_1207_ = l_Lean_Syntax_isOfKind(v_declId_x3f_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_declId_x3f_1205_);
lean_dec(v_unifHintTk_1198_);
lean_dec(v___x_1192_);
lean_dec(v_docComment_x3f_1188_);
lean_dec(v_x_1042_);
v___x_1208_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___y_1190_);
return v___x_1209_;
}
else
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_declId_x3f_1205_);
v___y_1144_ = v_unifHintTk_1198_;
v___y_1145_ = v___x_1192_;
v___y_1146_ = v___x_1197_;
v___y_1147_ = v_docComment_x3f_1188_;
v_declId_x3f_1148_ = v___x_1210_;
v___y_1149_ = v___y_1189_;
v___y_1150_ = v___y_1190_;
goto v___jp_1143_;
}
}
}
else
{
lean_object* v___x_1211_; 
lean_dec(v___x_1200_);
v___x_1211_ = lean_box(0);
v___y_1144_ = v_unifHintTk_1198_;
v___y_1145_ = v___x_1192_;
v___y_1146_ = v___x_1197_;
v___y_1147_ = v_docComment_x3f_1188_;
v_declId_x3f_1148_ = v___x_1211_;
v___y_1149_ = v___y_1189_;
v___y_1150_ = v___y_1190_;
goto v___jp_1143_;
}
}
}
}
v___jp_1047_:
{
size_t v_sz_1062_; lean_object* v___x_1063_; size_t v_sz_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_sz_1062_ = lean_array_size(v___y_1059_);
v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3(v_sz_1062_, v___y_1056_, v___y_1059_);
v_sz_1064_ = lean_array_size(v___x_1063_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4(v_sz_1064_, v___y_1056_, v___x_1063_);
lean_inc_n(v___y_1048_, 2);
v___x_1066_ = l_Lean_Fmt_fmtDeclarationSignature(v___y_1054_, v___y_1048_, v___y_1061_, v___x_1065_, v___y_1048_, v___y_1048_, v___y_1057_, v___y_1052_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
v_a_1068_ = lean_ctor_get(v___x_1066_, 1);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1066_, 2);
v___x_1069_ = l_Lean_Fmt_fmt(v___y_1051_, v___y_1057_, v_a_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
v_a_1071_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1069_, 2);
v___x_1072_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(v___y_1058_, v___y_1049_);
lean_dec_ref(v___y_1049_);
lean_dec_ref(v___y_1058_);
v___x_1073_ = l_Lean_Fmt_fmtTSepArray___redArg(v___x_1072_, v___y_1057_, v_a_1071_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
v_a_1075_ = lean_ctor_get(v___x_1073_, 1);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1073_, 2);
v___x_1076_ = l_Lean_Syntax_getArg(v_x_1042_, v___y_1055_);
lean_dec(v_x_1042_);
v___x_1077_ = l_Lean_Fmt_fmtAtomic(v___x_1076_, v___y_1057_, v_a_1075_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v_a_1079_; lean_object* v___x_1080_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
v_a_1079_ = lean_ctor_get(v___x_1077_, 1);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1077_, 2);
v___x_1080_ = l_Lean_Fmt_fmt(v___y_1053_, v___y_1057_, v_a_1079_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1103_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_a_1082_ = lean_ctor_get(v___x_1080_, 1);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1084_ = v___x_1080_;
v_isShared_1085_ = v_isSharedCheck_1103_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1103_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1086_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__2));
v___x_1087_ = 0;
v___x_1088_ = l_Lean_Fmt_Layouts_sepLines(v___x_1086_, v_a_1074_, v___x_1087_);
lean_dec(v_a_1074_);
v___x_1089_ = lean_unsigned_to_nat(3u);
v___x_1090_ = lean_mk_empty_array_with_capacity(v___x_1089_);
v___x_1091_ = lean_array_push(v___x_1090_, v___x_1088_);
v___x_1092_ = lean_array_push(v___x_1091_, v_a_1078_);
v___x_1093_ = lean_array_push(v___x_1092_, v_a_1081_);
v___x_1094_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_1093_, v___x_1046_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = l_Lean_Fmt_Layouts_whereDeclaration(v_a_1067_, v_a_1070_, v___x_1094_);
v___x_1096_ = lean_mk_empty_array_with_capacity(v___y_1050_);
v___x_1097_ = lean_array_push(v___x_1096_, v___y_1060_);
v___x_1098_ = lean_array_push(v___x_1097_, v___x_1095_);
v___x_1099_ = l_Lean_Fmt_Layouts_lines(v___x_1098_);
lean_dec_ref(v___x_1098_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1099_);
v___x_1101_ = v___x_1084_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_a_1082_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
lean_dec(v_a_1078_);
lean_dec(v_a_1074_);
lean_dec(v_a_1070_);
lean_dec(v_a_1067_);
lean_dec_ref(v___y_1060_);
return v___x_1080_;
}
}
else
{
lean_dec(v_a_1074_);
lean_dec(v_a_1070_);
lean_dec(v_a_1067_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1053_);
return v___x_1077_;
}
}
else
{
lean_object* v_a_1104_; lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v_a_1070_);
lean_dec(v_a_1067_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1053_);
lean_dec(v_x_1042_);
v_a_1104_ = lean_ctor_get(v___x_1073_, 0);
v_a_1105_ = lean_ctor_get(v___x_1073_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1073_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_inc(v_a_1104_);
lean_dec(v___x_1073_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1104_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_dec(v_a_1067_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1049_);
lean_dec(v_x_1042_);
return v___x_1069_;
}
}
else
{
lean_dec_ref(v___y_1060_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1053_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1049_);
lean_dec(v_x_1042_);
return v___x_1066_;
}
}
v___jp_1113_:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_Fmt_fmt_x3f(v___y_1127_, v___y_1121_, v___y_1125_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
v_a_1130_ = lean_ctor_get(v___x_1128_, 1);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1128_, 2);
v___x_1131_ = lean_mk_empty_array_with_capacity(v___y_1116_);
v___x_1132_ = lean_array_push(v___x_1131_, v___y_1123_);
v___x_1133_ = lean_array_push(v___x_1132_, v___y_1114_);
v___x_1134_ = lean_box(0);
if (lean_obj_tag(v___y_1126_) == 0)
{
v___y_1048_ = v___x_1134_;
v___y_1049_ = v___y_1115_;
v___y_1050_ = v___y_1116_;
v___y_1051_ = v___y_1117_;
v___y_1052_ = v_a_1130_;
v___y_1053_ = v___y_1118_;
v___y_1054_ = v___x_1133_;
v___y_1055_ = v___y_1119_;
v___y_1056_ = v___y_1120_;
v___y_1057_ = v___y_1121_;
v___y_1058_ = v___y_1122_;
v___y_1059_ = v___y_1124_;
v___y_1060_ = v_a_1129_;
v___y_1061_ = v___x_1134_;
goto v___jp_1047_;
}
else
{
lean_object* v_val_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_val_1135_ = lean_ctor_get(v___y_1126_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___y_1126_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___y_1126_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_val_1135_);
lean_dec(v___y_1126_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_val_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
v___y_1048_ = v___x_1134_;
v___y_1049_ = v___y_1115_;
v___y_1050_ = v___y_1116_;
v___y_1051_ = v___y_1117_;
v___y_1052_ = v_a_1130_;
v___y_1053_ = v___y_1118_;
v___y_1054_ = v___x_1133_;
v___y_1055_ = v___y_1119_;
v___y_1056_ = v___y_1120_;
v___y_1057_ = v___y_1121_;
v___y_1058_ = v___y_1122_;
v___y_1059_ = v___y_1124_;
v___y_1060_ = v_a_1129_;
v___y_1061_ = v___x_1140_;
goto v___jp_1047_;
}
}
}
}
else
{
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec(v_x_1042_);
return v___x_1128_;
}
}
v___jp_1143_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; size_t v_sz_1154_; size_t v___x_1155_; lean_object* v___x_1156_; 
v___x_1151_ = lean_unsigned_to_nat(6u);
v___x_1152_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1151_);
v___x_1153_ = l_Lean_Syntax_getArgs(v___x_1152_);
lean_dec(v___x_1152_);
v_sz_1154_ = lean_array_size(v___x_1153_);
v___x_1155_ = ((size_t)0ULL);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__0(v_sz_1154_, v___x_1155_, v___x_1153_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_declId_x3f_1148_);
lean_dec(v___y_1147_);
lean_dec(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec(v_x_1042_);
v___x_1157_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___y_1150_);
return v___x_1158_;
}
else
{
lean_object* v_val_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_val_1159_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_val_1159_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1160_ = lean_unsigned_to_nat(8u);
v___x_1161_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1160_);
v___x_1162_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifConstraint___regBuiltin_Lean_Fmt_fmtUnifConstraint__1___closed__1));
lean_inc(v___x_1161_);
v___x_1163_ = l_Lean_Syntax_isOfKind(v___x_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec(v___x_1161_);
lean_dec(v_val_1159_);
lean_dec(v_declId_x3f_1148_);
lean_dec(v___y_1147_);
lean_dec(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec(v_x_1042_);
v___x_1164_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___y_1150_);
return v___x_1165_;
}
else
{
size_t v_sz_1166_; lean_object* v_commaTks_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_whereTk_1171_; lean_object* v_constraints_1172_; lean_object* v___x_1173_; lean_object* v_binders_1174_; 
v_sz_1166_ = lean_array_size(v_val_1159_);
lean_inc(v_val_1159_);
v_commaTks_1167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1(v_sz_1166_, v___x_1155_, v_val_1159_);
v___x_1168_ = lean_unsigned_to_nat(4u);
v___x_1169_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1168_);
v___x_1170_ = lean_unsigned_to_nat(5u);
v_whereTk_1171_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1170_);
v_constraints_1172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2(v_sz_1166_, v___x_1155_, v_val_1159_);
v___x_1173_ = lean_unsigned_to_nat(7u);
v_binders_1174_ = l_Lean_Syntax_getArgs(v___x_1169_);
lean_dec(v___x_1169_);
if (lean_obj_tag(v___y_1147_) == 0)
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_box(0);
v___y_1114_ = v___y_1144_;
v___y_1115_ = v_commaTks_1167_;
v___y_1116_ = v___y_1146_;
v___y_1117_ = v_whereTk_1171_;
v___y_1118_ = v___x_1161_;
v___y_1119_ = v___x_1173_;
v___y_1120_ = v___x_1155_;
v___y_1121_ = v___y_1149_;
v___y_1122_ = v_constraints_1172_;
v___y_1123_ = v___y_1145_;
v___y_1124_ = v_binders_1174_;
v___y_1125_ = v___y_1150_;
v___y_1126_ = v_declId_x3f_1148_;
v___y_1127_ = v___x_1175_;
goto v___jp_1113_;
}
else
{
lean_object* v_val_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_val_1176_ = lean_ctor_get(v___y_1147_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___y_1147_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___y_1147_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_val_1176_);
lean_dec(v___y_1147_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_val_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
v___y_1114_ = v___y_1144_;
v___y_1115_ = v_commaTks_1167_;
v___y_1116_ = v___y_1146_;
v___y_1117_ = v_whereTk_1171_;
v___y_1118_ = v___x_1161_;
v___y_1119_ = v___x_1173_;
v___y_1120_ = v___x_1155_;
v___y_1121_ = v___y_1149_;
v___y_1122_ = v_constraints_1172_;
v___y_1123_ = v___y_1145_;
v___y_1124_ = v_binders_1174_;
v___y_1125_ = v___y_1150_;
v___y_1126_ = v_declId_x3f_1148_;
v___y_1127_ = v___x_1181_;
goto v___jp_1113_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnifHint___boxed(lean_object* v_x_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Fmt_fmtUnifHint(v_x_1225_, v_a_1226_, v_a_1227_);
lean_dec_ref(v_a_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1(){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1235_ = l_Lean_Fmt_fmtAttribute;
v___x_1236_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__1));
v___x_1237_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___closed__1));
v___x_1238_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtUnifHint___boxed), 3, 0);
v___x_1239_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1235_, v___x_1236_, v___x_1237_, v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1___boxed(lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtUnifHint___regBuiltin_Lean_Fmt_fmtUnifHint__1();
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0(size_t v_sz_1245_, size_t v_i_1246_, lean_object* v_bs_1247_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_usize_dec_lt(v_i_1246_, v_sz_1245_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_bs_1247_);
return v___x_1249_;
}
else
{
lean_object* v_v_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_v_1250_ = lean_array_uget(v_bs_1247_, v_i_1246_);
v___x_1251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__1));
lean_inc(v_v_1250_);
v___x_1252_ = l_Lean_Syntax_isOfKind(v_v_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec(v_v_1250_);
lean_dec_ref(v_bs_1247_);
v___x_1253_ = lean_box(0);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_bs_x27_1256_; lean_object* v_parents_1257_; lean_object* v_commaTks_1259_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_unsigned_to_nat(1u);
v_bs_x27_1256_ = lean_array_uset(v_bs_1247_, v_i_1246_, v___x_1254_);
v_parents_1257_ = l_Lean_Syntax_getArg(v_v_1250_, v___x_1254_);
v___x_1265_ = l_Lean_Syntax_getArg(v_v_1250_, v___x_1255_);
lean_dec(v_v_1250_);
v___x_1266_ = l_Lean_Syntax_isNone(v___x_1265_);
if (v___x_1266_ == 0)
{
uint8_t v___x_1267_; 
lean_inc(v___x_1265_);
v___x_1267_ = l_Lean_Syntax_matchesNull(v___x_1265_, v___x_1255_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec(v___x_1265_);
lean_dec(v_parents_1257_);
lean_dec_ref(v_bs_x27_1256_);
v___x_1268_ = lean_box(0);
return v___x_1268_;
}
else
{
lean_object* v_commaTks_1269_; lean_object* v___x_1270_; 
v_commaTks_1269_ = l_Lean_Syntax_getArg(v___x_1265_, v___x_1254_);
lean_dec(v___x_1265_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_commaTks_1269_);
v_commaTks_1259_ = v___x_1270_;
goto v___jp_1258_;
}
}
else
{
lean_object* v___x_1271_; 
lean_dec(v___x_1265_);
v___x_1271_ = lean_box(0);
v_commaTks_1259_ = v___x_1271_;
goto v___jp_1258_;
}
v___jp_1258_:
{
lean_object* v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_parents_1257_);
lean_ctor_set(v___x_1260_, 1, v_commaTks_1259_);
v___x_1261_ = ((size_t)1ULL);
v___x_1262_ = lean_usize_add(v_i_1246_, v___x_1261_);
v___x_1263_ = lean_array_uset(v_bs_x27_1256_, v_i_1246_, v___x_1260_);
v_i_1246_ = v___x_1262_;
v_bs_1247_ = v___x_1263_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___boxed(lean_object* v_sz_1272_, lean_object* v_i_1273_, lean_object* v_bs_1274_){
_start:
{
size_t v_sz_boxed_1275_; size_t v_i_boxed_1276_; lean_object* v_res_1277_; 
v_sz_boxed_1275_ = lean_unbox_usize(v_sz_1272_);
lean_dec(v_sz_1272_);
v_i_boxed_1276_ = lean_unbox_usize(v_i_1273_);
lean_dec(v_i_1273_);
v_res_1277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0(v_sz_boxed_1275_, v_i_boxed_1276_, v_bs_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtClassAbbrev(lean_object* v_x_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_Fmt_fmtClassAbbrev___closed__1));
lean_inc(v_x_1296_);
v___x_1300_ = l_Lean_Syntax_isOfKind(v_x_1296_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec(v_x_1296_);
v___x_1301_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v_a_1298_);
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; lean_object* v_mods_1304_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1303_ = lean_unsigned_to_nat(0u);
v_mods_1304_ = l_Lean_Syntax_getArg(v_x_1296_, v___x_1303_);
v___x_1341_ = ((lean_object*)(l_Lean_Fmt_fmtClassAbbrev___closed__3));
lean_inc(v_mods_1304_);
v___x_1342_ = l_Lean_Syntax_isOfKind(v_mods_1304_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec(v_mods_1304_);
lean_dec(v_x_1296_);
v___x_1343_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v_a_1298_);
return v___x_1344_;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1345_ = lean_unsigned_to_nat(3u);
v___x_1346_ = l_Lean_Syntax_getArg(v_x_1296_, v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Lean_Fmt_fmtClassAbbrev___closed__5));
lean_inc(v___x_1346_);
v___x_1348_ = l_Lean_Syntax_isOfKind(v___x_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v___x_1346_);
lean_dec(v_mods_1304_);
lean_dec(v_x_1296_);
v___x_1349_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v_a_1298_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; lean_object* v_classTk_1352_; lean_object* v___x_1353_; lean_object* v_abbrevTk_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_typeAscriptionTk_x3f_1358_; lean_object* v_type_x3f_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1351_ = lean_unsigned_to_nat(1u);
v_classTk_1352_ = l_Lean_Syntax_getArg(v_x_1296_, v___x_1351_);
v___x_1353_ = lean_unsigned_to_nat(2u);
v_abbrevTk_1354_ = l_Lean_Syntax_getArg(v_x_1296_, v___x_1353_);
v___x_1355_ = lean_unsigned_to_nat(4u);
v___x_1356_ = l_Lean_Syntax_getArg(v_x_1296_, v___x_1355_);
v___x_1400_ = lean_unsigned_to_nat(5u);
v___x_1401_ = l_Lean_Syntax_getArg(v_x_1296_, v___x_1400_);
v___x_1402_ = l_Lean_Syntax_isNone(v___x_1401_);
if (v___x_1402_ == 0)
{
uint8_t v___x_1403_; 
lean_inc(v___x_1401_);
v___x_1403_ = l_Lean_Syntax_matchesNull(v___x_1401_, v___x_1353_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec(v___x_1401_);
lean_dec(v___x_1356_);
lean_dec(v_abbrevTk_1354_);
lean_dec(v_classTk_1352_);
lean_dec(v___x_1346_);
lean_dec(v_mods_1304_);
lean_dec(v_x_1296_);
v___x_1404_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
lean_ctor_set(v___x_1405_, 1, v_a_1298_);
return v___x_1405_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_1406_; lean_object* v_type_x3f_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_typeAscriptionTk_x3f_1406_ = l_Lean_Syntax_getArg(v___x_1401_, v___x_1303_);
v_type_x3f_1407_ = l_Lean_Syntax_getArg(v___x_1401_, v___x_1351_);
lean_dec(v___x_1401_);
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_typeAscriptionTk_x3f_1406_);
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_type_x3f_1407_);
v_typeAscriptionTk_x3f_1358_ = v___x_1408_;
v_type_x3f_1359_ = v___x_1409_;
v___y_1360_ = v_a_1297_;
v___y_1361_ = v_a_1298_;
goto v___jp_1357_;
}
}
else
{
lean_object* v___x_1410_; 
lean_dec(v___x_1401_);
v___x_1410_ = lean_box(0);
v_typeAscriptionTk_x3f_1358_ = v___x_1410_;
v_type_x3f_1359_ = v___x_1410_;
v___y_1360_ = v_a_1297_;
v___y_1361_ = v_a_1298_;
goto v___jp_1357_;
}
v___jp_1357_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; size_t v_sz_1365_; size_t v___x_1366_; lean_object* v___x_1367_; 
v___x_1362_ = lean_unsigned_to_nat(7u);
v___x_1363_ = l_Lean_Syntax_getArg(v_x_1296_, v___x_1362_);
v___x_1364_ = l_Lean_Syntax_getArgs(v___x_1363_);
lean_dec(v___x_1363_);
v_sz_1365_ = lean_array_size(v___x_1364_);
v___x_1366_ = ((size_t)0ULL);
v___x_1367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0(v_sz_1365_, v___x_1366_, v___x_1364_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v_type_x3f_1359_);
lean_dec(v_typeAscriptionTk_x3f_1358_);
lean_dec(v___x_1356_);
lean_dec(v_abbrevTk_1354_);
lean_dec(v_classTk_1352_);
lean_dec(v___x_1346_);
lean_dec(v_mods_1304_);
lean_dec(v_x_1296_);
v___x_1368_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
lean_ctor_set(v___x_1369_, 1, v___y_1361_);
return v___x_1369_;
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1399_; 
v_val_1370_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1372_ = v___x_1367_;
v_isShared_1373_ = v_isSharedCheck_1399_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_val_1370_);
lean_dec(v___x_1367_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1399_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v_colonEqTk_1375_; size_t v_sz_1376_; lean_object* v_commaTks_1377_; lean_object* v_parents_1378_; lean_object* v_binders_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1374_ = lean_unsigned_to_nat(6u);
v_colonEqTk_1375_ = l_Lean_Syntax_getArg(v_x_1296_, v___x_1374_);
lean_dec(v_x_1296_);
v_sz_1376_ = lean_array_size(v_val_1370_);
lean_inc(v_val_1370_);
v_commaTks_1377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__1(v_sz_1376_, v___x_1366_, v_val_1370_);
v_parents_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__2(v_sz_1376_, v___x_1366_, v_val_1370_);
v_binders_1379_ = l_Lean_Syntax_getArgs(v___x_1356_);
lean_dec(v___x_1356_);
v___x_1380_ = lean_mk_empty_array_with_capacity(v___x_1353_);
v___x_1381_ = lean_array_push(v___x_1380_, v_classTk_1352_);
v___x_1382_ = lean_array_push(v___x_1381_, v_abbrevTk_1354_);
v___x_1383_ = lean_box(0);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1346_);
v___x_1385_ = v___x_1372_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1346_);
v___x_1385_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
size_t v_sz_1386_; lean_object* v___x_1387_; size_t v_sz_1388_; lean_object* v___x_1389_; 
v_sz_1386_ = lean_array_size(v_binders_1379_);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__3(v_sz_1386_, v___x_1366_, v_binders_1379_);
v_sz_1388_ = lean_array_size(v___x_1387_);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtUnifHint_spec__4(v_sz_1388_, v___x_1366_, v___x_1387_);
if (lean_obj_tag(v_type_x3f_1359_) == 0)
{
v___y_1306_ = v___x_1389_;
v___y_1307_ = v___y_1360_;
v___y_1308_ = v_parents_1378_;
v___y_1309_ = v___y_1361_;
v___y_1310_ = v_colonEqTk_1375_;
v___y_1311_ = v_typeAscriptionTk_x3f_1358_;
v___y_1312_ = v___x_1382_;
v___y_1313_ = v___x_1383_;
v___y_1314_ = v_commaTks_1377_;
v___y_1315_ = v___x_1385_;
v___y_1316_ = v___x_1383_;
goto v___jp_1305_;
}
else
{
lean_object* v_val_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
v_val_1390_ = lean_ctor_get(v_type_x3f_1359_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_type_x3f_1359_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v_type_x3f_1359_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_val_1390_);
lean_dec(v_type_x3f_1359_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_val_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
v___y_1306_ = v___x_1389_;
v___y_1307_ = v___y_1360_;
v___y_1308_ = v_parents_1378_;
v___y_1309_ = v___y_1361_;
v___y_1310_ = v_colonEqTk_1375_;
v___y_1311_ = v_typeAscriptionTk_x3f_1358_;
v___y_1312_ = v___x_1382_;
v___y_1313_ = v___x_1383_;
v___y_1314_ = v_commaTks_1377_;
v___y_1315_ = v___x_1385_;
v___y_1316_ = v___x_1395_;
goto v___jp_1305_;
}
}
}
}
}
}
}
}
}
v___jp_1305_:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_Fmt_fmtDeclarationSignature(v___y_1312_, v___y_1313_, v___y_1315_, v___y_1306_, v___y_1311_, v___y_1316_, v___y_1307_, v___y_1309_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v_a_1319_; lean_object* v___x_1320_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
v_a_1319_ = lean_ctor_get(v___x_1317_, 1);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1317_, 2);
v___x_1320_ = l_Lean_Fmt_fmt(v___y_1310_, v___y_1307_, v_a_1319_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
v_a_1322_ = lean_ctor_get(v___x_1320_, 1);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1320_, 2);
v___x_1323_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Syntax_TSepArray_ofElemsAndSeps___redArg(v___y_1308_, v___y_1314_);
lean_dec_ref(v___y_1314_);
lean_dec_ref(v___y_1308_);
v___x_1324_ = l_Lean_Fmt_fmtTSepArray___redArg(v___x_1323_, v___y_1307_, v_a_1322_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v_a_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
v_a_1326_ = lean_ctor_get(v___x_1324_, 1);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1324_, 2);
v___x_1327_ = ((lean_object*)(l_Lean_Fmt_fmtUnifHint___closed__2));
v___x_1328_ = l_Lean_Fmt_Layouts_sepFill(v___x_1327_, v_a_1325_);
lean_dec(v_a_1325_);
v___x_1329_ = 0;
v___x_1330_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1318_, v_a_1321_, v___x_1328_, v___x_1329_);
v___x_1331_ = l_Lean_Fmt_fmtDeclWithDeclModifiers(v_mods_1304_, v___x_1330_, v___y_1307_, v_a_1326_);
return v___x_1331_;
}
else
{
lean_object* v_a_1332_; lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_a_1321_);
lean_dec(v_a_1318_);
lean_dec(v_mods_1304_);
v_a_1332_ = lean_ctor_get(v___x_1324_, 0);
v_a_1333_ = lean_ctor_get(v___x_1324_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1324_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_inc(v_a_1332_);
lean_dec(v___x_1324_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1332_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_dec(v_a_1318_);
lean_dec_ref(v___y_1314_);
lean_dec_ref(v___y_1308_);
lean_dec(v_mods_1304_);
return v___x_1320_;
}
}
else
{
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1308_);
lean_dec(v_mods_1304_);
return v___x_1317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtClassAbbrev___boxed(lean_object* v_x_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Fmt_fmtClassAbbrev(v_x_1411_, v_a_1412_, v_a_1413_);
lean_dec_ref(v_a_1412_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1(){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1421_ = l_Lean_Fmt_fmtAttribute;
v___x_1422_ = ((lean_object*)(l_Lean_Fmt_fmtClassAbbrev___closed__1));
v___x_1423_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___closed__1));
v___x_1424_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtClassAbbrev___boxed), 3, 0);
v___x_1425_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1421_, v___x_1422_, v___x_1423_, v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1___boxed(lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtClassAbbrev___regBuiltin_Lean_Fmt_fmtClassAbbrev__1();
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFunext(lean_object* v_x_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_Fmt_fmtFunext___closed__1));
lean_inc(v_x_1431_);
v___x_1435_ = l_Lean_Syntax_isOfKind(v_x_1431_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v_x_1431_);
v___x_1436_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v_a_1433_);
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; lean_object* v_funextTk_1439_; lean_object* v___x_1440_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v_funextTk_1439_ = l_Lean_Syntax_getArg(v_x_1431_, v___x_1438_);
v___x_1440_ = l_Lean_Fmt_fmt(v_funextTk_1439_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v_a_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v_args_1445_; lean_object* v___x_1446_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
v_a_1442_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1440_, 2);
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = l_Lean_Syntax_getArg(v_x_1431_, v___x_1443_);
lean_dec(v_x_1431_);
v_args_1445_ = l_Lean_Syntax_getArgs(v___x_1444_);
lean_dec(v___x_1444_);
v___x_1446_ = l_Lean_Fmt_fmtArray___redArg(v_args_1445_, v_a_1432_, v_a_1442_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1461_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_a_1448_ = lean_ctor_get(v___x_1446_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1450_ = v___x_1446_;
v_isShared_1451_ = v_isSharedCheck_1461_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1461_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1452_ = lean_mk_empty_array_with_capacity(v___x_1443_);
v___x_1453_ = lean_array_push(v___x_1452_, v_a_1441_);
v___x_1454_ = l_Array_append___redArg(v___x_1453_, v_a_1447_);
lean_dec(v_a_1447_);
v___x_1455_ = 0;
v___x_1456_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1456_, 0, v___x_1435_);
lean_ctor_set_uint8(v___x_1456_, 1, v___x_1455_);
lean_ctor_set_uint8(v___x_1456_, 2, v___x_1435_);
lean_ctor_set_uint8(v___x_1456_, 3, v___x_1455_);
v___x_1457_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1454_, v___x_1456_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1457_);
v___x_1459_ = v___x_1450_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_a_1448_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_a_1441_);
v_a_1462_ = lean_ctor_get(v___x_1446_, 0);
v_a_1463_ = lean_ctor_get(v___x_1446_, 1);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1446_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_inc(v_a_1462_);
lean_dec(v___x_1446_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1462_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_dec(v_x_1431_);
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFunext___boxed(lean_object* v_x_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Fmt_fmtFunext(v_x_1471_, v_a_1472_, v_a_1473_);
lean_dec_ref(v_a_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1(){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1481_ = l_Lean_Fmt_fmtAttribute;
v___x_1482_ = ((lean_object*)(l_Lean_Fmt_fmtFunext___closed__1));
v___x_1483_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___closed__1));
v___x_1484_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtFunext___boxed), 3, 0);
v___x_1485_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1481_, v___x_1482_, v___x_1483_, v___x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1___boxed(lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtFunext___regBuiltin_Lean_Fmt_fmtFunext__1();
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCdotTactic(lean_object* v_x_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_Fmt_fmtCdotTactic___closed__1));
lean_inc(v_x_1503_);
v___x_1507_ = l_Lean_Syntax_isOfKind(v_x_1503_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v_x_1503_);
v___x_1508_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v_a_1505_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1510_ = lean_unsigned_to_nat(0u);
v___x_1511_ = l_Lean_Syntax_getArg(v_x_1503_, v___x_1510_);
v___x_1512_ = ((lean_object*)(l_Lean_Fmt_fmtCdotTactic___closed__3));
lean_inc(v___x_1511_);
v___x_1513_ = l_Lean_Syntax_isOfKind(v___x_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v___x_1511_);
lean_dec(v_x_1503_);
v___x_1514_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v_a_1505_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = l_Lean_Syntax_getArg(v_x_1503_, v___x_1516_);
lean_dec(v_x_1503_);
v___x_1518_ = ((lean_object*)(l_Lean_Fmt_fmtCdotTactic___closed__6));
lean_inc(v___x_1517_);
v___x_1519_ = l_Lean_Syntax_isOfKind(v___x_1517_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec(v___x_1517_);
lean_dec(v___x_1511_);
v___x_1520_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v_a_1505_);
return v___x_1521_;
}
else
{
lean_object* v_cdotTk_1522_; lean_object* v___x_1523_; 
v_cdotTk_1522_ = l_Lean_Syntax_getArg(v___x_1511_, v___x_1510_);
lean_dec(v___x_1511_);
v___x_1523_ = l_Lean_Fmt_fmt(v_cdotTk_1522_, v_a_1504_, v_a_1505_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
v_a_1525_ = lean_ctor_get(v___x_1523_, 1);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1523_, 2);
v___x_1526_ = l_Lean_Fmt_fmt(v___x_1517_, v_a_1504_, v_a_1525_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1543_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_a_1528_ = lean_ctor_get(v___x_1526_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1530_ = v___x_1526_;
v_isShared_1531_ = v_isSharedCheck_1543_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1543_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1532_ = lean_unsigned_to_nat(2u);
v___x_1533_ = lean_mk_empty_array_with_capacity(v___x_1532_);
v___x_1534_ = lean_array_push(v___x_1533_, v_a_1524_);
v___x_1535_ = lean_array_push(v___x_1534_, v_a_1527_);
v___x_1536_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v___x_1535_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1536_);
v___x_1538_ = 0;
v___x_1539_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_1537_, v___x_1538_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1539_);
v___x_1541_ = v___x_1530_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_a_1528_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
else
{
lean_dec(v_a_1524_);
return v___x_1526_;
}
}
else
{
lean_dec(v___x_1517_);
return v___x_1523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCdotTactic___boxed(lean_object* v_x_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Fmt_fmtCdotTactic(v_x_1544_, v_a_1545_, v_a_1546_);
lean_dec_ref(v_a_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1(){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1554_ = l_Lean_Fmt_fmtAttribute;
v___x_1555_ = ((lean_object*)(l_Lean_Fmt_fmtCdotTactic___closed__1));
v___x_1556_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___closed__1));
v___x_1557_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCdotTactic___boxed), 3, 0);
v___x_1558_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1554_, v___x_1555_, v___x_1556_, v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1___boxed(lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCdotTactic___regBuiltin_Lean_Fmt_fmtCdotTactic__1();
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__1(size_t v_sz_1561_, size_t v_i_1562_, lean_object* v_bs_1563_){
_start:
{
uint8_t v___x_1564_; 
v___x_1564_ = lean_usize_dec_lt(v_i_1562_, v_sz_1561_);
if (v___x_1564_ == 0)
{
return v_bs_1563_;
}
else
{
lean_object* v_v_1565_; lean_object* v_snd_1566_; lean_object* v___x_1567_; lean_object* v_bs_x27_1568_; size_t v___x_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
v_v_1565_ = lean_array_uget_borrowed(v_bs_1563_, v_i_1562_);
v_snd_1566_ = lean_ctor_get(v_v_1565_, 1);
lean_inc(v_snd_1566_);
v___x_1567_ = lean_unsigned_to_nat(0u);
v_bs_x27_1568_ = lean_array_uset(v_bs_1563_, v_i_1562_, v___x_1567_);
v___x_1569_ = ((size_t)1ULL);
v___x_1570_ = lean_usize_add(v_i_1562_, v___x_1569_);
v___x_1571_ = lean_array_uset(v_bs_x27_1568_, v_i_1562_, v_snd_1566_);
v_i_1562_ = v___x_1570_;
v_bs_1563_ = v___x_1571_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__1___boxed(lean_object* v_sz_1573_, lean_object* v_i_1574_, lean_object* v_bs_1575_){
_start:
{
size_t v_sz_boxed_1576_; size_t v_i_boxed_1577_; lean_object* v_res_1578_; 
v_sz_boxed_1576_ = lean_unbox_usize(v_sz_1573_);
lean_dec(v_sz_1573_);
v_i_boxed_1577_ = lean_unbox_usize(v_i_1574_);
lean_dec(v_i_1574_);
v_res_1578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__1(v_sz_boxed_1576_, v_i_boxed_1577_, v_bs_1575_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__0(size_t v_sz_1579_, size_t v_i_1580_, lean_object* v_bs_1581_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_usize_dec_lt(v_i_1580_, v_sz_1579_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_bs_1581_);
return v___x_1583_;
}
else
{
lean_object* v_v_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v_v_1584_ = lean_array_uget(v_bs_1581_, v_i_1580_);
v___x_1585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtClassAbbrev_spec__0___closed__1));
lean_inc(v_v_1584_);
v___x_1586_ = l_Lean_Syntax_isOfKind(v_v_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
lean_dec(v_v_1584_);
lean_dec_ref(v_bs_1581_);
v___x_1587_ = lean_box(0);
return v___x_1587_;
}
else
{
lean_object* v___x_1588_; lean_object* v_tacticSeqs_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1588_ = lean_unsigned_to_nat(1u);
v_tacticSeqs_1589_ = l_Lean_Syntax_getArg(v_v_1584_, v___x_1588_);
v___x_1590_ = ((lean_object*)(l_Lean_Fmt_fmtCdotTactic___closed__6));
lean_inc(v_tacticSeqs_1589_);
v___x_1591_ = l_Lean_Syntax_isOfKind(v_tacticSeqs_1589_, v___x_1590_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; 
lean_dec(v_tacticSeqs_1589_);
lean_dec(v_v_1584_);
lean_dec_ref(v_bs_1581_);
v___x_1592_ = lean_box(0);
return v___x_1592_;
}
else
{
lean_object* v___x_1593_; lean_object* v_bs_x27_1594_; lean_object* v_barTks_1595_; lean_object* v___x_1596_; size_t v___x_1597_; size_t v___x_1598_; lean_object* v___x_1599_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v_bs_x27_1594_ = lean_array_uset(v_bs_1581_, v_i_1580_, v___x_1593_);
v_barTks_1595_ = l_Lean_Syntax_getArg(v_v_1584_, v___x_1593_);
lean_dec(v_v_1584_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_barTks_1595_);
lean_ctor_set(v___x_1596_, 1, v_tacticSeqs_1589_);
v___x_1597_ = ((size_t)1ULL);
v___x_1598_ = lean_usize_add(v_i_1580_, v___x_1597_);
v___x_1599_ = lean_array_uset(v_bs_x27_1594_, v_i_1580_, v___x_1596_);
v_i_1580_ = v___x_1598_;
v_bs_1581_ = v___x_1599_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__0___boxed(lean_object* v_sz_1601_, lean_object* v_i_1602_, lean_object* v_bs_1603_){
_start:
{
size_t v_sz_boxed_1604_; size_t v_i_boxed_1605_; lean_object* v_res_1606_; 
v_sz_boxed_1604_ = lean_unbox_usize(v_sz_1601_);
lean_dec(v_sz_1601_);
v_i_boxed_1605_ = lean_unbox_usize(v_i_1602_);
lean_dec(v_i_1602_);
v_res_1606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__0(v_sz_boxed_1604_, v_i_boxed_1605_, v_bs_1603_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__2(size_t v_sz_1607_, size_t v_i_1608_, lean_object* v_bs_1609_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_usize_dec_lt(v_i_1608_, v_sz_1607_);
if (v___x_1610_ == 0)
{
return v_bs_1609_;
}
else
{
lean_object* v_v_1611_; lean_object* v_fst_1612_; lean_object* v___x_1613_; lean_object* v_bs_x27_1614_; size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v_v_1611_ = lean_array_uget_borrowed(v_bs_1609_, v_i_1608_);
v_fst_1612_ = lean_ctor_get(v_v_1611_, 0);
lean_inc(v_fst_1612_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v_bs_x27_1614_ = lean_array_uset(v_bs_1609_, v_i_1608_, v___x_1613_);
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1608_, v___x_1615_);
v___x_1617_ = lean_array_uset(v_bs_x27_1614_, v_i_1608_, v_fst_1612_);
v_i_1608_ = v___x_1616_;
v_bs_1609_ = v___x_1617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__2___boxed(lean_object* v_sz_1619_, lean_object* v_i_1620_, lean_object* v_bs_1621_){
_start:
{
size_t v_sz_boxed_1622_; size_t v_i_boxed_1623_; lean_object* v_res_1624_; 
v_sz_boxed_1622_ = lean_unbox_usize(v_sz_1619_);
lean_dec(v_sz_1619_);
v_i_boxed_1623_ = lean_unbox_usize(v_i_1620_);
lean_dec(v_i_1620_);
v_res_1624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__2(v_sz_boxed_1622_, v_i_boxed_1623_, v_bs_1621_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSolve(lean_object* v_x_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = ((lean_object*)(l_Lean_Fmt_fmtSolve___closed__1));
lean_inc(v_x_1629_);
v___x_1633_ = l_Lean_Syntax_isOfKind(v_x_1629_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec(v_x_1629_);
v___x_1634_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
lean_ctor_set(v___x_1635_, 1, v_a_1631_);
return v___x_1635_;
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; size_t v_sz_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = l_Lean_Syntax_getArg(v_x_1629_, v___x_1636_);
v___x_1638_ = l_Lean_Syntax_getArgs(v___x_1637_);
lean_dec(v___x_1637_);
v_sz_1639_ = lean_array_size(v___x_1638_);
v___x_1640_ = ((size_t)0ULL);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__0(v_sz_1639_, v___x_1640_, v___x_1638_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec(v_x_1629_);
v___x_1642_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_a_1631_);
return v___x_1643_;
}
else
{
lean_object* v_val_1644_; lean_object* v___x_1645_; lean_object* v_solveTk_1646_; size_t v_sz_1647_; lean_object* v_tacticSeqs_1648_; lean_object* v_barTks_1649_; lean_object* v___x_1650_; 
v_val_1644_ = lean_ctor_get(v___x_1641_, 0);
lean_inc_n(v_val_1644_, 2);
lean_dec_ref_known(v___x_1641_, 1);
v___x_1645_ = lean_unsigned_to_nat(0u);
v_solveTk_1646_ = l_Lean_Syntax_getArg(v_x_1629_, v___x_1645_);
lean_dec(v_x_1629_);
v_sz_1647_ = lean_array_size(v_val_1644_);
v_tacticSeqs_1648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__1(v_sz_1647_, v___x_1640_, v_val_1644_);
v_barTks_1649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSolve_spec__2(v_sz_1647_, v___x_1640_, v_val_1644_);
v___x_1650_ = l_Lean_Fmt_fmtAltsTactic___redArg(v_solveTk_1646_, v_barTks_1649_, v_tacticSeqs_1648_, v_a_1630_, v_a_1631_);
lean_dec_ref(v_tacticSeqs_1648_);
lean_dec_ref(v_barTks_1649_);
return v___x_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSolve___boxed(lean_object* v_x_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_Fmt_fmtSolve(v_x_1651_, v_a_1652_, v_a_1653_);
lean_dec_ref(v_a_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1(){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1661_ = l_Lean_Fmt_fmtAttribute;
v___x_1662_ = ((lean_object*)(l_Lean_Fmt_fmtSolve___closed__1));
v___x_1663_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___closed__1));
v___x_1664_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSolve___boxed), 3, 0);
v___x_1665_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1661_, v___x_1662_, v___x_1663_, v___x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1___boxed(lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtSolve___regBuiltin_Lean_Fmt_fmtSolve__1();
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStepLike(lean_object* v_pred_1668_, lean_object* v_colonEqTk_x3f_1669_, lean_object* v_proof_x3f_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Fmt_fmt_x3f(v_colonEqTk_x3f_1669_, v_a_1671_, v_a_1672_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v_a_1675_; lean_object* v___x_1676_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
v_a_1675_ = lean_ctor_get(v___x_1673_, 1);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1673_, 2);
v___x_1676_ = l_Lean_Fmt_fmt_x3f(v_proof_x3f_1670_, v_a_1671_, v_a_1675_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v_a_1678_; uint8_t v___x_1679_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
v_a_1678_ = lean_ctor_get(v___x_1676_, 1);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1676_, 2);
v___x_1679_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1674_);
if (v___x_1679_ == 0)
{
uint8_t v___x_1680_; 
v___x_1680_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1677_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1681_ = l_Lean_Syntax_getArgs(v_pred_1668_);
v___x_1682_ = lean_array_get_size(v___x_1681_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = lean_unsigned_to_nat(3u);
v___x_1684_ = lean_nat_dec_eq(v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_Fmt_fmt(v_pred_1668_, v_a_1671_, v_a_1678_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1695_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_a_1687_ = lean_ctor_get(v___x_1685_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1689_ = v___x_1685_;
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1695_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1686_, v_a_1674_, v_a_1677_, v___x_1680_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1691_);
v___x_1693_ = v___x_1689_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_a_1687_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
lean_dec(v_a_1677_);
lean_dec(v_a_1674_);
return v___x_1685_;
}
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = l_Lean_Syntax_getArg(v_pred_1668_, v___x_1696_);
v___x_1698_ = l_Lean_Fmt_fmt(v___x_1697_, v_a_1671_, v_a_1678_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v_a_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
v_a_1700_ = lean_ctor_get(v___x_1698_, 1);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1698_, 2);
v___x_1701_ = lean_unsigned_to_nat(1u);
v___x_1702_ = l_Lean_Syntax_getArg(v_pred_1668_, v___x_1701_);
v___x_1703_ = l_Lean_Fmt_fmt(v___x_1702_, v_a_1671_, v_a_1700_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v_a_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
v_a_1705_ = lean_ctor_get(v___x_1703_, 1);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1703_, 2);
v___x_1706_ = lean_unsigned_to_nat(2u);
v___x_1707_ = l_Lean_Syntax_getArg(v_pred_1668_, v___x_1706_);
lean_dec(v_pred_1668_);
v___x_1708_ = l_Lean_Fmt_fmt(v___x_1707_, v_a_1671_, v_a_1705_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1742_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_a_1710_ = lean_ctor_get(v___x_1708_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1712_ = v___x_1708_;
v_isShared_1713_ = v_isSharedCheck_1742_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1742_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
lean_inc(v_a_1709_);
v___x_1714_ = l_Lean_Fmt_TaggedDoc_flattened(v_a_1709_);
v___x_1715_ = lean_mk_empty_array_with_capacity(v___x_1683_);
lean_inc_ref(v___x_1715_);
v___x_1716_ = lean_array_push(v___x_1715_, v_a_1699_);
v___x_1717_ = lean_array_push(v___x_1716_, v_a_1704_);
lean_inc_ref(v___x_1717_);
v___x_1718_ = lean_array_push(v___x_1717_, v___x_1714_);
v___x_1719_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_1719_, 0, v___x_1684_);
lean_ctor_set_uint8(v___x_1719_, 1, v___x_1680_);
lean_ctor_set_uint8(v___x_1719_, 2, v___x_1684_);
lean_ctor_set_uint8(v___x_1719_, 3, v___x_1684_);
lean_ctor_set_uint8(v___x_1719_, 4, v___x_1680_);
v___x_1720_ = l_Lean_Fmt_Layouts_infixOperator(v___x_1718_, v___x_1719_);
lean_dec_ref_known(v___x_1719_, 0);
v___x_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
v___x_1722_ = lean_obj_once(&l_Lean_Fmt_fmtTermMatches___closed__4, &l_Lean_Fmt_fmtTermMatches___closed__4_once, _init_l_Lean_Fmt_fmtTermMatches___closed__4);
v___x_1723_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1721_, v___x_1722_);
lean_inc(v_a_1674_);
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_a_1674_);
v___x_1725_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1724_, v___x_1722_);
v___x_1726_ = lean_box(0);
lean_inc(v_a_1677_);
v___x_1727_ = l_Lean_Fmt_TaggedDoc_flattened(v_a_1677_);
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1726_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
lean_ctor_set(v___x_1729_, 2, v___x_1726_);
v___x_1730_ = lean_array_push(v___x_1715_, v___x_1723_);
v___x_1731_ = lean_array_push(v___x_1730_, v___x_1725_);
v___x_1732_ = lean_array_push(v___x_1731_, v___x_1729_);
v___x_1733_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1732_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = lean_array_push(v___x_1717_, v_a_1709_);
v___x_1735_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_1735_, 0, v___x_1684_);
lean_ctor_set_uint8(v___x_1735_, 1, v___x_1680_);
lean_ctor_set_uint8(v___x_1735_, 2, v___x_1684_);
lean_ctor_set_uint8(v___x_1735_, 3, v___x_1680_);
lean_ctor_set_uint8(v___x_1735_, 4, v___x_1680_);
v___x_1736_ = l_Lean_Fmt_Layouts_infixOperator(v___x_1734_, v___x_1735_);
lean_dec_ref_known(v___x_1735_, 0);
v___x_1737_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_1736_, v_a_1674_, v_a_1677_, v___x_1680_);
v___x_1738_ = l_Lean_Fmt_TaggedDoc_fallbackOnOverflow(v___x_1733_, v___x_1737_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1738_);
v___x_1740_ = v___x_1712_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_a_1710_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_dec(v_a_1704_);
lean_dec(v_a_1699_);
lean_dec(v_a_1677_);
lean_dec(v_a_1674_);
return v___x_1708_;
}
}
else
{
lean_dec(v_a_1699_);
lean_dec(v_a_1677_);
lean_dec(v_a_1674_);
lean_dec(v_pred_1668_);
return v___x_1703_;
}
}
else
{
lean_dec(v_a_1677_);
lean_dec(v_a_1674_);
lean_dec(v_pred_1668_);
return v___x_1698_;
}
}
}
else
{
lean_object* v___x_1743_; 
lean_dec(v_a_1677_);
lean_dec(v_a_1674_);
v___x_1743_ = l_Lean_Fmt_fmt(v_pred_1668_, v_a_1671_, v_a_1678_);
return v___x_1743_;
}
}
else
{
lean_object* v___x_1744_; 
lean_dec(v_a_1677_);
lean_dec(v_a_1674_);
v___x_1744_ = l_Lean_Fmt_fmt(v_pred_1668_, v_a_1671_, v_a_1678_);
return v___x_1744_;
}
}
else
{
lean_dec(v_a_1674_);
lean_dec(v_pred_1668_);
return v___x_1676_;
}
}
else
{
lean_dec(v_proof_x3f_1670_);
lean_dec(v_pred_1668_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStepLike___boxed(lean_object* v_pred_1745_, lean_object* v_colonEqTk_x3f_1746_, lean_object* v_proof_x3f_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Fmt_fmtCalcStepLike(v_pred_1745_, v_colonEqTk_x3f_1746_, v_proof_x3f_1747_, v_a_1748_, v_a_1749_);
lean_dec_ref(v_a_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcFirstStep(lean_object* v_x_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = ((lean_object*)(l_Lean_Fmt_fmtCalcFirstStep___closed__1));
lean_inc(v_x_1755_);
v___x_1759_ = l_Lean_Syntax_isOfKind(v_x_1755_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v_x_1755_);
v___x_1760_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v_a_1757_);
return v___x_1761_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = l_Lean_Syntax_getArg(v_x_1755_, v___x_1762_);
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = l_Lean_Syntax_getArg(v_x_1755_, v___x_1764_);
lean_dec(v_x_1755_);
v___x_1766_ = l_Lean_Syntax_isNone(v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1765_);
v___x_1768_ = l_Lean_Syntax_matchesNull(v___x_1765_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec(v___x_1765_);
lean_dec(v___x_1763_);
v___x_1769_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v_a_1757_);
return v___x_1770_;
}
else
{
lean_object* v_colonEqTk_x3f_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_colonEqTk_x3f_1771_ = l_Lean_Syntax_getArg(v___x_1765_, v___x_1762_);
v___x_1772_ = l_Lean_Syntax_getArg(v___x_1765_, v___x_1764_);
lean_dec(v___x_1765_);
v___x_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_colonEqTk_x3f_1771_);
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
v___x_1775_ = l_Lean_Fmt_fmtCalcStepLike(v___x_1763_, v___x_1773_, v___x_1774_, v_a_1756_, v_a_1757_);
return v___x_1775_;
}
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v___x_1765_);
v___x_1776_ = lean_box(0);
v___x_1777_ = l_Lean_Fmt_fmtCalcStepLike(v___x_1763_, v___x_1776_, v___x_1776_, v_a_1756_, v_a_1757_);
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcFirstStep___boxed(lean_object* v_x_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Fmt_fmtCalcFirstStep(v_x_1778_, v_a_1779_, v_a_1780_);
lean_dec_ref(v_a_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1(){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1788_ = l_Lean_Fmt_fmtAttribute;
v___x_1789_ = ((lean_object*)(l_Lean_Fmt_fmtCalcFirstStep___closed__1));
v___x_1790_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___closed__1));
v___x_1791_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCalcFirstStep___boxed), 3, 0);
v___x_1792_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1788_, v___x_1789_, v___x_1790_, v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1___boxed(lean_object* v_a_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcFirstStep___regBuiltin_Lean_Fmt_fmtCalcFirstStep__1();
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStep(lean_object* v_x_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_Lean_Fmt_fmtCalcStep___closed__1));
lean_inc(v_x_1799_);
v___x_1803_ = l_Lean_Syntax_isOfKind(v_x_1799_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v_x_1799_);
v___x_1804_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v_a_1801_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v_colonEqTk_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = l_Lean_Syntax_getArg(v_x_1799_, v___x_1806_);
v___x_1808_ = lean_unsigned_to_nat(1u);
v_colonEqTk_1809_ = l_Lean_Syntax_getArg(v_x_1799_, v___x_1808_);
v___x_1810_ = lean_unsigned_to_nat(2u);
v___x_1811_ = l_Lean_Syntax_getArg(v_x_1799_, v___x_1810_);
lean_dec(v_x_1799_);
v___x_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_colonEqTk_1809_);
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
v___x_1814_ = l_Lean_Fmt_fmtCalcStepLike(v___x_1807_, v___x_1812_, v___x_1813_, v_a_1800_, v_a_1801_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcStep___boxed(lean_object* v_x_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Fmt_fmtCalcStep(v_x_1815_, v_a_1816_, v_a_1817_);
lean_dec_ref(v_a_1816_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1(){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1825_ = l_Lean_Fmt_fmtAttribute;
v___x_1826_ = ((lean_object*)(l_Lean_Fmt_fmtCalcStep___closed__1));
v___x_1827_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___closed__1));
v___x_1828_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCalcStep___boxed), 3, 0);
v___x_1829_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1825_, v___x_1826_, v___x_1827_, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1___boxed(lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcStep___regBuiltin_Lean_Fmt_fmtCalcStep__1();
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCalcSteps_spec__0(size_t v_sz_1832_, size_t v_i_1833_, lean_object* v_bs_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_usize_dec_lt(v_i_1833_, v_sz_1832_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_bs_1834_);
lean_ctor_set(v___x_1838_, 1, v___y_1836_);
return v___x_1838_;
}
else
{
lean_object* v_v_1839_; lean_object* v___x_1840_; 
v_v_1839_ = lean_array_uget_borrowed(v_bs_1834_, v_i_1833_);
lean_inc(v_v_1839_);
v___x_1840_ = l_Lean_Fmt_fmt(v_v_1839_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v_bs_x27_1844_; size_t v___x_1845_; size_t v___x_1846_; lean_object* v___x_1847_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
v_a_1842_ = lean_ctor_get(v___x_1840_, 1);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1840_, 2);
v___x_1843_ = lean_unsigned_to_nat(0u);
v_bs_x27_1844_ = lean_array_uset(v_bs_1834_, v_i_1833_, v___x_1843_);
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1833_, v___x_1845_);
v___x_1847_ = lean_array_uset(v_bs_x27_1844_, v_i_1833_, v_a_1841_);
v_i_1833_ = v___x_1846_;
v_bs_1834_ = v___x_1847_;
v___y_1836_ = v_a_1842_;
goto _start;
}
else
{
lean_object* v_a_1849_; lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v_bs_1834_);
v_a_1849_ = lean_ctor_get(v___x_1840_, 0);
v_a_1850_ = lean_ctor_get(v___x_1840_, 1);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1840_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_inc(v_a_1849_);
lean_dec(v___x_1840_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1849_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCalcSteps_spec__0___boxed(lean_object* v_sz_1858_, lean_object* v_i_1859_, lean_object* v_bs_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
size_t v_sz_boxed_1863_; size_t v_i_boxed_1864_; lean_object* v_res_1865_; 
v_sz_boxed_1863_ = lean_unbox_usize(v_sz_1858_);
lean_dec(v_sz_1858_);
v_i_boxed_1864_ = lean_unbox_usize(v_i_1859_);
lean_dec(v_i_1859_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCalcSteps_spec__0(v_sz_boxed_1863_, v_i_boxed_1864_, v_bs_1860_, v___y_1861_, v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcSteps(lean_object* v_calcSteps_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = l_Lean_Fmt_getStxArg_x21___redArg(v_calcSteps_1866_, v___x_1869_, v_a_1868_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v_a_1872_; lean_object* v___x_1873_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
v_a_1872_ = lean_ctor_get(v___x_1870_, 1);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1870_, 2);
v___x_1873_ = l_Lean_Fmt_fmt(v_a_1871_, v_a_1867_, v_a_1872_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v_a_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
v_a_1875_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1873_, 2);
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = l_Lean_Fmt_getStxArg_x21___redArg(v_calcSteps_1866_, v___x_1876_, v_a_1875_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v_a_1879_; lean_object* v___x_1880_; size_t v_sz_1881_; size_t v___x_1882_; lean_object* v___x_1883_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
v_a_1879_ = lean_ctor_get(v___x_1877_, 1);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1877_, 2);
v___x_1880_ = l_Lean_Syntax_getArgs(v_a_1878_);
lean_dec(v_a_1878_);
v_sz_1881_ = lean_array_size(v___x_1880_);
v___x_1882_ = ((size_t)0ULL);
v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtCalcSteps_spec__0(v_sz_1881_, v___x_1882_, v___x_1880_, v_a_1867_, v_a_1879_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1895_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_a_1885_ = lean_ctor_get(v___x_1883_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1887_ = v___x_1883_;
v_isShared_1888_ = v_isSharedCheck_1895_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1895_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1889_ = lean_mk_empty_array_with_capacity(v___x_1876_);
v___x_1890_ = lean_array_push(v___x_1889_, v_a_1874_);
v___x_1891_ = l_Array_append___redArg(v___x_1890_, v_a_1884_);
lean_dec(v_a_1884_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1891_);
v___x_1893_ = v___x_1887_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_a_1885_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_dec(v_a_1874_);
return v___x_1883_;
}
}
else
{
lean_object* v_a_1896_; lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_a_1874_);
v_a_1896_ = lean_ctor_get(v___x_1877_, 0);
v_a_1897_ = lean_ctor_get(v___x_1877_, 1);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1877_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_inc(v_a_1896_);
lean_dec(v___x_1877_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1896_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_a_1905_ = lean_ctor_get(v___x_1873_, 0);
v_a_1906_ = lean_ctor_get(v___x_1873_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1873_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_inc(v_a_1905_);
lean_dec(v___x_1873_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1905_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1914_ = lean_ctor_get(v___x_1870_, 0);
v_a_1915_ = lean_ctor_get(v___x_1870_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1870_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_inc(v_a_1914_);
lean_dec(v___x_1870_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1914_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcSteps___boxed(lean_object* v_calcSteps_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Fmt_fmtCalcSteps(v_calcSteps_1923_, v_a_1924_, v_a_1925_);
lean_dec_ref(v_a_1924_);
lean_dec(v_calcSteps_1923_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalc(lean_object* v_calcTk_1927_, lean_object* v_calcSteps_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_Fmt_fmt(v_calcTk_1927_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
v_a_1933_ = lean_ctor_get(v___x_1931_, 1);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1931_, 2);
v___x_1934_ = l_Lean_Fmt_fmtCalcSteps(v_calcSteps_1928_, v_a_1929_, v_a_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1947_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_a_1936_ = lean_ctor_get(v___x_1934_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1938_ = v___x_1934_;
v_isShared_1939_ = v_isSharedCheck_1947_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1947_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1940_ = l_Lean_Fmt_Layouts_lines(v_a_1935_);
lean_dec(v_a_1935_);
v___x_1941_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_1940_);
v___x_1942_ = 1;
v___x_1943_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_1932_, v___x_1941_, v___x_1942_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1943_);
v___x_1945_ = v___x_1938_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_a_1936_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_a_1932_);
v_a_1948_ = lean_ctor_get(v___x_1934_, 0);
v_a_1949_ = lean_ctor_get(v___x_1934_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1934_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_inc(v_a_1948_);
lean_dec(v___x_1934_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1948_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_a_1949_);
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
else
{
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalc___boxed(lean_object* v_calcTk_1957_, lean_object* v_calcSteps_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Fmt_fmtCalc(v_calcTk_1957_, v_calcSteps_1958_, v_a_1959_, v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_calcSteps_1958_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTerm(lean_object* v_x_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTerm___closed__1));
lean_inc(v_x_1970_);
v___x_1974_ = l_Lean_Syntax_isOfKind(v_x_1970_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_dec(v_x_1970_);
v___x_1975_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v_a_1972_);
return v___x_1976_;
}
else
{
lean_object* v___x_1977_; lean_object* v_steps_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1977_ = lean_unsigned_to_nat(1u);
v_steps_1978_ = l_Lean_Syntax_getArg(v_x_1970_, v___x_1977_);
v___x_1979_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTerm___closed__3));
lean_inc(v_steps_1978_);
v___x_1980_ = l_Lean_Syntax_isOfKind(v_steps_1978_, v___x_1979_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_dec(v_steps_1978_);
lean_dec(v_x_1970_);
v___x_1981_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v_a_1972_);
return v___x_1982_;
}
else
{
lean_object* v___x_1983_; lean_object* v_calcTk_1984_; lean_object* v___x_1985_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v_calcTk_1984_ = l_Lean_Syntax_getArg(v_x_1970_, v___x_1983_);
lean_dec(v_x_1970_);
v___x_1985_ = l_Lean_Fmt_fmtCalc(v_calcTk_1984_, v_steps_1978_, v_a_1971_, v_a_1972_);
lean_dec(v_steps_1978_);
return v___x_1985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTerm___boxed(lean_object* v_x_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Fmt_fmtCalcTerm(v_x_1986_, v_a_1987_, v_a_1988_);
lean_dec_ref(v_a_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1(){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1996_ = l_Lean_Fmt_fmtAttribute;
v___x_1997_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTerm___closed__1));
v___x_1998_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___closed__1));
v___x_1999_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCalcTerm___boxed), 3, 0);
v___x_2000_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1996_, v___x_1997_, v___x_1998_, v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1___boxed(lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTerm___regBuiltin_Lean_Fmt_fmtCalcTerm__1();
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTactic(lean_object* v_x_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTactic___closed__1));
lean_inc(v_x_2007_);
v___x_2011_ = l_Lean_Syntax_isOfKind(v_x_2007_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_x_2007_);
v___x_2012_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v_a_2009_);
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; lean_object* v_steps_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2014_ = lean_unsigned_to_nat(1u);
v_steps_2015_ = l_Lean_Syntax_getArg(v_x_2007_, v___x_2014_);
v___x_2016_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTerm___closed__3));
lean_inc(v_steps_2015_);
v___x_2017_ = l_Lean_Syntax_isOfKind(v_steps_2015_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v_steps_2015_);
lean_dec(v_x_2007_);
v___x_2018_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v_a_2009_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; lean_object* v_calcTk_2021_; lean_object* v___x_2022_; 
v___x_2020_ = lean_unsigned_to_nat(0u);
v_calcTk_2021_ = l_Lean_Syntax_getArg(v_x_2007_, v___x_2020_);
lean_dec(v_x_2007_);
v___x_2022_ = l_Lean_Fmt_fmtCalc(v_calcTk_2021_, v_steps_2015_, v_a_2008_, v_a_2009_);
lean_dec(v_steps_2015_);
return v___x_2022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCalcTactic___boxed(lean_object* v_x_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_Fmt_fmtCalcTactic(v_x_2023_, v_a_2024_, v_a_2025_);
lean_dec_ref(v_a_2024_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1(){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2033_ = l_Lean_Fmt_fmtAttribute;
v___x_2034_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTactic___closed__1));
v___x_2035_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___closed__1));
v___x_2036_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCalcTactic___boxed), 3, 0);
v___x_2037_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2033_, v___x_2034_, v___x_2035_, v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1___boxed(lean_object* v_a_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtCalcTactic___regBuiltin_Lean_Fmt_fmtCalcTactic__1();
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCalc(lean_object* v_x_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_Lean_Fmt_fmtConvCalc___closed__1));
lean_inc(v_x_2044_);
v___x_2048_ = l_Lean_Syntax_isOfKind(v_x_2044_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_dec(v_x_2044_);
v___x_2049_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v_a_2046_);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; lean_object* v_steps_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2051_ = lean_unsigned_to_nat(1u);
v_steps_2052_ = l_Lean_Syntax_getArg(v_x_2044_, v___x_2051_);
v___x_2053_ = ((lean_object*)(l_Lean_Fmt_fmtCalcTerm___closed__3));
lean_inc(v_steps_2052_);
v___x_2054_ = l_Lean_Syntax_isOfKind(v_steps_2052_, v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec(v_steps_2052_);
lean_dec(v_x_2044_);
v___x_2055_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v_a_2046_);
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; lean_object* v_calcTk_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_unsigned_to_nat(0u);
v_calcTk_2058_ = l_Lean_Syntax_getArg(v_x_2044_, v___x_2057_);
lean_dec(v_x_2044_);
v___x_2059_ = l_Lean_Fmt_fmtCalc(v_calcTk_2058_, v_steps_2052_, v_a_2045_, v_a_2046_);
lean_dec(v_steps_2052_);
return v___x_2059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCalc___boxed(lean_object* v_x_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_Fmt_fmtConvCalc(v_x_2060_, v_a_2061_, v_a_2062_);
lean_dec_ref(v_a_2061_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1(){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2070_ = l_Lean_Fmt_fmtAttribute;
v___x_2071_ = ((lean_object*)(l_Lean_Fmt_fmtConvCalc___closed__1));
v___x_2072_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___closed__1));
v___x_2073_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvCalc___boxed), 3, 0);
v___x_2074_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2070_, v___x_2071_, v___x_2072_, v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1___boxed(lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___private_Lean_Fmt_Formatters_Init_NotationExtra_0__Lean_Fmt_fmtConvCalc___regBuiltin_Lean_Fmt_fmtConvCalc__1();
return v_res_2076_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
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
