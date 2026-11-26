// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Parser.Do
// Imports: import Lean.Fmt.Formatters.Lean.Parser.Term.Basic import Lean.Fmt.Formatters.Lean.Parser.Term public import Lean.Fmt.FmtM.Basic meta import Lean.Parser.Do import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtFullLetRecDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTermInstruction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object*);
lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_nl;
lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_unflattenable(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object*);
lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_getLineInfos(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object*, lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Fmt_fmtPatSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSeq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_Lean_Fmt_TaggedDoc_hardNl;
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_conditionalFmtAttribute;
lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtNestedAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtNestedAction___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtNestedAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtNestedAction___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtNestedAction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtNestedAction___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtNestedAction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedAction"};
static const lean_object* l_Lean_Fmt_fmtNestedAction___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtNestedAction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtNestedAction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtNestedAction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtNestedAction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(115, 27, 24, 243, 204, 49, 153, 202)}};
static const lean_object* l_Lean_Fmt_fmtNestedAction___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNestedAction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNestedAction___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtNestedAction"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(8, 114, 29, 114, 151, 177, 3, 233)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Fmt_fmtDoExpr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoExpr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Fmt_fmtDoExpr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoExpr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtDoExpr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 247, 177, 9, 140, 183, 166, 228)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoSeqItems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Fmt_fmtDoSeqItems___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoSeqItems___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtDoSeqItems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Fmt_fmtDoSeqItems___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoSeqItems___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqItems___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqItems___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoSeqItems___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqItems___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoSeqItems___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqItems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoSeqItems___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoSeqItems___closed__1_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Fmt_fmtDoSeqItems___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoSeqItems___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqItems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoSeqItems___closed__2_value)}};
static const lean_object* l_Lean_Fmt_fmtDoSeqItems___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoSeqItems___closed__3_value;
static const lean_array_object l_Lean_Fmt_fmtDoSeqItems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtDoSeqItems___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDoSeqItems___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqItems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqItems___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoSeqIndent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Fmt_fmtDoSeqIndent___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoSeqIndent___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqIndent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqIndent___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoSeqIndent___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqIndent___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoSeqIndent___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqIndent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoSeqIndent___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoSeqIndent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Fmt_fmtDoSeqIndent___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoSeqIndent___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqIndent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqIndent___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtDoSeqIndent"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 155, 30, 171, 182, 191, 95, 232)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoSeqBracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "doSeqBracketed"};
static const lean_object* l_Lean_Fmt_fmtDoSeqBracketed___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoSeqBracketed___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqBracketed___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqBracketed___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoSeqBracketed___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqBracketed___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoSeqBracketed___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoSeqBracketed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoSeqBracketed___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 57, 219, 150, 35, 125, 74, 168)}};
static const lean_object* l_Lean_Fmt_fmtDoSeqBracketed___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoSeqBracketed___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqBracketed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqBracketed___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtDoSeqBracketed"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 197, 154, 89, 189, 66, 92, 22)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean_Fmt_fmtDo___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDo___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDo___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDo___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDo___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDo___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDo___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDo___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l_Lean_Fmt_fmtDo___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDo___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fmtDo"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 135, 192, 104, 200, 204, 175, 31)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTermReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termReturn"};
static const lean_object* l_Lean_Fmt_fmtTermReturn___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermReturn___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermReturn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermReturn___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermReturn___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermReturn___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermReturn___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermReturn___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTermReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 245, 184, 22, 191, 152, 219, 48)}};
static const lean_object* l_Lean_Fmt_fmtTermReturn___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermReturn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermReturn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermReturn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtTermReturn"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 42, 62, 184, 228, 127, 84, 52)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoBreak(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoBreak___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtAtomic___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtDoBreak"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 203, 229, 202, 84, 175, 95, 113)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoContinue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoContinue___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtDoContinue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(20, 145, 109, 119, 249, 150, 12, 235)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Fmt_fmtDoReturn___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoReturn___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoReturn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReturn___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReturn___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReturn___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReturn___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReturn___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Fmt_fmtDoReturn___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoReturn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReturn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReturn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtDoReturn"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 224, 220, 55, 213, 148, 126, 236)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoDbgTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Fmt_fmtDoDbgTrace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoDbgTrace___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoDbgTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoDbgTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoDbgTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoDbgTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoDbgTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoDbgTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoDbgTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoDbgTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Fmt_fmtDoDbgTrace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoDbgTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoDbgTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoDbgTrace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtDoDbgTrace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 172, 87, 28, 181, 55, 43, 8)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoAssert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Fmt_fmtDoAssert___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoAssert___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoAssert___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoAssert___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoAssert___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoAssert___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoAssert___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoAssert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoAssert___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoAssert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Fmt_fmtDoAssert___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoAssert___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoAssert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoAssert___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtDoAssert"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 208, 144, 119, 90, 99, 213, 61)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoDebugAssert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Fmt_fmtDoDebugAssert___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoDebugAssert___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoDebugAssert___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoDebugAssert___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoDebugAssert___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoDebugAssert___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoDebugAssert___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoDebugAssert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoDebugAssert___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoDebugAssert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Fmt_fmtDoDebugAssert___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoDebugAssert___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoDebugAssert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoDebugAssert___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtDoDebugAssert"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 155, 46, 165, 195, 216, 60, 143)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoRepeat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doRepeat"};
static const lean_object* l_Lean_Fmt_fmtDoRepeat___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoRepeat___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoRepeat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoRepeat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoRepeat___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoRepeat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoRepeat___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoRepeat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoRepeat___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 14, 140, 183, 155, 194, 124, 178)}};
static const lean_object* l_Lean_Fmt_fmtDoRepeat___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoRepeat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoRepeat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoRepeat___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtDoRepeat"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 84, 58, 168, 6, 243, 89, 71)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Fmt_fmtDoLet___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoLet___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Fmt_fmtDoLet___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoLet___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDoLet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Fmt_fmtDoLet___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoLet___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l_Lean_Fmt_fmtDoLet___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoLet___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtDoLet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Fmt_fmtDoLet___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDoLet___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoLet___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Fmt_fmtDoLet___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtDoLet___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLet___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtDoLet"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 89, 87, 148, 85, 103, 106, 81)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l_Lean_Fmt_fmtDoHave___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoHave___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoHave___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Fmt_fmtDoHave___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoHave___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoHave(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoHave___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtDoHave"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 216, 67, 65, 49, 118, 155, 110)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___boxed(lean_object*);
static const lean_array_object l_Lean_Fmt_fmtDoLetElseLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtDoLetElseLike___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoLetElseLike___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetElseLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetElseLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtWithDoIdDecl_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtWithDoIdDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtWithDoIdDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Fmt_fmtWithDoIdDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtWithDoIdDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithDoIdDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithDoIdDecl___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithDoIdDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l_Lean_Fmt_fmtWithDoIdDecl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtWithDoIdDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtWithDoIdDecl___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtWithDoIdDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtWithDoIdDecl___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtWithDoIdDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtWithDoIdDecl___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtWithDoIdDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Fmt_fmtWithDoIdDecl___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtWithDoIdDecl___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithDoIdDecl___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithDoIdDecl___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithDoIdDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Fmt_fmtWithDoIdDecl___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtWithDoIdDecl___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithDoIdDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithDoIdDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtWithDoPatDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doPatDecl"};
static const lean_object* l_Lean_Fmt_fmtWithDoPatDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWithDoPatDecl___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtWithDoPatDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithDoPatDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithDoPatDecl___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithDoPatDecl___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithDoPatDecl___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithDoPatDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithDoPatDecl___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtWithDoPatDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 158, 71, 138, 110, 159, 158, 208)}};
static const lean_object* l_Lean_Fmt_fmtWithDoPatDecl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtWithDoPatDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithDoPatDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithDoPatDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoLetArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Fmt_fmtDoLetArrow___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoLetArrow___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLetArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetArrow___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetArrow___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoLetArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Fmt_fmtDoLetArrow___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoLetArrow___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetArrow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetArrow___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtDoLetArrow"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 21, 250, 27, 26, 62, 191, 218)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoLetElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetElse"};
static const lean_object* l_Lean_Fmt_fmtDoLetElse___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoLetElse___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLetElse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetElse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetElse___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetElse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetElse___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetElse___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoLetElse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 153, 29, 134, 242, 228, 141, 99)}};
static const lean_object* l_Lean_Fmt_fmtDoLetElse___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoLetElse___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetElse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetElse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtDoLetElse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 131, 181, 14, 168, 155, 213, 22)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoLetExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Fmt_fmtDoLetExpr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLetExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Fmt_fmtDoLetExpr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDoLetExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprPat"};
static const lean_object* l_Lean_Fmt_fmtDoLetExpr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLetExpr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetExpr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetExpr___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 152, 68, 102, 242, 224, 57, 35)}};
static const lean_object* l_Lean_Fmt_fmtDoLetExpr___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoLetExpr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtDoLetExpr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 123, 228, 42, 202, 45, 171, 171)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoLetMetaExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Fmt_fmtDoLetMetaExpr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoLetMetaExpr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLetMetaExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetMetaExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetMetaExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetMetaExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetMetaExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetMetaExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetMetaExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoLetMetaExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Fmt_fmtDoLetMetaExpr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoLetMetaExpr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetMetaExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetMetaExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtDoLetMetaExpr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 81, 52, 63, 236, 77, 44, 49)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoLetRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doLetRec"};
static const lean_object* l_Lean_Fmt_fmtDoLetRec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLetRec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetRec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetRec___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 47, 84, 182, 64, 225, 123, 219)}};
static const lean_object* l_Lean_Fmt_fmtDoLetRec___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDoLetRec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Fmt_fmtDoLetRec___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLetRec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Fmt_fmtDoLetRec___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtDoLetRec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Fmt_fmtDoLetRec___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoLetRec___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetRec___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetRec___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoLetRec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Fmt_fmtDoLetRec___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtDoLetRec___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetRec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetRec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtDoLetRec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 116, 23, 129, 16, 52, 118, 129)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLetIdDeclNoBinders(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLetIdDeclNoBinders___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtLetIdDeclNoBinders"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 97, 187, 226, 116, 81, 236, 96)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoReassign___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Fmt_fmtDoReassign___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoReassign___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReassign___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReassign___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReassign___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Fmt_fmtDoReassign___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDoReassign___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Fmt_fmtDoReassign___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoReassign___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReassign___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReassign___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReassign___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Fmt_fmtDoReassign___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoReassign___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReassign(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReassign___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtDoReassign"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 28, 78, 187, 108, 72, 124, 69)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoReassignArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Fmt_fmtDoReassignArrow___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoReassignArrow___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoReassignArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReassignArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReassignArrow___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReassignArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReassignArrow___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoReassignArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoReassignArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoReassignArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Fmt_fmtDoReassignArrow___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoReassignArrow___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReassignArrow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReassignArrow___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtDoReassignArrow"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 21, 113, 248, 200, 198, 158, 225)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoIfProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l_Lean_Fmt_fmtDoIfProp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoIfProp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoIfProp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfProp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfProp___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfProp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfProp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfProp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfProp___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoIfProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 147, 210, 58, 86, 191, 41, 151)}};
static const lean_object* l_Lean_Fmt_fmtDoIfProp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoIfProp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfProp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfProp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtDoIfProp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 82, 107, 79, 2, 201, 163, 249)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfLetLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfLetLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoIfLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doIfLet"};
static const lean_object* l_Lean_Fmt_fmtDoIfLet___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 227, 73, 225, 0, 143, 195, 11)}};
static const lean_object* l_Lean_Fmt_fmtDoIfLet___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDoIfLet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doIfLetPure"};
static const lean_object* l_Lean_Fmt_fmtDoIfLet___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(30, 29, 142, 71, 96, 53, 139, 191)}};
static const lean_object* l_Lean_Fmt_fmtDoIfLet___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtDoIfLet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doIfLetBind"};
static const lean_object* l_Lean_Fmt_fmtDoIfLet___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIfLet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__4_value),LEAN_SCALAR_PTR_LITERAL(251, 203, 116, 140, 48, 138, 26, 199)}};
static const lean_object* l_Lean_Fmt_fmtDoIfLet___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtDoIfLet___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfLet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfLet___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtDoIfLet"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 194, 245, 134, 216, 125, 173, 110)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtDoIf_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtDoIf_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoIf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Fmt_fmtDoIf___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoIf___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoIf___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIf___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIf___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIf___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIf___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoIf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoIf___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoIf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Fmt_fmtDoIf___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoIf___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtDoIf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtDoIf___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoIf___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIf___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fmtDoIf"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 0, 59, 176, 76, 204, 177, 201)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtUnlessLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtUnlessLike___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtUnlessLike___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtUnlessLike___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtUnlessLike___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtUnlessLike___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnlessLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnlessLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoUnless___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Fmt_fmtDoUnless___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoUnless___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoUnless___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoUnless___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoUnless___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoUnless___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoUnless___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoUnless___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoUnless___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoUnless___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Fmt_fmtDoUnless___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoUnless___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoUnless(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoUnless___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtDoUnless"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 55, 154, 81, 33, 77, 160, 247)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTermUnless___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termUnless"};
static const lean_object* l_Lean_Fmt_fmtTermUnless___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermUnless___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermUnless___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermUnless___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermUnless___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermUnless___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermUnless___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermUnless___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermUnless___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTermUnless___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 93, 2, 77, 146, 4, 53, 233)}};
static const lean_object* l_Lean_Fmt_fmtTermUnless___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermUnless___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermUnless(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermUnless___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtTermUnless"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 37, 146, 231, 133, 153, 249)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoForDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l_Lean_Fmt_fmtDoForDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoForDecl___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoForDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoForDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoForDecl___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoForDecl___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoForDecl___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoForDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoForDecl___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoForDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l_Lean_Fmt_fmtDoForDecl___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoForDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoForDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoForDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtDoForDecl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 51, 62, 92, 208, 62, 172, 202)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Fmt_fmtDoFor___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoFor___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoFor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoFor___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoFor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoFor___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoFor___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Fmt_fmtDoFor___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoFor___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtDoFor___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoFor___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoFor___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtDoFor"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 118, 183, 19, 73, 225, 153, 251)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTermFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termFor"};
static const lean_object* l_Lean_Fmt_fmtTermFor___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermFor___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermFor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermFor___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermFor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermFor___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermFor___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTermFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 224, 91, 133, 33, 161, 189, 246)}};
static const lean_object* l_Lean_Fmt_fmtTermFor___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermFor___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermFor___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtTermFor"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 69, 173, 237, 228, 156, 122, 143)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDependentParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Fmt_fmtDependentParam___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDependentParam___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDependentParam___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDependentParam___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDependentParam___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDependentParam___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDependentParam___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDependentParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDependentParam___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDependentParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Fmt_fmtDependentParam___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDependentParam___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDependentParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDependentParam___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtDependentParam"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 209, 143, 31, 108, 246, 101, 187)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Fmt_fmtDoMatch___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Fmt_fmtDoMatch___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtDoMatch___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtDoMatch___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Fmt_fmtDoMatch___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Fmt_fmtDoMatch___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtDoMatch___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean_Fmt_fmtDoMatch___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__5_value),LEAN_SCALAR_PTR_LITERAL(81, 58, 182, 248, 224, 44, 170, 90)}};
static const lean_object* l_Lean_Fmt_fmtDoMatch___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtDoMatch___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Fmt_fmtDoMatch___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__8_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__8_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatch___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__8_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__7_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Fmt_fmtDoMatch___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtDoMatch___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoMatch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoMatch___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtDoMatch"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 80, 24, 219, 247, 181, 16, 190)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoMatchExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Fmt_fmtDoMatchExpr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoMatchExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatchExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatchExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatchExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Fmt_fmtDoMatchExpr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDoMatchExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Fmt_fmtDoMatchExpr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoMatchExpr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatchExpr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatchExpr___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoMatchExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Fmt_fmtDoMatchExpr___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoMatchExpr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoMatchExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoMatchExpr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtDoMatchExpr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 47, 233, 236, 245, 206, 113, 39)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_doCatch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_doCatch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_doCatchMatch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_doCatchMatch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_hasNewline(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_hasNewline___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_nested, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doCatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 196, 191, 146, 79, 230, 20, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "doCatchMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 106, 10, 98, 177, 11, 181, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTryCatchFinally___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Fmt_fmtTryCatchFinally___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTryCatchFinally___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTryCatchFinally___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryCatchFinally___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryCatchFinally___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryCatchFinally___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryCatchFinally___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtTryCatchFinally___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTryCatchFinally___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTryCatchFinally___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Fmt_fmtTryCatchFinally___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTryCatchFinally___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryCatchFinally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryCatchFinally___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoTry_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoTry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoTry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Fmt_fmtDoTry___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoTry___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoTry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoTry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoTry___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoTry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoTry___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoTry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoTry___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoTry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Fmt_fmtDoTry___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoTry___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoTry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoTry___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtDoTry"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 228, 102, 169, 80, 155, 196, 122)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTermTry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termTry"};
static const lean_object* l_Lean_Fmt_fmtTermTry___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermTry___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermTry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermTry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermTry___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermTry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermTry___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtTermTry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermTry___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTermTry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 80, 182, 167, 150, 154, 214, 88)}};
static const lean_object* l_Lean_Fmt_fmtTermTry___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermTry___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermTry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermTry___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtTermTry"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 161, 50, 131, 121, 77, 133, 164)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoForward___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForward"};
static const lean_object* l_Lean_Fmt_fmtDoForward___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoForward___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoForward___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoForward___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoForward___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoForward___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoForward___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoForward___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoForward___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoForward___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 164, 175, 48, 233, 61, 15, 76)}};
static const lean_object* l_Lean_Fmt_fmtDoForward___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoForward___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoForward(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoForward___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtDoForward"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 197, 157, 228, 109, 143, 123, 83)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoWhile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doWhile"};
static const lean_object* l_Lean_Fmt_fmtDoWhile___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoWhile___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoWhile___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoWhile___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoWhile___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoWhile___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoWhile___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoWhile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoWhile___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoWhile___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 22, 162, 157, 218, 80, 50, 216)}};
static const lean_object* l_Lean_Fmt_fmtDoWhile___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoWhile___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoWhile___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtDoWhile"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 96, 182, 164, 160, 43, 77, 41)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoRepeatUntil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doRepeatUntil"};
static const lean_object* l_Lean_Fmt_fmtDoRepeatUntil___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoRepeatUntil___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoRepeatUntil___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoRepeatUntil___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoRepeatUntil___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoRepeatUntil___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoRepeatUntil___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoRepeatUntil___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoRepeatUntil___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoRepeatUntil___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 11, 184, 16, 157, 182, 78, 231)}};
static const lean_object* l_Lean_Fmt_fmtDoRepeatUntil___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoRepeatUntil___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoRepeatUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoRepeatUntil___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtDoRepeatUntil"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 178, 195, 30, 12, 36, 3, 251)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoNested(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoNested___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtDoNested"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtNestedAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 156, 111, 115, 40, 41, 166, 194)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNestedAction(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtNestedAction___closed__4));
lean_inc(v_x_10_);
v___x_14_ = l_Lean_Syntax_isOfKind(v_x_10_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec(v_x_10_);
v___x_15_ = l_Lean_Fmt_Error_partialFormatter;
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v_a_12_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v_leftArrowTk_18_; lean_object* v___x_19_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v_leftArrowTk_18_ = l_Lean_Syntax_getArg(v_x_10_, v___x_17_);
v___x_19_ = l_Lean_Fmt_fmt(v_leftArrowTk_18_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v___x_19_, 1);
lean_inc(v_a_21_);
lean_dec_ref_known(v___x_19_, 2);
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = l_Lean_Syntax_getArg(v_x_10_, v___x_22_);
lean_dec(v_x_10_);
v___x_24_ = l_Lean_Fmt_fmt(v___x_23_, v_a_11_, v_a_21_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_35_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_a_26_ = lean_ctor_get(v___x_24_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_35_ == 0)
{
v___x_28_ = v___x_24_;
v_isShared_29_ = v_isSharedCheck_35_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_35_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_30_ = 2;
v___x_31_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_20_, v_a_25_, v___x_30_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___x_31_);
v___x_33_ = v___x_28_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_a_26_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
else
{
lean_dec(v_a_20_);
return v___x_24_;
}
}
else
{
lean_dec(v_x_10_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNestedAction___boxed(lean_object* v_x_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Fmt_fmtNestedAction(v_x_36_, v_a_37_, v_a_38_);
lean_dec_ref(v_a_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1(){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_47_ = l_Lean_Fmt_fmtAttribute;
v___x_48_ = ((lean_object*)(l_Lean_Fmt_fmtNestedAction___closed__4));
v___x_49_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___closed__2));
v___x_50_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtNestedAction___boxed), 3, 0);
v___x_51_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_47_, v___x_48_, v___x_49_, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1___boxed(lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1();
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoExpr(lean_object* v_x_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = ((lean_object*)(l_Lean_Fmt_fmtDoExpr___closed__1));
lean_inc(v_x_60_);
v___x_64_ = l_Lean_Syntax_isOfKind(v_x_60_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_x_60_);
v___x_65_ = l_Lean_Fmt_Error_partialFormatter;
v___x_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v_a_62_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = l_Lean_Syntax_getArg(v_x_60_, v___x_67_);
lean_dec(v_x_60_);
v___x_69_ = l_Lean_Fmt_fmt(v___x_68_, v_a_61_, v_a_62_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoExpr___boxed(lean_object* v_x_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Fmt_fmtDoExpr(v_x_70_, v_a_71_, v_a_72_);
lean_dec_ref(v_a_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1(){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = l_Lean_Fmt_fmtAttribute;
v___x_81_ = ((lean_object*)(l_Lean_Fmt_fmtDoExpr___closed__1));
v___x_82_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___closed__1));
v___x_83_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoExpr___boxed), 3, 0);
v___x_84_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_80_, v___x_81_, v___x_82_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1___boxed(lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1();
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0(lean_object* v___x_90_, lean_object* v___x_91_, lean_object* v_x_92_, lean_object* v_semicolonTk_x3f_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___y_97_; 
if (lean_obj_tag(v_semicolonTk_x3f_93_) == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = lean_mk_empty_array_with_capacity(v___x_91_);
v___x_104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0___closed__1));
v___x_105_ = lean_box(2);
v___x_106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
lean_ctor_set(v___x_106_, 2, v___x_103_);
v___y_97_ = v___x_106_;
goto v___jp_96_;
}
else
{
lean_object* v_val_107_; 
v_val_107_ = lean_ctor_get(v_semicolonTk_x3f_93_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v_semicolonTk_x3f_93_, 1);
v___y_97_ = v_val_107_;
goto v___jp_96_;
}
v___jp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_98_ = lean_unsigned_to_nat(2u);
v___x_99_ = lean_mk_empty_array_with_capacity(v___x_98_);
v___x_100_ = lean_array_push(v___x_99_, v___x_90_);
v___x_101_ = lean_array_push(v___x_100_, v___y_97_);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___y_95_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0___boxed(lean_object* v___x_108_, lean_object* v___x_109_, lean_object* v_x_110_, lean_object* v_semicolonTk_x3f_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0(v___x_108_, v___x_109_, v_x_110_, v_semicolonTk_x3f_111_, v___y_112_, v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___x_109_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0(lean_object* v_as_121_, size_t v_i_122_, size_t v_stop_123_, lean_object* v_b_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___y_128_; uint8_t v___x_135_; 
v___x_135_ = lean_usize_dec_eq(v_i_122_, v_stop_123_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_array_uget_borrowed(v_as_121_, v_i_122_);
v___x_137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___closed__1));
lean_inc(v___x_136_);
v___x_138_ = l_Lean_Syntax_isOfKind(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec_ref(v_b_124_);
v___x_139_ = l_Lean_Fmt_Error_partialFormatter;
v___x_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___y_126_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = l_Lean_Syntax_getArg(v___x_136_, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = l_Lean_Syntax_getArg(v___x_136_, v___x_143_);
v___x_145_ = l_Lean_Syntax_isNone(v___x_144_);
if (v___x_145_ == 0)
{
uint8_t v___x_146_; 
lean_inc(v___x_144_);
v___x_146_ = l_Lean_Syntax_matchesNull(v___x_144_, v___x_143_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v___x_144_);
lean_dec(v___x_142_);
lean_dec_ref(v_b_124_);
v___x_147_ = l_Lean_Fmt_Error_partialFormatter;
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___y_126_);
return v___x_148_;
}
else
{
lean_object* v_semicolonTk_x3f_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_semicolonTk_x3f_149_ = l_Lean_Syntax_getArg(v___x_144_, v___x_141_);
lean_dec(v___x_144_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v_semicolonTk_x3f_149_);
v___x_152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0(v___x_142_, v___x_141_, v___x_150_, v___x_151_, v___y_125_, v___y_126_);
v___y_128_ = v___x_152_;
goto v___jp_127_;
}
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v___x_144_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_box(0);
v___x_155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___lam__0(v___x_142_, v___x_141_, v___x_153_, v___x_154_, v___y_125_, v___y_126_);
v___y_128_ = v___x_155_;
goto v___jp_127_;
}
}
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v_b_124_);
lean_ctor_set(v___x_156_, 1, v___y_126_);
return v___x_156_;
}
v___jp_127_:
{
if (lean_obj_tag(v___y_128_) == 0)
{
lean_object* v_a_129_; lean_object* v_a_130_; lean_object* v___x_131_; size_t v___x_132_; size_t v___x_133_; 
v_a_129_ = lean_ctor_get(v___y_128_, 0);
lean_inc(v_a_129_);
v_a_130_ = lean_ctor_get(v___y_128_, 1);
lean_inc(v_a_130_);
lean_dec_ref_known(v___y_128_, 2);
v___x_131_ = l_Array_append___redArg(v_b_124_, v_a_129_);
lean_dec(v_a_129_);
v___x_132_ = ((size_t)1ULL);
v___x_133_ = lean_usize_add(v_i_122_, v___x_132_);
v_i_122_ = v___x_133_;
v_b_124_ = v___x_131_;
v___y_126_ = v_a_130_;
goto _start;
}
else
{
lean_dec_ref(v_b_124_);
return v___y_128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0___boxed(lean_object* v_as_157_, lean_object* v_i_158_, lean_object* v_stop_159_, lean_object* v_b_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
size_t v_i_boxed_163_; size_t v_stop_boxed_164_; lean_object* v_res_165_; 
v_i_boxed_163_ = lean_unbox_usize(v_i_158_);
lean_dec(v_i_158_);
v_stop_boxed_164_ = lean_unbox_usize(v_stop_159_);
lean_dec(v_stop_159_);
v_res_165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0(v_as_157_, v_i_boxed_163_, v_stop_boxed_164_, v_b_160_, v___y_161_, v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec_ref(v_as_157_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqItems(lean_object* v_items_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_a_181_; lean_object* v_a_182_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqItems___closed__4));
v___x_188_ = lean_array_get_size(v_items_177_);
v___x_189_ = lean_nat_dec_lt(v___x_186_, v___x_188_);
if (v___x_189_ == 0)
{
v_a_181_ = v___x_187_;
v_a_182_ = v_a_179_;
goto v___jp_180_;
}
else
{
size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((size_t)0ULL);
v___x_191_ = lean_usize_of_nat(v___x_188_);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtDoSeqItems_spec__0(v_items_177_, v___x_190_, v___x_191_, v___x_187_, v_a_178_, v_a_179_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v_a_194_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
v_a_194_ = lean_ctor_get(v___x_192_, 1);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_192_, 2);
v_a_181_ = v_a_193_;
v_a_182_ = v_a_194_;
goto v___jp_180_;
}
else
{
lean_object* v_a_195_; lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_195_ = lean_ctor_get(v___x_192_, 0);
v_a_196_ = lean_ctor_get(v___x_192_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_192_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_inc(v_a_195_);
lean_dec(v___x_192_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_195_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
v___jp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqItems___closed__0));
v___x_184_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqItems___closed__3));
v___x_185_ = l_Lean_Fmt_fmtSeq___redArg(v___x_183_, v_a_181_, v___x_184_, v_a_178_, v_a_182_);
lean_dec_ref(v_a_181_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqItems___boxed(lean_object* v_items_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Fmt_fmtDoSeqItems(v_items_204_, v_a_205_, v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_items_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqIndent(lean_object* v_x_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqIndent___closed__1));
lean_inc(v_x_214_);
v___x_218_ = l_Lean_Syntax_isOfKind(v_x_214_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v_x_214_);
v___x_219_ = l_Lean_Fmt_Error_partialFormatter;
v___x_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v_a_216_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_items_223_; lean_object* v___x_224_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l_Lean_Syntax_getArg(v_x_214_, v___x_221_);
lean_dec(v_x_214_);
v_items_223_ = l_Lean_Syntax_getArgs(v___x_222_);
lean_dec(v___x_222_);
v___x_224_ = l_Lean_Fmt_fmtDoSeqItems(v_items_223_, v_a_215_, v_a_216_);
lean_dec_ref(v_items_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqIndent___boxed(lean_object* v_x_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Fmt_fmtDoSeqIndent(v_x_225_, v_a_226_, v_a_227_);
lean_dec_ref(v_a_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1(){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_235_ = l_Lean_Fmt_fmtAttribute;
v___x_236_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqIndent___closed__1));
v___x_237_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___closed__1));
v___x_238_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoSeqIndent___boxed), 3, 0);
v___x_239_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_235_, v___x_236_, v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1___boxed(lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1();
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqBracketed(lean_object* v_x_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqBracketed___closed__1));
lean_inc(v_x_248_);
v___x_252_ = l_Lean_Syntax_isOfKind(v_x_248_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_x_248_);
v___x_253_ = l_Lean_Fmt_Error_partialFormatter;
v___x_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v_a_250_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v_lbTk_256_; lean_object* v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v_lbTk_256_ = l_Lean_Syntax_getArg(v_x_248_, v___x_255_);
v___x_257_ = l_Lean_Fmt_fmt(v_lbTk_256_, v_a_249_, v_a_250_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v_a_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_items_262_; lean_object* v___x_263_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
v_a_259_ = lean_ctor_get(v___x_257_, 1);
lean_inc(v_a_259_);
lean_dec_ref_known(v___x_257_, 2);
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = l_Lean_Syntax_getArg(v_x_248_, v___x_260_);
v_items_262_ = l_Lean_Syntax_getArgs(v___x_261_);
lean_dec(v___x_261_);
v___x_263_ = l_Lean_Fmt_fmtDoSeqItems(v_items_262_, v_a_249_, v_a_259_);
lean_dec_ref(v_items_262_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v_a_265_; lean_object* v___x_266_; lean_object* v_rbTk_267_; lean_object* v___x_268_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
v_a_265_ = lean_ctor_get(v___x_263_, 1);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_263_, 2);
v___x_266_ = lean_unsigned_to_nat(2u);
v_rbTk_267_ = l_Lean_Syntax_getArg(v_x_248_, v___x_266_);
lean_dec(v_x_248_);
v___x_268_ = l_Lean_Fmt_fmt(v_rbTk_267_, v_a_249_, v_a_265_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_281_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_a_270_ = lean_ctor_get(v___x_268_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_281_ == 0)
{
v___x_272_ = v___x_268_;
v_isShared_273_ = v_isSharedCheck_281_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_281_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_274_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_275_ = 1;
v___x_276_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v___x_252_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1 + 1, v___x_275_);
v___x_277_ = l_Lean_Fmt_Layouts_bracketed(v_a_258_, v_a_264_, v_a_269_, v___x_276_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_277_);
v___x_279_ = v___x_272_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_a_270_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_dec(v_a_264_);
lean_dec(v_a_258_);
return v___x_268_;
}
}
else
{
lean_dec(v_a_258_);
lean_dec(v_x_248_);
return v___x_263_;
}
}
else
{
lean_dec(v_x_248_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoSeqBracketed___boxed(lean_object* v_x_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Fmt_fmtDoSeqBracketed(v_x_282_, v_a_283_, v_a_284_);
lean_dec_ref(v_a_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1(){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_292_ = l_Lean_Fmt_fmtAttribute;
v___x_293_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqBracketed___closed__1));
v___x_294_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___closed__1));
v___x_295_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoSeqBracketed___boxed), 3, 0);
v___x_296_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_292_, v___x_293_, v___x_294_, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1___boxed(lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1();
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDo(lean_object* v_x_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_Fmt_fmtDo___closed__1));
lean_inc(v_x_305_);
v___x_309_ = l_Lean_Syntax_isOfKind(v_x_305_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_x_305_);
v___x_310_ = l_Lean_Fmt_Error_partialFormatter;
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_a_307_);
return v___x_311_;
}
else
{
lean_object* v___x_312_; lean_object* v_doTk_313_; lean_object* v___x_314_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v_doTk_313_ = l_Lean_Syntax_getArg(v_x_305_, v___x_312_);
v___x_314_ = l_Lean_Fmt_fmt(v_doTk_313_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v_a_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
v_a_316_ = lean_ctor_get(v___x_314_, 1);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_314_, 2);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = l_Lean_Syntax_getArg(v_x_305_, v___x_317_);
lean_dec(v_x_305_);
v___x_319_ = l_Lean_Fmt_fmt(v___x_318_, v_a_306_, v_a_316_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_330_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_a_321_ = lean_ctor_get(v___x_319_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_330_ == 0)
{
v___x_323_ = v___x_319_;
v_isShared_324_ = v_isSharedCheck_330_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_330_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = 0;
v___x_326_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_315_, v_a_320_, v___x_325_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_326_);
v___x_328_ = v___x_323_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_a_321_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
else
{
lean_dec(v_a_315_);
return v___x_319_;
}
}
else
{
lean_dec(v_x_305_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDo___boxed(lean_object* v_x_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Fmt_fmtDo(v_x_331_, v_a_332_, v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1(){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_341_ = l_Lean_Fmt_fmtAttribute;
v___x_342_ = ((lean_object*)(l_Lean_Fmt_fmtDo___closed__1));
v___x_343_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___closed__1));
v___x_344_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDo___boxed), 3, 0);
v___x_345_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_341_, v___x_342_, v___x_343_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1___boxed(lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1();
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermReturn(lean_object* v_x_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; uint8_t v___x_358_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; 
v___x_357_ = ((lean_object*)(l_Lean_Fmt_fmtTermReturn___closed__1));
lean_inc(v_x_354_);
v___x_358_ = l_Lean_Syntax_isOfKind(v_x_354_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec(v_x_354_);
v___x_382_ = l_Lean_Fmt_Error_partialFormatter;
v___x_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v_a_356_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; lean_object* v_returnTk_385_; lean_object* v_t_x3f_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_384_ = lean_unsigned_to_nat(0u);
v_returnTk_385_ = l_Lean_Syntax_getArg(v_x_354_, v___x_384_);
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = l_Lean_Syntax_getArg(v_x_354_, v___x_404_);
lean_dec(v_x_354_);
v___x_406_ = l_Lean_Syntax_isNone(v___x_405_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
lean_inc(v___x_405_);
v___x_407_ = l_Lean_Syntax_matchesNull(v___x_405_, v___x_404_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v___x_405_);
lean_dec(v_returnTk_385_);
v___x_408_ = l_Lean_Fmt_Error_partialFormatter;
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_a_356_);
return v___x_409_;
}
else
{
lean_object* v_t_x3f_410_; lean_object* v___x_411_; 
v_t_x3f_410_ = l_Lean_Syntax_getArg(v___x_405_, v___x_384_);
lean_dec(v___x_405_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v_t_x3f_410_);
v_t_x3f_387_ = v___x_411_;
v___y_388_ = v_a_355_;
v___y_389_ = v_a_356_;
goto v___jp_386_;
}
}
else
{
lean_object* v___x_412_; 
lean_dec(v___x_405_);
v___x_412_ = lean_box(0);
v_t_x3f_387_ = v___x_412_;
v___y_388_ = v_a_355_;
v___y_389_ = v_a_356_;
goto v___jp_386_;
}
v___jp_386_:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Fmt_fmt(v_returnTk_385_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_390_) == 0)
{
if (lean_obj_tag(v_t_x3f_387_) == 0)
{
lean_object* v_a_391_; lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
v_a_392_ = lean_ctor_get(v___x_390_, 1);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_390_, 2);
v___x_393_ = lean_box(0);
v___y_360_ = v___y_388_;
v___y_361_ = v_a_392_;
v___y_362_ = v_a_391_;
v___y_363_ = v___x_393_;
goto v___jp_359_;
}
else
{
lean_object* v_a_394_; lean_object* v_a_395_; lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_a_394_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_394_);
v_a_395_ = lean_ctor_get(v___x_390_, 1);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_390_, 2);
v_val_396_ = lean_ctor_get(v_t_x3f_387_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_t_x3f_387_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v_t_x3f_387_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_dec(v_t_x3f_387_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_val_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
v___y_360_ = v___y_388_;
v___y_361_ = v_a_395_;
v___y_362_ = v_a_394_;
v___y_363_ = v___x_401_;
goto v___jp_359_;
}
}
}
}
else
{
lean_dec(v_t_x3f_387_);
return v___x_390_;
}
}
}
v___jp_359_:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Fmt_fmt_x3f(v___y_363_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_381_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_a_366_ = lean_ctor_get(v___x_364_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_381_ == 0)
{
v___x_368_ = v___x_364_;
v_isShared_369_ = v_isSharedCheck_381_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_381_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_370_ = lean_unsigned_to_nat(2u);
v___x_371_ = lean_mk_empty_array_with_capacity(v___x_370_);
v___x_372_ = lean_array_push(v___x_371_, v___y_362_);
v___x_373_ = lean_array_push(v___x_372_, v_a_365_);
v___x_374_ = 0;
v___x_375_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_375_, 0, v___x_358_);
lean_ctor_set_uint8(v___x_375_, 1, v___x_374_);
lean_ctor_set_uint8(v___x_375_, 2, v___x_374_);
lean_ctor_set_uint8(v___x_375_, 3, v___x_374_);
v___x_376_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_373_, v___x_375_);
v___x_377_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_376_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_377_);
v___x_379_ = v___x_368_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_a_366_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_dec_ref(v___y_362_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermReturn___boxed(lean_object* v_x_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Fmt_fmtTermReturn(v_x_413_, v_a_414_, v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1(){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_423_ = l_Lean_Fmt_fmtAttribute;
v___x_424_ = ((lean_object*)(l_Lean_Fmt_fmtTermReturn___closed__1));
v___x_425_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___closed__1));
v___x_426_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermReturn___boxed), 3, 0);
v___x_427_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_423_, v___x_424_, v___x_425_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1___boxed(lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1();
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoBreak(lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Fmt_fmtAtomic(v_a_430_, v_a_431_, v_a_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoBreak___boxed(lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Fmt_fmtDoBreak(v_a_434_, v_a_435_, v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1(){
_start:
{
lean_object* v___f_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___f_451_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__0));
v___x_452_ = l_Lean_Fmt_fmtAttribute;
v___x_453_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__2));
v___x_454_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__4));
v___x_455_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_452_, v___x_453_, v___x_454_, v___f_451_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___boxed(lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1();
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoContinue(lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Fmt_fmtAtomic(v_a_458_, v_a_459_, v_a_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoContinue___boxed(lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Fmt_fmtDoContinue(v_a_462_, v_a_463_, v_a_464_);
lean_dec_ref(v_a_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1(){
_start:
{
lean_object* v___f_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___f_478_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1___closed__0));
v___x_479_ = l_Lean_Fmt_fmtAttribute;
v___x_480_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__1));
v___x_481_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___closed__3));
v___x_482_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_479_, v___x_480_, v___x_481_, v___f_478_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1___boxed(lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1();
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReturn(lean_object* v_x_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; 
v___x_494_ = ((lean_object*)(l_Lean_Fmt_fmtDoReturn___closed__1));
lean_inc(v_x_491_);
v___x_495_ = l_Lean_Syntax_isOfKind(v_x_491_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v_x_491_);
v___x_519_ = l_Lean_Fmt_Error_partialFormatter;
v___x_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v_a_493_);
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v_returnTk_522_; lean_object* v_e_x3f_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_521_ = lean_unsigned_to_nat(0u);
v_returnTk_522_ = l_Lean_Syntax_getArg(v_x_491_, v___x_521_);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = l_Lean_Syntax_getArg(v_x_491_, v___x_541_);
lean_dec(v_x_491_);
v___x_543_ = l_Lean_Syntax_isNone(v___x_542_);
if (v___x_543_ == 0)
{
uint8_t v___x_544_; 
lean_inc(v___x_542_);
v___x_544_ = l_Lean_Syntax_matchesNull(v___x_542_, v___x_541_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v___x_542_);
lean_dec(v_returnTk_522_);
v___x_545_ = l_Lean_Fmt_Error_partialFormatter;
v___x_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v_a_493_);
return v___x_546_;
}
else
{
lean_object* v_e_x3f_547_; lean_object* v___x_548_; 
v_e_x3f_547_ = l_Lean_Syntax_getArg(v___x_542_, v___x_521_);
lean_dec(v___x_542_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_e_x3f_547_);
v_e_x3f_524_ = v___x_548_;
v___y_525_ = v_a_492_;
v___y_526_ = v_a_493_;
goto v___jp_523_;
}
}
else
{
lean_object* v___x_549_; 
lean_dec(v___x_542_);
v___x_549_ = lean_box(0);
v_e_x3f_524_ = v___x_549_;
v___y_525_ = v_a_492_;
v___y_526_ = v_a_493_;
goto v___jp_523_;
}
v___jp_523_:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Fmt_fmt(v_returnTk_522_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
if (lean_obj_tag(v_e_x3f_524_) == 0)
{
lean_object* v_a_528_; lean_object* v_a_529_; lean_object* v___x_530_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
v_a_529_ = lean_ctor_get(v___x_527_, 1);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_527_, 2);
v___x_530_ = lean_box(0);
v___y_497_ = v_a_529_;
v___y_498_ = v___y_525_;
v___y_499_ = v_a_528_;
v___y_500_ = v___x_530_;
goto v___jp_496_;
}
else
{
lean_object* v_a_531_; lean_object* v_a_532_; lean_object* v_val_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
v_a_531_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_531_);
v_a_532_ = lean_ctor_get(v___x_527_, 1);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_527_, 2);
v_val_533_ = lean_ctor_get(v_e_x3f_524_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v_e_x3f_524_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v_e_x3f_524_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_val_533_);
lean_dec(v_e_x3f_524_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_val_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
v___y_497_ = v_a_532_;
v___y_498_ = v___y_525_;
v___y_499_ = v_a_531_;
v___y_500_ = v___x_538_;
goto v___jp_496_;
}
}
}
}
else
{
lean_dec(v_e_x3f_524_);
return v___x_527_;
}
}
}
v___jp_496_:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Fmt_fmt_x3f(v___y_500_, v___y_498_, v___y_497_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_518_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_a_503_ = lean_ctor_get(v___x_501_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_518_ == 0)
{
v___x_505_ = v___x_501_;
v_isShared_506_ = v_isSharedCheck_518_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_518_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_507_ = lean_unsigned_to_nat(2u);
v___x_508_ = lean_mk_empty_array_with_capacity(v___x_507_);
v___x_509_ = lean_array_push(v___x_508_, v___y_499_);
v___x_510_ = lean_array_push(v___x_509_, v_a_502_);
v___x_511_ = 0;
v___x_512_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_512_, 0, v___x_495_);
lean_ctor_set_uint8(v___x_512_, 1, v___x_511_);
lean_ctor_set_uint8(v___x_512_, 2, v___x_511_);
lean_ctor_set_uint8(v___x_512_, 3, v___x_511_);
v___x_513_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_510_, v___x_512_);
v___x_514_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_513_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_514_);
v___x_516_ = v___x_505_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_a_503_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
lean_dec_ref(v___y_499_);
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReturn___boxed(lean_object* v_x_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Fmt_fmtDoReturn(v_x_550_, v_a_551_, v_a_552_);
lean_dec_ref(v_a_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1(){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_560_ = l_Lean_Fmt_fmtAttribute;
v___x_561_ = ((lean_object*)(l_Lean_Fmt_fmtDoReturn___closed__1));
v___x_562_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___closed__1));
v___x_563_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoReturn___boxed), 3, 0);
v___x_564_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_560_, v___x_561_, v___x_562_, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1___boxed(lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1();
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoDbgTrace(lean_object* v_x_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Fmt_fmtDoDbgTrace___closed__1));
lean_inc(v_x_573_);
v___x_577_ = l_Lean_Syntax_isOfKind(v_x_573_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_x_573_);
v___x_578_ = l_Lean_Fmt_Error_partialFormatter;
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_a_575_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v_dbgTraceTk_581_; lean_object* v___x_582_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v_dbgTraceTk_581_ = l_Lean_Syntax_getArg(v_x_573_, v___x_580_);
v___x_582_ = l_Lean_Fmt_fmt(v_dbgTraceTk_581_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
v_a_584_ = lean_ctor_get(v___x_582_, 1);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_582_, 2);
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = l_Lean_Syntax_getArg(v_x_573_, v___x_585_);
lean_dec(v_x_573_);
v___x_587_ = l_Lean_Fmt_fmt(v___x_586_, v_a_574_, v_a_584_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_603_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_a_589_ = lean_ctor_get(v___x_587_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_603_ == 0)
{
v___x_591_ = v___x_587_;
v_isShared_592_ = v_isSharedCheck_603_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_603_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_593_ = lean_unsigned_to_nat(2u);
v___x_594_ = lean_mk_empty_array_with_capacity(v___x_593_);
v___x_595_ = lean_array_push(v___x_594_, v_a_583_);
v___x_596_ = lean_array_push(v___x_595_, v_a_588_);
v___x_597_ = 0;
v___x_598_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_598_, 0, v___x_577_);
lean_ctor_set_uint8(v___x_598_, 1, v___x_597_);
lean_ctor_set_uint8(v___x_598_, 2, v___x_597_);
lean_ctor_set_uint8(v___x_598_, 3, v___x_597_);
v___x_599_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_596_, v___x_598_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_599_);
v___x_601_ = v___x_591_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_a_589_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
lean_dec(v_a_583_);
return v___x_587_;
}
}
else
{
lean_dec(v_x_573_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoDbgTrace___boxed(lean_object* v_x_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Fmt_fmtDoDbgTrace(v_x_604_, v_a_605_, v_a_606_);
lean_dec_ref(v_a_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1(){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_614_ = l_Lean_Fmt_fmtAttribute;
v___x_615_ = ((lean_object*)(l_Lean_Fmt_fmtDoDbgTrace___closed__1));
v___x_616_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___closed__1));
v___x_617_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoDbgTrace___boxed), 3, 0);
v___x_618_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_614_, v___x_615_, v___x_616_, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1___boxed(lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1();
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoAssert(lean_object* v_x_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_Fmt_fmtDoAssert___closed__1));
lean_inc(v_x_627_);
v___x_631_ = l_Lean_Syntax_isOfKind(v_x_627_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v_x_627_);
v___x_632_ = l_Lean_Fmt_Error_partialFormatter;
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v_a_629_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v_assertTk_635_; lean_object* v___x_636_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v_assertTk_635_ = l_Lean_Syntax_getArg(v_x_627_, v___x_634_);
v___x_636_ = l_Lean_Fmt_fmt(v_assertTk_635_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v_a_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
v_a_638_ = lean_ctor_get(v___x_636_, 1);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_636_, 2);
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = l_Lean_Syntax_getArg(v_x_627_, v___x_639_);
lean_dec(v_x_627_);
v___x_641_ = l_Lean_Fmt_fmt(v___x_640_, v_a_628_, v_a_638_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_657_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_a_643_ = lean_ctor_get(v___x_641_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_657_ == 0)
{
v___x_645_ = v___x_641_;
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_647_ = lean_unsigned_to_nat(2u);
v___x_648_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___x_649_ = lean_array_push(v___x_648_, v_a_637_);
v___x_650_ = lean_array_push(v___x_649_, v_a_642_);
v___x_651_ = 0;
v___x_652_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_652_, 0, v___x_631_);
lean_ctor_set_uint8(v___x_652_, 1, v___x_651_);
lean_ctor_set_uint8(v___x_652_, 2, v___x_651_);
lean_ctor_set_uint8(v___x_652_, 3, v___x_651_);
v___x_653_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_650_, v___x_652_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_653_);
v___x_655_ = v___x_645_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_a_643_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
else
{
lean_dec(v_a_637_);
return v___x_641_;
}
}
else
{
lean_dec(v_x_627_);
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoAssert___boxed(lean_object* v_x_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Fmt_fmtDoAssert(v_x_658_, v_a_659_, v_a_660_);
lean_dec_ref(v_a_659_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1(){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_668_ = l_Lean_Fmt_fmtAttribute;
v___x_669_ = ((lean_object*)(l_Lean_Fmt_fmtDoAssert___closed__1));
v___x_670_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___closed__1));
v___x_671_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoAssert___boxed), 3, 0);
v___x_672_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_668_, v___x_669_, v___x_670_, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1___boxed(lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1();
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoDebugAssert(lean_object* v_x_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_Fmt_fmtDoDebugAssert___closed__1));
lean_inc(v_x_681_);
v___x_685_ = l_Lean_Syntax_isOfKind(v_x_681_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v_x_681_);
v___x_686_ = l_Lean_Fmt_Error_partialFormatter;
v___x_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v_a_683_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; lean_object* v_debugAssertTk_689_; lean_object* v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v_debugAssertTk_689_ = l_Lean_Syntax_getArg(v_x_681_, v___x_688_);
v___x_690_ = l_Lean_Fmt_fmt(v_debugAssertTk_689_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v_a_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
v_a_692_ = lean_ctor_get(v___x_690_, 1);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_690_, 2);
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = l_Lean_Syntax_getArg(v_x_681_, v___x_693_);
lean_dec(v_x_681_);
v___x_695_ = l_Lean_Fmt_fmt(v___x_694_, v_a_682_, v_a_692_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_711_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_a_697_ = lean_ctor_get(v___x_695_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_711_ == 0)
{
v___x_699_ = v___x_695_;
v_isShared_700_ = v_isSharedCheck_711_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_711_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_701_ = lean_unsigned_to_nat(2u);
v___x_702_ = lean_mk_empty_array_with_capacity(v___x_701_);
v___x_703_ = lean_array_push(v___x_702_, v_a_691_);
v___x_704_ = lean_array_push(v___x_703_, v_a_696_);
v___x_705_ = 0;
v___x_706_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_706_, 0, v___x_685_);
lean_ctor_set_uint8(v___x_706_, 1, v___x_705_);
lean_ctor_set_uint8(v___x_706_, 2, v___x_705_);
lean_ctor_set_uint8(v___x_706_, 3, v___x_705_);
v___x_707_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_704_, v___x_706_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_707_);
v___x_709_ = v___x_699_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_a_697_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_dec(v_a_691_);
return v___x_695_;
}
}
else
{
lean_dec(v_x_681_);
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoDebugAssert___boxed(lean_object* v_x_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Fmt_fmtDoDebugAssert(v_x_712_, v_a_713_, v_a_714_);
lean_dec_ref(v_a_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1(){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_722_ = l_Lean_Fmt_fmtAttribute;
v___x_723_ = ((lean_object*)(l_Lean_Fmt_fmtDoDebugAssert___closed__1));
v___x_724_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___closed__1));
v___x_725_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoDebugAssert___boxed), 3, 0);
v___x_726_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_722_, v___x_723_, v___x_724_, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1___boxed(lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1();
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoRepeat(lean_object* v_x_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_Fmt_fmtDoRepeat___closed__1));
lean_inc(v_x_735_);
v___x_739_ = l_Lean_Syntax_isOfKind(v_x_735_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_x_735_);
v___x_740_ = l_Lean_Fmt_Error_partialFormatter;
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_a_737_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = l_Lean_Syntax_getArg(v_x_735_, v___x_743_);
v___x_745_ = l_Lean_Syntax_matchesNull(v___x_744_, v___x_742_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v_x_735_);
v___x_746_ = l_Lean_Fmt_Error_partialFormatter;
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v_a_737_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = lean_unsigned_to_nat(2u);
v___x_749_ = l_Lean_Syntax_getArg(v_x_735_, v___x_748_);
v___x_750_ = l_Lean_Syntax_matchesNull(v___x_749_, v___x_742_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec(v_x_735_);
v___x_751_ = l_Lean_Fmt_Error_partialFormatter;
v___x_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v_a_737_);
return v___x_752_;
}
else
{
lean_object* v_repeatTk_753_; lean_object* v___x_754_; 
v_repeatTk_753_ = l_Lean_Syntax_getArg(v_x_735_, v___x_742_);
v___x_754_ = l_Lean_Fmt_fmt(v_repeatTk_753_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v_a_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
v_a_756_ = lean_ctor_get(v___x_754_, 1);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_754_, 2);
v___x_757_ = lean_unsigned_to_nat(3u);
v___x_758_ = l_Lean_Syntax_getArg(v_x_735_, v___x_757_);
lean_dec(v_x_735_);
v___x_759_ = l_Lean_Fmt_fmt(v___x_758_, v_a_736_, v_a_756_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_770_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_a_761_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_770_ == 0)
{
v___x_763_ = v___x_759_;
v_isShared_764_ = v_isSharedCheck_770_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_770_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
uint8_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_765_ = 1;
v___x_766_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_755_, v_a_760_, v___x_765_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_a_761_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
else
{
lean_dec(v_a_755_);
return v___x_759_;
}
}
else
{
lean_dec(v_x_735_);
return v___x_754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoRepeat___boxed(lean_object* v_x_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Fmt_fmtDoRepeat(v_x_771_, v_a_772_, v_a_773_);
lean_dec_ref(v_a_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1(){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_781_ = l_Lean_Fmt_fmtAttribute;
v___x_782_ = ((lean_object*)(l_Lean_Fmt_fmtDoRepeat___closed__1));
v___x_783_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___closed__1));
v___x_784_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoRepeat___boxed), 3, 0);
v___x_785_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_781_, v___x_782_, v___x_783_, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1___boxed(lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1();
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLet(lean_object* v_x_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = ((lean_object*)(l_Lean_Fmt_fmtDoLet___closed__1));
lean_inc(v_x_806_);
v___x_810_ = l_Lean_Syntax_isOfKind(v_x_806_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v_x_806_);
v___x_811_ = l_Lean_Fmt_Error_partialFormatter;
v___x_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_a_808_);
return v___x_812_;
}
else
{
lean_object* v___x_813_; lean_object* v_letTk_814_; lean_object* v_mutTk_x3f_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_813_ = lean_unsigned_to_nat(0u);
v_letTk_814_ = l_Lean_Syntax_getArg(v_x_806_, v___x_813_);
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = l_Lean_Syntax_getArg(v_x_806_, v___x_856_);
v___x_858_ = l_Lean_Syntax_isNone(v___x_857_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; 
lean_inc(v___x_857_);
v___x_859_ = l_Lean_Syntax_matchesNull(v___x_857_, v___x_856_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec(v___x_857_);
lean_dec(v_letTk_814_);
lean_dec(v_x_806_);
v___x_860_ = l_Lean_Fmt_Error_partialFormatter;
v___x_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v_a_808_);
return v___x_861_;
}
else
{
lean_object* v_mutTk_x3f_862_; lean_object* v___x_863_; 
v_mutTk_x3f_862_ = l_Lean_Syntax_getArg(v___x_857_, v___x_813_);
lean_dec(v___x_857_);
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_mutTk_x3f_862_);
v_mutTk_x3f_816_ = v___x_863_;
v___y_817_ = v_a_807_;
v___y_818_ = v_a_808_;
goto v___jp_815_;
}
}
else
{
lean_object* v___x_864_; 
lean_dec(v___x_857_);
v___x_864_ = lean_box(0);
v_mutTk_x3f_816_ = v___x_864_;
v___y_817_ = v_a_807_;
v___y_818_ = v_a_808_;
goto v___jp_815_;
}
v___jp_815_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_819_ = lean_unsigned_to_nat(2u);
v___x_820_ = l_Lean_Syntax_getArg(v_x_806_, v___x_819_);
v___x_821_ = ((lean_object*)(l_Lean_Fmt_fmtDoLet___closed__3));
lean_inc(v___x_820_);
v___x_822_ = l_Lean_Syntax_isOfKind(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v___x_820_);
lean_dec(v_mutTk_x3f_816_);
lean_dec(v_letTk_814_);
lean_dec(v_x_806_);
v___x_823_ = l_Lean_Fmt_Error_partialFormatter;
v___x_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___y_818_);
return v___x_824_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_825_ = lean_unsigned_to_nat(3u);
v___x_826_ = l_Lean_Syntax_getArg(v_x_806_, v___x_825_);
lean_dec(v_x_806_);
v___x_827_ = ((lean_object*)(l_Lean_Fmt_fmtDoLet___closed__5));
lean_inc(v___x_826_);
v___x_828_ = l_Lean_Syntax_isOfKind(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v___x_826_);
lean_dec(v___x_820_);
lean_dec(v_mutTk_x3f_816_);
lean_dec(v_letTk_814_);
v___x_829_ = l_Lean_Fmt_Error_partialFormatter;
v___x_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___y_818_);
return v___x_830_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Fmt_fmt(v_letTk_814_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v_a_833_; lean_object* v___x_834_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
v_a_833_ = lean_ctor_get(v___x_831_, 1);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_831_, 2);
v___x_834_ = l_Lean_Fmt_fmt_x3f(v_mutTk_x3f_816_, v___y_817_, v_a_833_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v_a_836_; lean_object* v___x_837_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
v_a_836_ = lean_ctor_get(v___x_834_, 1);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_834_, 2);
v___x_837_ = l_Lean_Fmt_fmt(v___x_820_, v___y_817_, v_a_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v_a_839_; lean_object* v___x_840_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
v_a_839_ = lean_ctor_get(v___x_837_, 1);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_837_, 2);
v___x_840_ = l_Lean_Fmt_fmt(v___x_826_, v___y_817_, v_a_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_855_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_a_842_ = lean_ctor_get(v___x_840_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_855_ == 0)
{
v___x_844_ = v___x_840_;
v_isShared_845_ = v_isSharedCheck_855_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_855_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_846_ = lean_mk_empty_array_with_capacity(v___x_819_);
v___x_847_ = lean_array_push(v___x_846_, v_a_832_);
v___x_848_ = lean_array_push(v___x_847_, v_a_835_);
v___x_849_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_848_);
lean_dec_ref(v___x_848_);
v___x_850_ = 0;
v___x_851_ = l_Lean_Fmt_Layouts_letDecl(v___x_849_, v_a_838_, v_a_841_, v___x_850_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_851_);
v___x_853_ = v___x_844_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_a_842_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_dec(v_a_838_);
lean_dec(v_a_835_);
lean_dec(v_a_832_);
return v___x_840_;
}
}
else
{
lean_dec(v_a_835_);
lean_dec(v_a_832_);
lean_dec(v___x_826_);
return v___x_837_;
}
}
else
{
lean_dec(v_a_832_);
lean_dec(v___x_826_);
lean_dec(v___x_820_);
return v___x_834_;
}
}
else
{
lean_dec(v___x_826_);
lean_dec(v___x_820_);
lean_dec(v_mutTk_x3f_816_);
return v___x_831_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLet___boxed(lean_object* v_x_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Fmt_fmtDoLet(v_x_865_, v_a_866_, v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1(){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_875_ = l_Lean_Fmt_fmtAttribute;
v___x_876_ = ((lean_object*)(l_Lean_Fmt_fmtDoLet___closed__1));
v___x_877_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___closed__1));
v___x_878_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoLet___boxed), 3, 0);
v___x_879_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_875_, v___x_876_, v___x_877_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1___boxed(lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1();
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoHave(lean_object* v_x_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_Fmt_fmtDoHave___closed__1));
lean_inc(v_x_888_);
v___x_892_ = l_Lean_Syntax_isOfKind(v_x_888_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec(v_x_888_);
v___x_893_ = l_Lean_Fmt_Error_partialFormatter;
v___x_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v_a_890_);
return v___x_894_;
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_895_ = lean_unsigned_to_nat(1u);
v___x_896_ = l_Lean_Syntax_getArg(v_x_888_, v___x_895_);
v___x_897_ = ((lean_object*)(l_Lean_Fmt_fmtDoLet___closed__3));
lean_inc(v___x_896_);
v___x_898_ = l_Lean_Syntax_isOfKind(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec(v___x_896_);
lean_dec(v_x_888_);
v___x_899_ = l_Lean_Fmt_Error_partialFormatter;
v___x_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v_a_890_);
return v___x_900_;
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_901_ = lean_unsigned_to_nat(2u);
v___x_902_ = l_Lean_Syntax_getArg(v_x_888_, v___x_901_);
v___x_903_ = ((lean_object*)(l_Lean_Fmt_fmtDoLet___closed__5));
lean_inc(v___x_902_);
v___x_904_ = l_Lean_Syntax_isOfKind(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec(v___x_902_);
lean_dec(v___x_896_);
lean_dec(v_x_888_);
v___x_905_ = l_Lean_Fmt_Error_partialFormatter;
v___x_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v_a_890_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v_haveTk_908_; lean_object* v___x_909_; 
v___x_907_ = lean_unsigned_to_nat(0u);
v_haveTk_908_ = l_Lean_Syntax_getArg(v_x_888_, v___x_907_);
lean_dec(v_x_888_);
v___x_909_ = l_Lean_Fmt_fmt(v_haveTk_908_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v_a_911_; lean_object* v___x_912_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
v_a_911_ = lean_ctor_get(v___x_909_, 1);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_909_, 2);
v___x_912_ = l_Lean_Fmt_fmt(v___x_896_, v_a_889_, v_a_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v_a_914_; lean_object* v___x_915_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
v_a_914_ = lean_ctor_get(v___x_912_, 1);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_912_, 2);
v___x_915_ = l_Lean_Fmt_fmt(v___x_902_, v_a_889_, v_a_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_926_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_a_917_ = lean_ctor_get(v___x_915_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_926_ == 0)
{
v___x_919_ = v___x_915_;
v_isShared_920_ = v_isSharedCheck_926_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_926_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_921_ = 0;
v___x_922_ = l_Lean_Fmt_Layouts_letDecl(v_a_910_, v_a_913_, v_a_916_, v___x_921_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_922_);
v___x_924_ = v___x_919_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_a_917_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
else
{
lean_dec(v_a_913_);
lean_dec(v_a_910_);
return v___x_915_;
}
}
else
{
lean_dec(v_a_910_);
lean_dec(v___x_902_);
return v___x_912_;
}
}
else
{
lean_dec(v___x_902_);
lean_dec(v___x_896_);
return v___x_909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoHave___boxed(lean_object* v_x_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Fmt_fmtDoHave(v_x_927_, v_a_928_, v_a_929_);
lean_dec_ref(v_a_928_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1(){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_937_ = l_Lean_Fmt_fmtAttribute;
v___x_938_ = ((lean_object*)(l_Lean_Fmt_fmtDoHave___closed__1));
v___x_939_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___closed__1));
v___x_940_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoHave___boxed), 3, 0);
v___x_941_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_937_, v___x_938_, v___x_939_, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1___boxed(lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1();
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetElseLike(lean_object* v_decl_946_, lean_object* v_declComponents_947_, lean_object* v_pipeTk_x3f_948_, lean_object* v_elseSeq_x3f_949_, lean_object* v_body_x3f_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_981_; 
if (lean_obj_tag(v_pipeTk_x3f_948_) == 0)
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElseLike___closed__0));
v___y_981_ = v___x_988_;
goto v___jp_980_;
}
else
{
lean_object* v_val_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_val_989_ = lean_ctor_get(v_pipeTk_x3f_948_, 0);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_990_);
lean_inc(v_val_989_);
v___x_992_ = lean_array_push(v___x_991_, v_val_989_);
v___y_981_ = v___x_992_;
goto v___jp_980_;
}
v___jp_953_:
{
if (lean_obj_tag(v_body_x3f_950_) == 1)
{
lean_object* v_val_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_val_957_ = lean_ctor_get(v_body_x3f_950_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v_body_x3f_950_, 1);
v___x_958_ = lean_box(0);
v___x_959_ = l_Lean_Fmt_fmtTermInstruction(v___y_956_, v___y_954_, v___x_958_, v_val_957_, v_a_951_, v___y_955_);
return v___x_959_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec_ref(v___y_954_);
lean_dec(v_body_x3f_950_);
v___x_960_ = l_Lean_Fmt_TaggedDoc_withPosition(v___y_956_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___y_955_);
return v___x_961_;
}
}
v___jp_962_:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Fmt_fmt_x3f(v_pipeTk_x3f_948_, v_a_951_, v_a_952_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v_a_967_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
v_a_967_ = lean_ctor_get(v___x_965_, 1);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_965_, 2);
v___x_968_ = l_Lean_Fmt_fmt_x3f(v_elseSeq_x3f_949_, v_a_951_, v_a_967_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v_a_970_; lean_object* v_instructionComponents_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
v_a_970_ = lean_ctor_get(v___x_968_, 1);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_968_, 2);
v_instructionComponents_971_ = l_Array_append___redArg(v___y_963_, v___y_964_);
lean_dec_ref(v___y_964_);
v___x_972_ = lean_unsigned_to_nat(2u);
v___x_973_ = lean_mk_empty_array_with_capacity(v___x_972_);
v___x_974_ = lean_array_push(v___x_973_, v_a_966_);
v___x_975_ = lean_array_push(v___x_974_, v_a_969_);
v___x_976_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v___x_975_);
lean_dec_ref(v___x_975_);
v___x_977_ = l_Lean_Fmt_TaggedDoc_nested(v___x_976_);
v___x_978_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Fmt_Layouts_matchDeclaration(v_decl_946_, v___x_977_);
v___y_954_ = v_instructionComponents_971_;
v___y_955_ = v_a_970_;
v___y_956_ = v___x_979_;
goto v___jp_953_;
}
else
{
lean_dec_ref(v___x_977_);
v___y_954_ = v_instructionComponents_971_;
v___y_955_ = v_a_970_;
v___y_956_ = v_decl_946_;
goto v___jp_953_;
}
}
else
{
lean_dec(v_a_966_);
lean_dec_ref(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v_body_x3f_950_);
lean_dec_ref(v_decl_946_);
return v___x_968_;
}
}
else
{
lean_dec_ref(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v_body_x3f_950_);
lean_dec(v_elseSeq_x3f_949_);
lean_dec_ref(v_decl_946_);
return v___x_965_;
}
}
v___jp_980_:
{
lean_object* v___x_982_; 
v___x_982_ = l_Array_append___redArg(v_declComponents_947_, v___y_981_);
lean_dec_ref(v___y_981_);
if (lean_obj_tag(v_elseSeq_x3f_949_) == 0)
{
lean_object* v___x_983_; 
v___x_983_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElseLike___closed__0));
v___y_963_ = v___x_982_;
v___y_964_ = v___x_983_;
goto v___jp_962_;
}
else
{
lean_object* v_val_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_val_984_ = lean_ctor_get(v_elseSeq_x3f_949_, 0);
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_mk_empty_array_with_capacity(v___x_985_);
lean_inc(v_val_984_);
v___x_987_ = lean_array_push(v___x_986_, v_val_984_);
v___y_963_ = v___x_982_;
v___y_964_ = v___x_987_;
goto v___jp_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetElseLike___boxed(lean_object* v_decl_993_, lean_object* v_declComponents_994_, lean_object* v_pipeTk_x3f_995_, lean_object* v_elseSeq_x3f_996_, lean_object* v_body_x3f_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Fmt_fmtDoLetElseLike(v_decl_993_, v_declComponents_994_, v_pipeTk_x3f_995_, v_elseSeq_x3f_996_, v_body_x3f_997_, v_a_998_, v_a_999_);
lean_dec_ref(v_a_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtWithDoIdDecl_spec__0(size_t v_sz_1001_, size_t v_i_1002_, lean_object* v_bs_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_lt(v_i_1002_, v_sz_1001_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_bs_1003_);
lean_ctor_set(v___x_1007_, 1, v___y_1005_);
return v___x_1007_;
}
else
{
lean_object* v_v_1008_; lean_object* v___x_1009_; 
v_v_1008_ = lean_array_uget_borrowed(v_bs_1003_, v_i_1002_);
lean_inc(v_v_1008_);
v___x_1009_ = l_Lean_Fmt_fmt(v_v_1008_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v_bs_x27_1013_; size_t v___x_1014_; size_t v___x_1015_; lean_object* v___x_1016_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
v_a_1011_ = lean_ctor_get(v___x_1009_, 1);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1009_, 2);
v___x_1012_ = lean_unsigned_to_nat(0u);
v_bs_x27_1013_ = lean_array_uset(v_bs_1003_, v_i_1002_, v___x_1012_);
v___x_1014_ = ((size_t)1ULL);
v___x_1015_ = lean_usize_add(v_i_1002_, v___x_1014_);
v___x_1016_ = lean_array_uset(v_bs_x27_1013_, v_i_1002_, v_a_1010_);
v_i_1002_ = v___x_1015_;
v_bs_1003_ = v___x_1016_;
v___y_1005_ = v_a_1011_;
goto _start;
}
else
{
lean_object* v_a_1018_; lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v_bs_1003_);
v_a_1018_ = lean_ctor_get(v___x_1009_, 0);
v_a_1019_ = lean_ctor_get(v___x_1009_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1009_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_inc(v_a_1018_);
lean_dec(v___x_1009_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1018_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtWithDoIdDecl_spec__0___boxed(lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_bs_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
size_t v_sz_boxed_1032_; size_t v_i_boxed_1033_; lean_object* v_res_1034_; 
v_sz_boxed_1032_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1033_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtWithDoIdDecl_spec__0(v_sz_boxed_1032_, v_i_boxed_1033_, v_bs_1029_, v___y_1030_, v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithDoIdDecl(lean_object* v_kws_1052_, lean_object* v_cfg_x3f_1053_, lean_object* v_idDecl_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__1));
lean_inc(v_idDecl_1054_);
v___x_1058_ = l_Lean_Syntax_isOfKind(v_idDecl_1054_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_idDecl_1054_);
lean_dec(v_cfg_x3f_1053_);
lean_dec_ref(v_kws_1052_);
v___x_1059_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v_a_1056_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___x_1097_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v_typeAscriptionTk_x3f_1128_; lean_object* v_type_x3f_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1097_ = l_Lean_Syntax_getArg(v_idDecl_1054_, v___x_1061_);
v___x_1159_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__4));
lean_inc(v___x_1097_);
v___x_1160_ = l_Lean_Syntax_isOfKind(v___x_1097_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec(v___x_1097_);
lean_dec(v_idDecl_1054_);
lean_dec(v_cfg_x3f_1053_);
lean_dec_ref(v_kws_1052_);
v___x_1161_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v_a_1056_);
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = l_Lean_Syntax_getArg(v_idDecl_1054_, v___x_1163_);
v___x_1165_ = l_Lean_Syntax_isNone(v___x_1164_);
if (v___x_1165_ == 0)
{
uint8_t v___x_1166_; 
lean_inc(v___x_1164_);
v___x_1166_ = l_Lean_Syntax_matchesNull(v___x_1164_, v___x_1163_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v___x_1164_);
lean_dec(v___x_1097_);
lean_dec(v_idDecl_1054_);
lean_dec(v_cfg_x3f_1053_);
lean_dec_ref(v_kws_1052_);
v___x_1167_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v_a_1056_);
return v___x_1168_;
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = l_Lean_Syntax_getArg(v___x_1164_, v___x_1061_);
lean_dec(v___x_1164_);
v___x_1170_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__6));
lean_inc(v___x_1169_);
v___x_1171_ = l_Lean_Syntax_isOfKind(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec(v___x_1169_);
lean_dec(v___x_1097_);
lean_dec(v_idDecl_1054_);
lean_dec(v_cfg_x3f_1053_);
lean_dec_ref(v_kws_1052_);
v___x_1172_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_a_1056_);
return v___x_1173_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_1174_; lean_object* v_type_x3f_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_typeAscriptionTk_x3f_1174_ = l_Lean_Syntax_getArg(v___x_1169_, v___x_1061_);
v_type_x3f_1175_ = l_Lean_Syntax_getArg(v___x_1169_, v___x_1163_);
lean_dec(v___x_1169_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_typeAscriptionTk_x3f_1174_);
v___x_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_type_x3f_1175_);
v_typeAscriptionTk_x3f_1128_ = v___x_1176_;
v_type_x3f_1129_ = v___x_1177_;
v___y_1130_ = v_a_1055_;
v___y_1131_ = v_a_1056_;
goto v___jp_1127_;
}
}
}
else
{
lean_object* v___x_1178_; 
lean_dec(v___x_1164_);
v___x_1178_ = lean_box(0);
v_typeAscriptionTk_x3f_1128_ = v___x_1178_;
v_type_x3f_1129_ = v___x_1178_;
v___y_1130_ = v_a_1055_;
v___y_1131_ = v_a_1056_;
goto v___jp_1127_;
}
}
v___jp_1062_:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Fmt_fmt_x3f(v___y_1071_, v___y_1064_, v___y_1063_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v_a_1074_; lean_object* v___x_1075_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
v_a_1074_ = lean_ctor_get(v___x_1072_, 1);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1072_, 2);
v___x_1075_ = l_Lean_Fmt_fmt(v___y_1070_, v___y_1064_, v_a_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v_a_1077_; lean_object* v___x_1078_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
v_a_1077_ = lean_ctor_get(v___x_1075_, 1);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1075_, 2);
v___x_1078_ = l_Lean_Fmt_fmt(v___y_1067_, v___y_1064_, v_a_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1096_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_a_1080_ = lean_ctor_get(v___x_1078_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1082_ = v___x_1078_;
v_isShared_1083_ = v_isSharedCheck_1096_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1096_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1084_ = l_Lean_Fmt_Layouts_spacedAtomic(v___y_1066_);
lean_dec_ref(v___y_1066_);
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = lean_mk_empty_array_with_capacity(v___x_1085_);
v___x_1087_ = lean_array_push(v___x_1086_, v___y_1069_);
v___x_1088_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__2));
v___x_1089_ = l_Lean_Fmt_Layouts_localSignature(v___x_1087_, v___x_1088_, v___y_1068_, v_a_1073_);
lean_dec_ref(v___x_1087_);
v___x_1090_ = 0;
v___x_1091_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_1089_, v_a_1076_, v_a_1079_, v___x_1090_);
v___x_1092_ = l_Lean_Fmt_Layouts_letDecl(v___x_1084_, v___y_1065_, v___x_1091_, v___x_1090_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1092_);
v___x_1094_ = v___x_1082_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_a_1080_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_dec(v_a_1076_);
lean_dec(v_a_1073_);
lean_dec_ref(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v___x_1078_;
}
}
else
{
lean_dec(v_a_1073_);
lean_dec_ref(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v___x_1075_;
}
}
else
{
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v___x_1072_;
}
}
v___jp_1098_:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_Fmt_fmt_x3f(v___y_1106_, v___y_1101_, v___y_1102_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v_a_1109_; lean_object* v___x_1110_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
v_a_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1107_, 2);
v___x_1110_ = l_Lean_Fmt_fmt(v___x_1097_, v___y_1101_, v_a_1109_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v_a_1112_; lean_object* v___x_1113_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
v_a_1112_ = lean_ctor_get(v___x_1110_, 1);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1110_, 2);
v___x_1113_ = l_Lean_Fmt_fmt_x3f(v___y_1100_, v___y_1101_, v_a_1112_);
if (lean_obj_tag(v___x_1113_) == 0)
{
if (lean_obj_tag(v___y_1099_) == 0)
{
lean_object* v_a_1114_; lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
v_a_1115_ = lean_ctor_get(v___x_1113_, 1);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1113_, 2);
v___x_1116_ = lean_box(0);
v___y_1063_ = v_a_1115_;
v___y_1064_ = v___y_1101_;
v___y_1065_ = v_a_1108_;
v___y_1066_ = v___y_1104_;
v___y_1067_ = v___y_1103_;
v___y_1068_ = v_a_1114_;
v___y_1069_ = v_a_1111_;
v___y_1070_ = v___y_1105_;
v___y_1071_ = v___x_1116_;
goto v___jp_1062_;
}
else
{
lean_object* v_a_1117_; lean_object* v_a_1118_; lean_object* v_val_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_a_1117_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1117_);
v_a_1118_ = lean_ctor_get(v___x_1113_, 1);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1113_, 2);
v_val_1119_ = lean_ctor_get(v___y_1099_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___y_1099_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___y_1099_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_val_1119_);
lean_dec(v___y_1099_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_val_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v___y_1063_ = v_a_1118_;
v___y_1064_ = v___y_1101_;
v___y_1065_ = v_a_1108_;
v___y_1066_ = v___y_1104_;
v___y_1067_ = v___y_1103_;
v___y_1068_ = v_a_1117_;
v___y_1069_ = v_a_1111_;
v___y_1070_ = v___y_1105_;
v___y_1071_ = v___x_1124_;
goto v___jp_1062_;
}
}
}
}
else
{
lean_dec(v_a_1111_);
lean_dec(v_a_1108_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v___y_1099_);
return v___x_1113_;
}
}
else
{
lean_dec(v_a_1108_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
return v___x_1110_;
}
}
else
{
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec(v___x_1097_);
return v___x_1107_;
}
}
v___jp_1127_:
{
size_t v_sz_1132_; size_t v___x_1133_; lean_object* v___x_1134_; 
v_sz_1132_ = lean_array_size(v_kws_1052_);
v___x_1133_ = ((size_t)0ULL);
v___x_1134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtWithDoIdDecl_spec__0(v_sz_1132_, v___x_1133_, v_kws_1052_, v___y_1130_, v___y_1131_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v_a_1136_; lean_object* v___x_1137_; lean_object* v_leftArrowTk_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
v_a_1136_ = lean_ctor_get(v___x_1134_, 1);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1134_, 2);
v___x_1137_ = lean_unsigned_to_nat(2u);
v_leftArrowTk_1138_ = l_Lean_Syntax_getArg(v_idDecl_1054_, v___x_1137_);
v___x_1139_ = lean_unsigned_to_nat(3u);
v___x_1140_ = l_Lean_Syntax_getArg(v_idDecl_1054_, v___x_1139_);
lean_dec(v_idDecl_1054_);
if (lean_obj_tag(v_cfg_x3f_1053_) == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_box(0);
v___y_1099_ = v_type_x3f_1129_;
v___y_1100_ = v_typeAscriptionTk_x3f_1128_;
v___y_1101_ = v___y_1130_;
v___y_1102_ = v_a_1136_;
v___y_1103_ = v___x_1140_;
v___y_1104_ = v_a_1135_;
v___y_1105_ = v_leftArrowTk_1138_;
v___y_1106_ = v___x_1141_;
goto v___jp_1098_;
}
else
{
lean_object* v_val_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_val_1142_ = lean_ctor_get(v_cfg_x3f_1053_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_cfg_x3f_1053_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v_cfg_x3f_1053_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_val_1142_);
lean_dec(v_cfg_x3f_1053_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_val_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
v___y_1099_ = v_type_x3f_1129_;
v___y_1100_ = v_typeAscriptionTk_x3f_1128_;
v___y_1101_ = v___y_1130_;
v___y_1102_ = v_a_1136_;
v___y_1103_ = v___x_1140_;
v___y_1104_ = v_a_1135_;
v___y_1105_ = v_leftArrowTk_1138_;
v___y_1106_ = v___x_1147_;
goto v___jp_1098_;
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_type_x3f_1129_);
lean_dec(v_typeAscriptionTk_x3f_1128_);
lean_dec(v___x_1097_);
lean_dec(v_idDecl_1054_);
lean_dec(v_cfg_x3f_1053_);
v_a_1150_ = lean_ctor_get(v___x_1134_, 0);
v_a_1151_ = lean_ctor_get(v___x_1134_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1134_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_inc(v_a_1150_);
lean_dec(v___x_1134_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1150_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithDoIdDecl___boxed(lean_object* v_kws_1179_, lean_object* v_cfg_x3f_1180_, lean_object* v_idDecl_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Fmt_fmtWithDoIdDecl(v_kws_1179_, v_cfg_x3f_1180_, v_idDecl_1181_, v_a_1182_, v_a_1183_);
lean_dec_ref(v_a_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithDoPatDecl(lean_object* v_kws_1191_, lean_object* v_cfg_x3f_1192_, lean_object* v_patDecl_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoPatDecl___closed__1));
lean_inc(v_patDecl_1193_);
v___x_1224_ = l_Lean_Syntax_isOfKind(v_patDecl_1193_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec(v_patDecl_1193_);
lean_dec(v_cfg_x3f_1192_);
lean_dec_ref(v_kws_1191_);
v___x_1225_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_a_1195_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; lean_object* v_pat_1228_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___x_1326_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v_pipeTk_x3f_1352_; lean_object* v_elseSeq_x3f_1353_; lean_object* v_body_x3f_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v_body_x3f_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v_typeAscriptionTk_x3f_1376_; lean_object* v_type_x3f_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
v_pat_1228_ = l_Lean_Syntax_getArg(v_patDecl_1193_, v___x_1227_);
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1408_ = l_Lean_Syntax_getArg(v_patDecl_1193_, v___x_1326_);
v___x_1409_ = l_Lean_Syntax_isNone(v___x_1408_);
if (v___x_1409_ == 0)
{
uint8_t v___x_1410_; 
lean_inc(v___x_1408_);
v___x_1410_ = l_Lean_Syntax_matchesNull(v___x_1408_, v___x_1326_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec(v___x_1408_);
lean_dec(v_pat_1228_);
lean_dec(v_patDecl_1193_);
lean_dec(v_cfg_x3f_1192_);
lean_dec_ref(v_kws_1191_);
v___x_1411_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v_a_1195_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = l_Lean_Syntax_getArg(v___x_1408_, v___x_1227_);
lean_dec(v___x_1408_);
v___x_1414_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__6));
lean_inc(v___x_1413_);
v___x_1415_ = l_Lean_Syntax_isOfKind(v___x_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec(v___x_1413_);
lean_dec(v_pat_1228_);
lean_dec(v_patDecl_1193_);
lean_dec(v_cfg_x3f_1192_);
lean_dec_ref(v_kws_1191_);
v___x_1416_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v_a_1195_);
return v___x_1417_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_1418_; lean_object* v_type_x3f_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_typeAscriptionTk_x3f_1418_ = l_Lean_Syntax_getArg(v___x_1413_, v___x_1227_);
v_type_x3f_1419_ = l_Lean_Syntax_getArg(v___x_1413_, v___x_1326_);
lean_dec(v___x_1413_);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_typeAscriptionTk_x3f_1418_);
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_type_x3f_1419_);
v_typeAscriptionTk_x3f_1376_ = v___x_1420_;
v_type_x3f_1377_ = v___x_1421_;
v___y_1378_ = v_a_1194_;
v___y_1379_ = v_a_1195_;
goto v___jp_1375_;
}
}
}
else
{
lean_object* v___x_1422_; 
lean_dec(v___x_1408_);
v___x_1422_ = lean_box(0);
v_typeAscriptionTk_x3f_1376_ = v___x_1422_;
v_type_x3f_1377_ = v___x_1422_;
v___y_1378_ = v_a_1194_;
v___y_1379_ = v_a_1195_;
goto v___jp_1375_;
}
v___jp_1229_:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Fmt_fmt_x3f(v___y_1241_, v___y_1234_, v___y_1240_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v_a_1244_; lean_object* v___x_1245_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
v_a_1244_ = lean_ctor_get(v___x_1242_, 1);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1242_, 2);
v___x_1245_ = l_Lean_Fmt_fmtPatSignature(v_pat_1228_, v___y_1236_, v___y_1235_, v___y_1234_, v_a_1244_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v_a_1247_; lean_object* v___x_1248_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
v_a_1247_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1245_, 2);
v___x_1248_ = l_Lean_Fmt_fmt(v___y_1232_, v___y_1234_, v_a_1247_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
v_a_1250_ = lean_ctor_get(v___x_1248_, 1);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1248_, 2);
v___x_1251_ = l_Lean_Fmt_fmt(v___y_1239_, v___y_1234_, v_a_1250_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v_a_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
v_a_1253_ = lean_ctor_get(v___x_1251_, 1);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1251_, 2);
v___x_1254_ = l_Lean_Fmt_Layouts_spacedAtomic(v___y_1233_);
lean_dec_ref(v___y_1233_);
v___x_1255_ = 0;
v___x_1256_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1246_, v_a_1249_, v_a_1252_, v___x_1255_);
v___x_1257_ = l_Lean_Fmt_Layouts_letDecl(v___x_1254_, v_a_1243_, v___x_1256_, v___x_1255_);
if (lean_obj_tag(v___y_1238_) == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_box(0);
v___y_1206_ = v___y_1231_;
v___y_1207_ = v___y_1230_;
v___y_1208_ = v___y_1234_;
v___y_1209_ = v_a_1253_;
v___y_1210_ = v___y_1237_;
v___y_1211_ = v___x_1257_;
v___y_1212_ = v___x_1258_;
goto v___jp_1205_;
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_val_1259_ = lean_ctor_get(v___y_1238_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___y_1238_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___y_1238_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_val_1259_);
lean_dec(v___y_1238_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_val_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
v___y_1206_ = v___y_1231_;
v___y_1207_ = v___y_1230_;
v___y_1208_ = v___y_1234_;
v___y_1209_ = v_a_1253_;
v___y_1210_ = v___y_1237_;
v___y_1211_ = v___x_1257_;
v___y_1212_ = v___x_1264_;
goto v___jp_1205_;
}
}
}
}
else
{
lean_dec(v_a_1249_);
lean_dec(v_a_1246_);
lean_dec(v_a_1243_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
return v___x_1251_;
}
}
else
{
lean_dec(v_a_1246_);
lean_dec(v_a_1243_);
lean_dec(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
return v___x_1248_;
}
}
else
{
lean_dec(v_a_1243_);
lean_dec(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
return v___x_1245_;
}
}
else
{
lean_dec(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec(v_pat_1228_);
return v___x_1242_;
}
}
v___jp_1267_:
{
size_t v_sz_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v_sz_1280_ = lean_array_size(v_kws_1191_);
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtWithDoIdDecl_spec__0(v_sz_1280_, v___x_1281_, v_kws_1191_, v___y_1272_, v___y_1276_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v_declComponents_1289_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
v_a_1284_ = lean_ctor_get(v___x_1282_, 1);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1282_, 2);
v___x_1285_ = l_Array_append___redArg(v___y_1271_, v___y_1279_);
lean_dec_ref(v___y_1279_);
v___x_1286_ = lean_mk_empty_array_with_capacity(v___y_1273_);
lean_inc(v___y_1270_);
v___x_1287_ = lean_array_push(v___x_1286_, v___y_1270_);
lean_inc(v___y_1278_);
v___x_1288_ = lean_array_push(v___x_1287_, v___y_1278_);
v_declComponents_1289_ = l_Array_append___redArg(v___x_1285_, v___x_1288_);
lean_dec_ref(v___x_1288_);
if (lean_obj_tag(v_cfg_x3f_1192_) == 0)
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_box(0);
v___y_1230_ = v___y_1269_;
v___y_1231_ = v___y_1268_;
v___y_1232_ = v___y_1270_;
v___y_1233_ = v_a_1283_;
v___y_1234_ = v___y_1272_;
v___y_1235_ = v___y_1274_;
v___y_1236_ = v___y_1275_;
v___y_1237_ = v_declComponents_1289_;
v___y_1238_ = v___y_1277_;
v___y_1239_ = v___y_1278_;
v___y_1240_ = v_a_1284_;
v___y_1241_ = v___x_1290_;
goto v___jp_1229_;
}
else
{
lean_object* v_val_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_val_1291_ = lean_ctor_get(v_cfg_x3f_1192_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_cfg_x3f_1192_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v_cfg_x3f_1192_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_val_1291_);
lean_dec(v_cfg_x3f_1192_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_val_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
v___y_1230_ = v___y_1269_;
v___y_1231_ = v___y_1268_;
v___y_1232_ = v___y_1270_;
v___y_1233_ = v_a_1283_;
v___y_1234_ = v___y_1272_;
v___y_1235_ = v___y_1274_;
v___y_1236_ = v___y_1275_;
v___y_1237_ = v_declComponents_1289_;
v___y_1238_ = v___y_1277_;
v___y_1239_ = v___y_1278_;
v___y_1240_ = v_a_1284_;
v___y_1241_ = v___x_1296_;
goto v___jp_1229_;
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v_pat_1228_);
lean_dec(v_cfg_x3f_1192_);
v_a_1299_ = lean_ctor_get(v___x_1282_, 0);
v_a_1300_ = lean_ctor_get(v___x_1282_, 1);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1282_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_inc(v_a_1299_);
lean_dec(v___x_1282_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1299_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
v___jp_1308_:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Array_append___redArg(v___y_1318_, v___y_1321_);
lean_dec_ref(v___y_1321_);
if (lean_obj_tag(v___y_1315_) == 0)
{
lean_object* v___x_1323_; 
lean_dec_ref(v___y_1312_);
v___x_1323_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElseLike___closed__0));
v___y_1268_ = v___y_1310_;
v___y_1269_ = v___y_1309_;
v___y_1270_ = v___y_1311_;
v___y_1271_ = v___x_1322_;
v___y_1272_ = v___y_1313_;
v___y_1273_ = v___y_1314_;
v___y_1274_ = v___y_1315_;
v___y_1275_ = v___y_1317_;
v___y_1276_ = v___y_1316_;
v___y_1277_ = v___y_1319_;
v___y_1278_ = v___y_1320_;
v___y_1279_ = v___x_1323_;
goto v___jp_1267_;
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1325_; 
v_val_1324_ = lean_ctor_get(v___y_1315_, 0);
lean_inc(v_val_1324_);
v___x_1325_ = lean_array_push(v___y_1312_, v_val_1324_);
v___y_1268_ = v___y_1310_;
v___y_1269_ = v___y_1309_;
v___y_1270_ = v___y_1311_;
v___y_1271_ = v___x_1322_;
v___y_1272_ = v___y_1313_;
v___y_1273_ = v___y_1314_;
v___y_1274_ = v___y_1315_;
v___y_1275_ = v___y_1317_;
v___y_1276_ = v___y_1316_;
v___y_1277_ = v___y_1319_;
v___y_1278_ = v___y_1320_;
v___y_1279_ = v___x_1325_;
goto v___jp_1267_;
}
}
v___jp_1327_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_inc_ref(v_kws_1191_);
v___x_1339_ = l_Array_append___redArg(v_kws_1191_, v___y_1338_);
lean_dec_ref(v___y_1338_);
v___x_1340_ = lean_mk_empty_array_with_capacity(v___x_1326_);
lean_inc(v_pat_1228_);
lean_inc_ref(v___x_1340_);
v___x_1341_ = lean_array_push(v___x_1340_, v_pat_1228_);
v___x_1342_ = l_Array_append___redArg(v___x_1339_, v___x_1341_);
lean_dec_ref(v___x_1341_);
if (lean_obj_tag(v___y_1334_) == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElseLike___closed__0));
v___y_1309_ = v___y_1329_;
v___y_1310_ = v___y_1328_;
v___y_1311_ = v___y_1330_;
v___y_1312_ = v___x_1340_;
v___y_1313_ = v___y_1331_;
v___y_1314_ = v___y_1332_;
v___y_1315_ = v___y_1333_;
v___y_1316_ = v___y_1335_;
v___y_1317_ = v___y_1334_;
v___y_1318_ = v___x_1342_;
v___y_1319_ = v___y_1336_;
v___y_1320_ = v___y_1337_;
v___y_1321_ = v___x_1343_;
goto v___jp_1308_;
}
else
{
lean_object* v_val_1344_; lean_object* v___x_1345_; 
v_val_1344_ = lean_ctor_get(v___y_1334_, 0);
lean_inc(v_val_1344_);
lean_inc_ref(v___x_1340_);
v___x_1345_ = lean_array_push(v___x_1340_, v_val_1344_);
v___y_1309_ = v___y_1329_;
v___y_1310_ = v___y_1328_;
v___y_1311_ = v___y_1330_;
v___y_1312_ = v___x_1340_;
v___y_1313_ = v___y_1331_;
v___y_1314_ = v___y_1332_;
v___y_1315_ = v___y_1333_;
v___y_1316_ = v___y_1335_;
v___y_1317_ = v___y_1334_;
v___y_1318_ = v___x_1342_;
v___y_1319_ = v___y_1336_;
v___y_1320_ = v___y_1337_;
v___y_1321_ = v___x_1345_;
goto v___jp_1308_;
}
}
v___jp_1346_:
{
if (lean_obj_tag(v_cfg_x3f_1192_) == 0)
{
lean_object* v___x_1357_; 
v___x_1357_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElseLike___closed__0));
v___y_1328_ = v_body_x3f_1354_;
v___y_1329_ = v_pipeTk_x3f_1352_;
v___y_1330_ = v___y_1347_;
v___y_1331_ = v___y_1355_;
v___y_1332_ = v___y_1348_;
v___y_1333_ = v___y_1349_;
v___y_1334_ = v___y_1350_;
v___y_1335_ = v___y_1356_;
v___y_1336_ = v_elseSeq_x3f_1353_;
v___y_1337_ = v___y_1351_;
v___y_1338_ = v___x_1357_;
goto v___jp_1327_;
}
else
{
lean_object* v_val_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_val_1358_ = lean_ctor_get(v_cfg_x3f_1192_, 0);
v___x_1359_ = lean_mk_empty_array_with_capacity(v___x_1326_);
lean_inc(v_val_1358_);
v___x_1360_ = lean_array_push(v___x_1359_, v_val_1358_);
v___y_1328_ = v_body_x3f_1354_;
v___y_1329_ = v_pipeTk_x3f_1352_;
v___y_1330_ = v___y_1347_;
v___y_1331_ = v___y_1355_;
v___y_1332_ = v___y_1348_;
v___y_1333_ = v___y_1349_;
v___y_1334_ = v___y_1350_;
v___y_1335_ = v___y_1356_;
v___y_1336_ = v_elseSeq_x3f_1353_;
v___y_1337_ = v___y_1351_;
v___y_1338_ = v___x_1360_;
goto v___jp_1327_;
}
}
v___jp_1361_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___y_1364_);
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___y_1368_);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_body_x3f_1369_);
v___y_1347_ = v___y_1362_;
v___y_1348_ = v___y_1363_;
v___y_1349_ = v___y_1365_;
v___y_1350_ = v___y_1366_;
v___y_1351_ = v___y_1367_;
v_pipeTk_x3f_1352_ = v___x_1372_;
v_elseSeq_x3f_1353_ = v___x_1373_;
v_body_x3f_1354_ = v___x_1374_;
v___y_1355_ = v___y_1370_;
v___y_1356_ = v___y_1371_;
goto v___jp_1346_;
}
v___jp_1375_:
{
lean_object* v___x_1380_; lean_object* v_leftArrowTk_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1380_ = lean_unsigned_to_nat(2u);
v_leftArrowTk_1381_ = l_Lean_Syntax_getArg(v_patDecl_1193_, v___x_1380_);
v___x_1382_ = lean_unsigned_to_nat(3u);
v___x_1383_ = l_Lean_Syntax_getArg(v_patDecl_1193_, v___x_1382_);
v___x_1384_ = lean_unsigned_to_nat(4u);
v___x_1385_ = l_Lean_Syntax_getArg(v_patDecl_1193_, v___x_1384_);
lean_dec(v_patDecl_1193_);
v___x_1386_ = l_Lean_Syntax_isNone(v___x_1385_);
if (v___x_1386_ == 0)
{
uint8_t v___x_1387_; 
lean_inc(v___x_1385_);
v___x_1387_ = l_Lean_Syntax_matchesNull(v___x_1385_, v___x_1382_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec(v___x_1385_);
lean_dec(v___x_1383_);
lean_dec(v_leftArrowTk_1381_);
lean_dec(v_type_x3f_1377_);
lean_dec(v_typeAscriptionTk_x3f_1376_);
lean_dec(v_pat_1228_);
lean_dec(v_cfg_x3f_1192_);
lean_dec_ref(v_kws_1191_);
v___x_1388_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v___y_1379_);
return v___x_1389_;
}
else
{
lean_object* v_elseSeq_x3f_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_elseSeq_x3f_1390_ = l_Lean_Syntax_getArg(v___x_1385_, v___x_1326_);
v___x_1391_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqIndent___closed__1));
lean_inc(v_elseSeq_x3f_1390_);
v___x_1392_ = l_Lean_Syntax_isOfKind(v_elseSeq_x3f_1390_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec(v_elseSeq_x3f_1390_);
lean_dec(v___x_1385_);
lean_dec(v___x_1383_);
lean_dec(v_leftArrowTk_1381_);
lean_dec(v_type_x3f_1377_);
lean_dec(v_typeAscriptionTk_x3f_1376_);
lean_dec(v_pat_1228_);
lean_dec(v_cfg_x3f_1192_);
lean_dec_ref(v_kws_1191_);
v___x_1393_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
lean_ctor_set(v___x_1394_, 1, v___y_1379_);
return v___x_1394_;
}
else
{
lean_object* v_pipeTk_x3f_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_pipeTk_x3f_1395_ = l_Lean_Syntax_getArg(v___x_1385_, v___x_1227_);
v___x_1396_ = l_Lean_Syntax_getArg(v___x_1385_, v___x_1380_);
lean_dec(v___x_1385_);
v___x_1397_ = l_Lean_Syntax_isNone(v___x_1396_);
if (v___x_1397_ == 0)
{
uint8_t v___x_1398_; 
lean_inc(v___x_1396_);
v___x_1398_ = l_Lean_Syntax_matchesNull(v___x_1396_, v___x_1326_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec(v___x_1396_);
lean_dec(v_pipeTk_x3f_1395_);
lean_dec(v_elseSeq_x3f_1390_);
lean_dec(v___x_1383_);
lean_dec(v_leftArrowTk_1381_);
lean_dec(v_type_x3f_1377_);
lean_dec(v_typeAscriptionTk_x3f_1376_);
lean_dec(v_pat_1228_);
lean_dec(v_cfg_x3f_1192_);
lean_dec_ref(v_kws_1191_);
v___x_1399_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___y_1379_);
return v___x_1400_;
}
else
{
lean_object* v_body_x3f_1401_; uint8_t v___x_1402_; 
v_body_x3f_1401_ = l_Lean_Syntax_getArg(v___x_1396_, v___x_1227_);
lean_dec(v___x_1396_);
lean_inc(v_body_x3f_1401_);
v___x_1402_ = l_Lean_Syntax_isOfKind(v_body_x3f_1401_, v___x_1391_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v_body_x3f_1401_);
lean_dec(v_pipeTk_x3f_1395_);
lean_dec(v_elseSeq_x3f_1390_);
lean_dec(v___x_1383_);
lean_dec(v_leftArrowTk_1381_);
lean_dec(v_type_x3f_1377_);
lean_dec(v_typeAscriptionTk_x3f_1376_);
lean_dec(v_pat_1228_);
lean_dec(v_cfg_x3f_1192_);
lean_dec_ref(v_kws_1191_);
v___x_1403_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
lean_ctor_set(v___x_1404_, 1, v___y_1379_);
return v___x_1404_;
}
else
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v_body_x3f_1401_);
v___y_1362_ = v_leftArrowTk_1381_;
v___y_1363_ = v___x_1380_;
v___y_1364_ = v_pipeTk_x3f_1395_;
v___y_1365_ = v_type_x3f_1377_;
v___y_1366_ = v_typeAscriptionTk_x3f_1376_;
v___y_1367_ = v___x_1383_;
v___y_1368_ = v_elseSeq_x3f_1390_;
v_body_x3f_1369_ = v___x_1405_;
v___y_1370_ = v___y_1378_;
v___y_1371_ = v___y_1379_;
goto v___jp_1361_;
}
}
}
else
{
lean_object* v___x_1406_; 
lean_dec(v___x_1396_);
v___x_1406_ = lean_box(0);
v___y_1362_ = v_leftArrowTk_1381_;
v___y_1363_ = v___x_1380_;
v___y_1364_ = v_pipeTk_x3f_1395_;
v___y_1365_ = v_type_x3f_1377_;
v___y_1366_ = v_typeAscriptionTk_x3f_1376_;
v___y_1367_ = v___x_1383_;
v___y_1368_ = v_elseSeq_x3f_1390_;
v_body_x3f_1369_ = v___x_1406_;
v___y_1370_ = v___y_1378_;
v___y_1371_ = v___y_1379_;
goto v___jp_1361_;
}
}
}
}
else
{
lean_object* v___x_1407_; 
lean_dec(v___x_1385_);
v___x_1407_ = lean_box(0);
v___y_1347_ = v_leftArrowTk_1381_;
v___y_1348_ = v___x_1380_;
v___y_1349_ = v_type_x3f_1377_;
v___y_1350_ = v_typeAscriptionTk_x3f_1376_;
v___y_1351_ = v___x_1383_;
v_pipeTk_x3f_1352_ = v___x_1407_;
v_elseSeq_x3f_1353_ = v___x_1407_;
v_body_x3f_1354_ = v___x_1407_;
v___y_1355_ = v___y_1378_;
v___y_1356_ = v___y_1379_;
goto v___jp_1346_;
}
}
}
v___jp_1196_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_box(0);
v___x_1204_ = l_Lean_Fmt_fmtDoLetElseLike(v___y_1202_, v___y_1201_, v___y_1197_, v___y_1200_, v___x_1203_, v___y_1198_, v___y_1199_);
return v___x_1204_;
}
v___jp_1205_:
{
if (lean_obj_tag(v___y_1206_) == 0)
{
v___y_1197_ = v___y_1207_;
v___y_1198_ = v___y_1208_;
v___y_1199_ = v___y_1209_;
v___y_1200_ = v___y_1212_;
v___y_1201_ = v___y_1210_;
v___y_1202_ = v___y_1211_;
goto v___jp_1196_;
}
else
{
lean_object* v_val_1213_; 
v_val_1213_ = lean_ctor_get(v___y_1206_, 0);
lean_inc(v_val_1213_);
lean_dec_ref_known(v___y_1206_, 1);
if (lean_obj_tag(v_val_1213_) == 0)
{
v___y_1197_ = v___y_1207_;
v___y_1198_ = v___y_1208_;
v___y_1199_ = v___y_1209_;
v___y_1200_ = v___y_1212_;
v___y_1201_ = v___y_1210_;
v___y_1202_ = v___y_1211_;
goto v___jp_1196_;
}
else
{
lean_object* v_val_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
v_val_1214_ = lean_ctor_get(v_val_1213_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_val_1213_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1216_ = v_val_1213_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_val_1214_);
lean_dec(v_val_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_val_1214_);
v___x_1219_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_Fmt_fmtDoLetElseLike(v___y_1211_, v___y_1210_, v___y_1207_, v___y_1212_, v___x_1219_, v___y_1208_, v___y_1209_);
return v___x_1220_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithDoPatDecl___boxed(lean_object* v_kws_1423_, lean_object* v_cfg_x3f_1424_, lean_object* v_patDecl_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_Fmt_fmtWithDoPatDecl(v_kws_1423_, v_cfg_x3f_1424_, v_patDecl_1425_, v_a_1426_, v_a_1427_);
lean_dec_ref(v_a_1426_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetArrow(lean_object* v_x_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1458_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetArrow___closed__1));
lean_inc(v_x_1435_);
v___x_1459_ = l_Lean_Syntax_isOfKind(v_x_1435_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_dec(v_x_1435_);
v___x_1460_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v_a_1437_);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; lean_object* v_letTk_1463_; lean_object* v_mutTk_x3f_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1462_ = lean_unsigned_to_nat(0u);
v_letTk_1463_ = l_Lean_Syntax_getArg(v_x_1435_, v___x_1462_);
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = l_Lean_Syntax_getArg(v_x_1435_, v___x_1494_);
v___x_1496_ = l_Lean_Syntax_isNone(v___x_1495_);
if (v___x_1496_ == 0)
{
uint8_t v___x_1497_; 
lean_inc(v___x_1495_);
v___x_1497_ = l_Lean_Syntax_matchesNull(v___x_1495_, v___x_1494_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec(v___x_1495_);
lean_dec(v_letTk_1463_);
lean_dec(v_x_1435_);
v___x_1498_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v_a_1437_);
return v___x_1499_;
}
else
{
lean_object* v_mutTk_x3f_1500_; lean_object* v___x_1501_; 
v_mutTk_x3f_1500_ = l_Lean_Syntax_getArg(v___x_1495_, v___x_1462_);
lean_dec(v___x_1495_);
v___x_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_mutTk_x3f_1500_);
v_mutTk_x3f_1465_ = v___x_1501_;
v___y_1466_ = v_a_1436_;
v___y_1467_ = v_a_1437_;
goto v___jp_1464_;
}
}
else
{
lean_object* v___x_1502_; 
lean_dec(v___x_1495_);
v___x_1502_ = lean_box(0);
v_mutTk_x3f_1465_ = v___x_1502_;
v___y_1466_ = v_a_1436_;
v___y_1467_ = v_a_1437_;
goto v___jp_1464_;
}
v___jp_1464_:
{
lean_object* v___x_1468_; lean_object* v_cfg_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1468_ = lean_unsigned_to_nat(2u);
v_cfg_1469_ = l_Lean_Syntax_getArg(v_x_1435_, v___x_1468_);
v___x_1470_ = ((lean_object*)(l_Lean_Fmt_fmtDoLet___closed__3));
lean_inc(v_cfg_1469_);
v___x_1471_ = l_Lean_Syntax_isOfKind(v_cfg_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_cfg_1469_);
lean_dec(v_mutTk_x3f_1465_);
lean_dec(v_letTk_1463_);
lean_dec(v_x_1435_);
v___x_1472_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___y_1467_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; lean_object* v_decl_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1474_ = lean_unsigned_to_nat(3u);
v_decl_1475_ = l_Lean_Syntax_getArg(v_x_1435_, v___x_1474_);
lean_dec(v_x_1435_);
v___x_1476_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__1));
lean_inc(v_decl_1475_);
v___x_1477_ = l_Lean_Syntax_isOfKind(v_decl_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoPatDecl___closed__1));
lean_inc(v_decl_1475_);
v___x_1479_ = l_Lean_Syntax_isOfKind(v_decl_1475_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec(v_decl_1475_);
lean_dec(v_cfg_1469_);
lean_dec(v_mutTk_x3f_1465_);
lean_dec(v_letTk_1463_);
v___x_1480_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___y_1467_);
return v___x_1481_;
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_unsigned_to_nat(1u);
v___x_1483_ = lean_mk_empty_array_with_capacity(v___x_1482_);
lean_inc_ref(v___x_1483_);
v___x_1484_ = lean_array_push(v___x_1483_, v_letTk_1463_);
if (lean_obj_tag(v_mutTk_x3f_1465_) == 0)
{
lean_object* v___x_1485_; 
lean_dec_ref(v___x_1483_);
v___x_1485_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElseLike___closed__0));
v___y_1439_ = v___y_1467_;
v___y_1440_ = v_decl_1475_;
v___y_1441_ = v___x_1484_;
v___y_1442_ = v___y_1466_;
v___y_1443_ = v_cfg_1469_;
v___y_1444_ = v___x_1485_;
goto v___jp_1438_;
}
else
{
lean_object* v_val_1486_; lean_object* v___x_1487_; 
v_val_1486_ = lean_ctor_get(v_mutTk_x3f_1465_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v_mutTk_x3f_1465_, 1);
v___x_1487_ = lean_array_push(v___x_1483_, v_val_1486_);
v___y_1439_ = v___y_1467_;
v___y_1440_ = v_decl_1475_;
v___y_1441_ = v___x_1484_;
v___y_1442_ = v___y_1466_;
v___y_1443_ = v_cfg_1469_;
v___y_1444_ = v___x_1487_;
goto v___jp_1438_;
}
}
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = lean_unsigned_to_nat(1u);
v___x_1489_ = lean_mk_empty_array_with_capacity(v___x_1488_);
lean_inc_ref(v___x_1489_);
v___x_1490_ = lean_array_push(v___x_1489_, v_letTk_1463_);
if (lean_obj_tag(v_mutTk_x3f_1465_) == 0)
{
lean_object* v___x_1491_; 
lean_dec_ref(v___x_1489_);
v___x_1491_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElseLike___closed__0));
v___y_1449_ = v___y_1467_;
v___y_1450_ = v_decl_1475_;
v___y_1451_ = v___y_1466_;
v___y_1452_ = v_cfg_1469_;
v___y_1453_ = v___x_1490_;
v___y_1454_ = v___x_1491_;
goto v___jp_1448_;
}
else
{
lean_object* v_val_1492_; lean_object* v___x_1493_; 
v_val_1492_ = lean_ctor_get(v_mutTk_x3f_1465_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v_mutTk_x3f_1465_, 1);
v___x_1493_ = lean_array_push(v___x_1489_, v_val_1492_);
v___y_1449_ = v___y_1467_;
v___y_1450_ = v_decl_1475_;
v___y_1451_ = v___y_1466_;
v___y_1452_ = v_cfg_1469_;
v___y_1453_ = v___x_1490_;
v___y_1454_ = v___x_1493_;
goto v___jp_1448_;
}
}
}
}
}
v___jp_1438_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = l_Array_append___redArg(v___y_1441_, v___y_1444_);
lean_dec_ref(v___y_1444_);
v___x_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___y_1443_);
v___x_1447_ = l_Lean_Fmt_fmtWithDoPatDecl(v___x_1445_, v___x_1446_, v___y_1440_, v___y_1442_, v___y_1439_);
return v___x_1447_;
}
v___jp_1448_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = l_Array_append___redArg(v___y_1453_, v___y_1454_);
lean_dec_ref(v___y_1454_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___y_1452_);
v___x_1457_ = l_Lean_Fmt_fmtWithDoIdDecl(v___x_1455_, v___x_1456_, v___y_1450_, v___y_1451_, v___y_1449_);
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetArrow___boxed(lean_object* v_x_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Fmt_fmtDoLetArrow(v_x_1503_, v_a_1504_, v_a_1505_);
lean_dec_ref(v_a_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1(){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1513_ = l_Lean_Fmt_fmtAttribute;
v___x_1514_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetArrow___closed__1));
v___x_1515_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___closed__1));
v___x_1516_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoLetArrow___boxed), 3, 0);
v___x_1517_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1513_, v___x_1514_, v___x_1515_, v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1___boxed(lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1();
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetElse(lean_object* v_x_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElse___closed__1));
lean_inc(v_x_1526_);
v___x_1530_ = l_Lean_Syntax_isOfKind(v_x_1526_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_x_1526_);
v___x_1531_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v_a_1528_);
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; lean_object* v_letTk_1534_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___x_1595_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v_body_x3f_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v_mutTk_x3f_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1533_ = lean_unsigned_to_nat(0u);
v_letTk_1534_ = l_Lean_Syntax_getArg(v_x_1526_, v___x_1533_);
v___x_1595_ = lean_unsigned_to_nat(1u);
v___x_1650_ = l_Lean_Syntax_getArg(v_x_1526_, v___x_1595_);
v___x_1651_ = l_Lean_Syntax_isNone(v___x_1650_);
if (v___x_1651_ == 0)
{
uint8_t v___x_1652_; 
lean_inc(v___x_1650_);
v___x_1652_ = l_Lean_Syntax_matchesNull(v___x_1650_, v___x_1595_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec(v___x_1650_);
lean_dec(v_letTk_1534_);
lean_dec(v_x_1526_);
v___x_1653_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_a_1528_);
return v___x_1654_;
}
else
{
lean_object* v_mutTk_x3f_1655_; lean_object* v___x_1656_; 
v_mutTk_x3f_1655_ = l_Lean_Syntax_getArg(v___x_1650_, v___x_1533_);
lean_dec(v___x_1650_);
v___x_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_mutTk_x3f_1655_);
v_mutTk_x3f_1615_ = v___x_1656_;
v___y_1616_ = v_a_1527_;
v___y_1617_ = v_a_1528_;
goto v___jp_1614_;
}
}
else
{
lean_object* v___x_1657_; 
lean_dec(v___x_1650_);
v___x_1657_ = lean_box(0);
v_mutTk_x3f_1615_ = v___x_1657_;
v___y_1616_ = v_a_1527_;
v___y_1617_ = v_a_1528_;
goto v___jp_1614_;
}
v___jp_1535_:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Fmt_fmt(v_letTk_1534_, v___y_1539_, v___y_1546_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
v_a_1552_ = lean_ctor_get(v___x_1550_, 1);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1550_, 2);
v___x_1553_ = l_Lean_Fmt_fmt_x3f(v___y_1536_, v___y_1539_, v_a_1552_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
v_a_1555_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1553_, 2);
v___x_1556_ = lean_mk_empty_array_with_capacity(v___y_1543_);
lean_inc(v___y_1547_);
v___x_1557_ = lean_array_push(v___x_1556_, v___y_1547_);
v___x_1558_ = l_Lean_Fmt_fmt(v___y_1547_, v___y_1539_, v_a_1555_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v_a_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
v_a_1560_ = lean_ctor_get(v___x_1558_, 1);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1558_, 2);
lean_inc(v___y_1542_);
v___x_1561_ = lean_array_push(v___x_1557_, v___y_1542_);
v___x_1562_ = l_Lean_Fmt_fmt(v___y_1542_, v___y_1539_, v_a_1560_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v_a_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
v_a_1564_ = lean_ctor_get(v___x_1562_, 1);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1562_, 2);
lean_inc(v___y_1540_);
v___x_1565_ = lean_array_push(v___x_1561_, v___y_1540_);
v___x_1566_ = l_Lean_Fmt_fmt(v___y_1540_, v___y_1539_, v_a_1564_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v_a_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
v_a_1568_ = lean_ctor_get(v___x_1566_, 1);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1566_, 2);
lean_inc(v___y_1541_);
v___x_1569_ = lean_array_push(v___x_1565_, v___y_1541_);
v___x_1570_ = l_Lean_Fmt_fmt(v___y_1541_, v___y_1539_, v_a_1568_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v_a_1572_; lean_object* v___x_1573_; lean_object* v_declComponents_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
v_a_1572_ = lean_ctor_get(v___x_1570_, 1);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1570_, 2);
v___x_1573_ = l_Array_append___redArg(v___y_1544_, v___y_1549_);
lean_dec_ref(v___y_1549_);
v_declComponents_1574_ = l_Array_append___redArg(v___x_1573_, v___x_1569_);
lean_dec_ref(v___x_1569_);
v___x_1575_ = lean_mk_empty_array_with_capacity(v___y_1538_);
v___x_1576_ = lean_array_push(v___x_1575_, v_a_1551_);
v___x_1577_ = lean_array_push(v___x_1576_, v_a_1554_);
v___x_1578_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1577_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = 0;
v___x_1580_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1563_, v_a_1567_, v_a_1571_, v___x_1579_);
v___x_1581_ = l_Lean_Fmt_Layouts_letDecl(v___x_1578_, v_a_1559_, v___x_1580_, v___x_1579_);
v___x_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___y_1537_);
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___y_1548_);
if (lean_obj_tag(v___y_1545_) == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_box(0);
v___x_1585_ = l_Lean_Fmt_fmtDoLetElseLike(v___x_1581_, v_declComponents_1574_, v___x_1582_, v___x_1583_, v___x_1584_, v___y_1539_, v_a_1572_);
return v___x_1585_;
}
else
{
lean_object* v_val_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1594_; 
v_val_1586_ = lean_ctor_get(v___y_1545_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___y_1545_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1588_ = v___y_1545_;
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_val_1586_);
lean_dec(v___y_1545_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_val_1586_);
v___x_1591_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_Fmt_fmtDoLetElseLike(v___x_1581_, v_declComponents_1574_, v___x_1582_, v___x_1583_, v___x_1591_, v___y_1539_, v_a_1572_);
return v___x_1592_;
}
}
}
}
else
{
lean_dec_ref(v___x_1569_);
lean_dec(v_a_1567_);
lean_dec(v_a_1563_);
lean_dec(v_a_1559_);
lean_dec(v_a_1554_);
lean_dec(v_a_1551_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1537_);
return v___x_1570_;
}
}
else
{
lean_dec_ref(v___x_1565_);
lean_dec(v_a_1563_);
lean_dec(v_a_1559_);
lean_dec(v_a_1554_);
lean_dec(v_a_1551_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1541_);
lean_dec(v___y_1537_);
return v___x_1566_;
}
}
else
{
lean_dec_ref(v___x_1561_);
lean_dec(v_a_1559_);
lean_dec(v_a_1554_);
lean_dec(v_a_1551_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec(v___y_1537_);
return v___x_1562_;
}
}
else
{
lean_dec_ref(v___x_1557_);
lean_dec(v_a_1554_);
lean_dec(v_a_1551_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec(v___y_1537_);
return v___x_1558_;
}
}
else
{
lean_dec(v_a_1551_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec(v___y_1537_);
return v___x_1553_;
}
}
else
{
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec(v___y_1537_);
lean_dec(v___y_1536_);
return v___x_1550_;
}
}
v___jp_1596_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_mk_empty_array_with_capacity(v___x_1595_);
lean_inc(v_letTk_1534_);
lean_inc_ref(v___x_1609_);
v___x_1610_ = lean_array_push(v___x_1609_, v_letTk_1534_);
if (lean_obj_tag(v___y_1598_) == 0)
{
lean_object* v___x_1611_; 
lean_dec_ref(v___x_1609_);
v___x_1611_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElseLike___closed__0));
v___y_1536_ = v___y_1598_;
v___y_1537_ = v___y_1597_;
v___y_1538_ = v___y_1599_;
v___y_1539_ = v___y_1607_;
v___y_1540_ = v___y_1604_;
v___y_1541_ = v___y_1603_;
v___y_1542_ = v___y_1605_;
v___y_1543_ = v___y_1600_;
v___y_1544_ = v___x_1610_;
v___y_1545_ = v_body_x3f_1606_;
v___y_1546_ = v___y_1608_;
v___y_1547_ = v___y_1602_;
v___y_1548_ = v___y_1601_;
v___y_1549_ = v___x_1611_;
goto v___jp_1535_;
}
else
{
lean_object* v_val_1612_; lean_object* v___x_1613_; 
v_val_1612_ = lean_ctor_get(v___y_1598_, 0);
lean_inc(v_val_1612_);
v___x_1613_ = lean_array_push(v___x_1609_, v_val_1612_);
v___y_1536_ = v___y_1598_;
v___y_1537_ = v___y_1597_;
v___y_1538_ = v___y_1599_;
v___y_1539_ = v___y_1607_;
v___y_1540_ = v___y_1604_;
v___y_1541_ = v___y_1603_;
v___y_1542_ = v___y_1605_;
v___y_1543_ = v___y_1600_;
v___y_1544_ = v___x_1610_;
v___y_1545_ = v_body_x3f_1606_;
v___y_1546_ = v___y_1608_;
v___y_1547_ = v___y_1602_;
v___y_1548_ = v___y_1601_;
v___y_1549_ = v___x_1613_;
goto v___jp_1535_;
}
}
v___jp_1614_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1618_ = lean_unsigned_to_nat(2u);
v___x_1619_ = l_Lean_Syntax_getArg(v_x_1526_, v___x_1618_);
v___x_1620_ = ((lean_object*)(l_Lean_Fmt_fmtDoLet___closed__3));
lean_inc(v___x_1619_);
v___x_1621_ = l_Lean_Syntax_isOfKind(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_dec(v___x_1619_);
lean_dec(v_mutTk_x3f_1615_);
lean_dec(v_letTk_1534_);
lean_dec(v_x_1526_);
v___x_1622_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v___y_1617_);
return v___x_1623_;
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1624_ = lean_unsigned_to_nat(7u);
v___x_1625_ = l_Lean_Syntax_getArg(v_x_1526_, v___x_1624_);
v___x_1626_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqIndent___closed__1));
lean_inc(v___x_1625_);
v___x_1627_ = l_Lean_Syntax_isOfKind(v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v___x_1625_);
lean_dec(v___x_1619_);
lean_dec(v_mutTk_x3f_1615_);
lean_dec(v_letTk_1534_);
lean_dec(v_x_1526_);
v___x_1628_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v___y_1617_);
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_colonEqTk_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_pipeTk_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1630_ = lean_unsigned_to_nat(3u);
v___x_1631_ = l_Lean_Syntax_getArg(v_x_1526_, v___x_1630_);
v___x_1632_ = lean_unsigned_to_nat(4u);
v_colonEqTk_1633_ = l_Lean_Syntax_getArg(v_x_1526_, v___x_1632_);
v___x_1634_ = lean_unsigned_to_nat(5u);
v___x_1635_ = l_Lean_Syntax_getArg(v_x_1526_, v___x_1634_);
v___x_1636_ = lean_unsigned_to_nat(6u);
v_pipeTk_1637_ = l_Lean_Syntax_getArg(v_x_1526_, v___x_1636_);
v___x_1638_ = lean_unsigned_to_nat(8u);
v___x_1639_ = l_Lean_Syntax_getArg(v_x_1526_, v___x_1638_);
lean_dec(v_x_1526_);
v___x_1640_ = l_Lean_Syntax_isNone(v___x_1639_);
if (v___x_1640_ == 0)
{
uint8_t v___x_1641_; 
lean_inc(v___x_1639_);
v___x_1641_ = l_Lean_Syntax_matchesNull(v___x_1639_, v___x_1595_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec(v___x_1639_);
lean_dec(v_pipeTk_1637_);
lean_dec(v___x_1635_);
lean_dec(v_colonEqTk_1633_);
lean_dec(v___x_1631_);
lean_dec(v___x_1625_);
lean_dec(v___x_1619_);
lean_dec(v_mutTk_x3f_1615_);
lean_dec(v_letTk_1534_);
v___x_1642_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v___y_1617_);
return v___x_1643_;
}
else
{
lean_object* v_body_x3f_1644_; uint8_t v___x_1645_; 
v_body_x3f_1644_ = l_Lean_Syntax_getArg(v___x_1639_, v___x_1533_);
lean_dec(v___x_1639_);
lean_inc(v_body_x3f_1644_);
v___x_1645_ = l_Lean_Syntax_isOfKind(v_body_x3f_1644_, v___x_1626_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec(v_body_x3f_1644_);
lean_dec(v_pipeTk_1637_);
lean_dec(v___x_1635_);
lean_dec(v_colonEqTk_1633_);
lean_dec(v___x_1631_);
lean_dec(v___x_1625_);
lean_dec(v___x_1619_);
lean_dec(v_mutTk_x3f_1615_);
lean_dec(v_letTk_1534_);
v___x_1646_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
lean_ctor_set(v___x_1647_, 1, v___y_1617_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1648_, 0, v_body_x3f_1644_);
v___y_1597_ = v_pipeTk_1637_;
v___y_1598_ = v_mutTk_x3f_1615_;
v___y_1599_ = v___x_1618_;
v___y_1600_ = v___x_1632_;
v___y_1601_ = v___x_1625_;
v___y_1602_ = v___x_1619_;
v___y_1603_ = v___x_1635_;
v___y_1604_ = v_colonEqTk_1633_;
v___y_1605_ = v___x_1631_;
v_body_x3f_1606_ = v___x_1648_;
v___y_1607_ = v___y_1616_;
v___y_1608_ = v___y_1617_;
goto v___jp_1596_;
}
}
}
else
{
lean_object* v___x_1649_; 
lean_dec(v___x_1639_);
v___x_1649_ = lean_box(0);
v___y_1597_ = v_pipeTk_1637_;
v___y_1598_ = v_mutTk_x3f_1615_;
v___y_1599_ = v___x_1618_;
v___y_1600_ = v___x_1632_;
v___y_1601_ = v___x_1625_;
v___y_1602_ = v___x_1619_;
v___y_1603_ = v___x_1635_;
v___y_1604_ = v_colonEqTk_1633_;
v___y_1605_ = v___x_1631_;
v_body_x3f_1606_ = v___x_1649_;
v___y_1607_ = v___y_1616_;
v___y_1608_ = v___y_1617_;
goto v___jp_1596_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetElse___boxed(lean_object* v_x_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_Fmt_fmtDoLetElse(v_x_1658_, v_a_1659_, v_a_1660_);
lean_dec_ref(v_a_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1(){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1668_ = l_Lean_Fmt_fmtAttribute;
v___x_1669_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElse___closed__1));
v___x_1670_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___closed__1));
v___x_1671_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoLetElse___boxed), 3, 0);
v___x_1672_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1668_, v___x_1669_, v___x_1670_, v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1___boxed(lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1();
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetExpr(lean_object* v_x_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetExpr___closed__1));
lean_inc(v_x_1687_);
v___x_1691_ = l_Lean_Syntax_isOfKind(v_x_1687_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v_x_1687_);
v___x_1692_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v_a_1689_);
return v___x_1693_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = l_Lean_Syntax_getArg(v_x_1687_, v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetExpr___closed__3));
lean_inc(v___x_1695_);
v___x_1697_ = l_Lean_Syntax_isOfKind(v___x_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec(v___x_1695_);
lean_dec(v_x_1687_);
v___x_1698_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v_a_1689_);
return v___x_1699_;
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1700_ = lean_unsigned_to_nat(5u);
v___x_1701_ = l_Lean_Syntax_getArg(v_x_1687_, v___x_1700_);
v___x_1702_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqIndent___closed__1));
lean_inc(v___x_1701_);
v___x_1703_ = l_Lean_Syntax_isOfKind(v___x_1701_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v___x_1701_);
lean_dec(v___x_1695_);
lean_dec(v_x_1687_);
v___x_1704_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v_a_1689_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v_letExprTk_1707_; lean_object* v___x_1708_; lean_object* v_colonEqTk_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v_pipeTk_1713_; lean_object* v_body_x3f_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v_letExprTk_1707_ = l_Lean_Syntax_getArg(v_x_1687_, v___x_1706_);
v___x_1708_ = lean_unsigned_to_nat(2u);
v_colonEqTk_1709_ = l_Lean_Syntax_getArg(v_x_1687_, v___x_1708_);
v___x_1710_ = lean_unsigned_to_nat(3u);
v___x_1711_ = l_Lean_Syntax_getArg(v_x_1687_, v___x_1710_);
v___x_1712_ = lean_unsigned_to_nat(4u);
v_pipeTk_1713_ = l_Lean_Syntax_getArg(v_x_1687_, v___x_1712_);
v___x_1752_ = lean_unsigned_to_nat(6u);
v___x_1753_ = l_Lean_Syntax_getArg(v_x_1687_, v___x_1752_);
lean_dec(v_x_1687_);
v___x_1754_ = l_Lean_Syntax_isNone(v___x_1753_);
if (v___x_1754_ == 0)
{
uint8_t v___x_1755_; 
lean_inc(v___x_1753_);
v___x_1755_ = l_Lean_Syntax_matchesNull(v___x_1753_, v___x_1694_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v___x_1753_);
lean_dec(v_pipeTk_1713_);
lean_dec(v___x_1711_);
lean_dec(v_colonEqTk_1709_);
lean_dec(v_letExprTk_1707_);
lean_dec(v___x_1701_);
lean_dec(v___x_1695_);
v___x_1756_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v_a_1689_);
return v___x_1757_;
}
else
{
lean_object* v_body_x3f_1758_; uint8_t v___x_1759_; 
v_body_x3f_1758_ = l_Lean_Syntax_getArg(v___x_1753_, v___x_1706_);
lean_dec(v___x_1753_);
lean_inc(v_body_x3f_1758_);
v___x_1759_ = l_Lean_Syntax_isOfKind(v_body_x3f_1758_, v___x_1702_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v_body_x3f_1758_);
lean_dec(v_pipeTk_1713_);
lean_dec(v___x_1711_);
lean_dec(v_colonEqTk_1709_);
lean_dec(v_letExprTk_1707_);
lean_dec(v___x_1701_);
lean_dec(v___x_1695_);
v___x_1760_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v_a_1689_);
return v___x_1761_;
}
else
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_body_x3f_1758_);
v_body_x3f_1715_ = v___x_1762_;
v___y_1716_ = v_a_1688_;
v___y_1717_ = v_a_1689_;
goto v___jp_1714_;
}
}
}
else
{
lean_object* v___x_1763_; 
lean_dec(v___x_1753_);
v___x_1763_ = lean_box(0);
v_body_x3f_1715_ = v___x_1763_;
v___y_1716_ = v_a_1688_;
v___y_1717_ = v_a_1689_;
goto v___jp_1714_;
}
v___jp_1714_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_mk_empty_array_with_capacity(v___x_1712_);
lean_inc(v_letExprTk_1707_);
v___x_1719_ = lean_array_push(v___x_1718_, v_letExprTk_1707_);
v___x_1720_ = l_Lean_Fmt_fmt(v_letExprTk_1707_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
v_a_1722_ = lean_ctor_get(v___x_1720_, 1);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1720_, 2);
lean_inc(v___x_1695_);
v___x_1723_ = lean_array_push(v___x_1719_, v___x_1695_);
v___x_1724_ = l_Lean_Fmt_fmt(v___x_1695_, v___y_1716_, v_a_1722_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
v_a_1726_ = lean_ctor_get(v___x_1724_, 1);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1724_, 2);
lean_inc(v_colonEqTk_1709_);
v___x_1727_ = lean_array_push(v___x_1723_, v_colonEqTk_1709_);
v___x_1728_ = l_Lean_Fmt_fmt(v_colonEqTk_1709_, v___y_1716_, v_a_1726_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v_a_1730_; lean_object* v_declComponents_1731_; lean_object* v___x_1732_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
v_a_1730_ = lean_ctor_get(v___x_1728_, 1);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1728_, 2);
lean_inc(v___x_1711_);
v_declComponents_1731_ = lean_array_push(v___x_1727_, v___x_1711_);
v___x_1732_ = l_Lean_Fmt_fmt(v___x_1711_, v___y_1716_, v_a_1730_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v_a_1734_; uint8_t v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
v_a_1734_ = lean_ctor_get(v___x_1732_, 1);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1732_, 2);
v___x_1735_ = 0;
v___x_1736_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1725_, v_a_1729_, v_a_1733_, v___x_1735_);
v___x_1737_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_1738_ = l_Lean_Fmt_Layouts_letDecl(v_a_1721_, v___x_1737_, v___x_1736_, v___x_1735_);
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v_pipeTk_1713_);
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1701_);
if (lean_obj_tag(v_body_x3f_1715_) == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_box(0);
v___x_1742_ = l_Lean_Fmt_fmtDoLetElseLike(v___x_1738_, v_declComponents_1731_, v___x_1739_, v___x_1740_, v___x_1741_, v___y_1716_, v_a_1734_);
return v___x_1742_;
}
else
{
lean_object* v_val_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1751_; 
v_val_1743_ = lean_ctor_get(v_body_x3f_1715_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_body_x3f_1715_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1745_ = v_body_x3f_1715_;
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_val_1743_);
lean_dec(v_body_x3f_1715_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_val_1743_);
v___x_1748_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Fmt_fmtDoLetElseLike(v___x_1738_, v_declComponents_1731_, v___x_1739_, v___x_1740_, v___x_1748_, v___y_1716_, v_a_1734_);
return v___x_1749_;
}
}
}
}
else
{
lean_dec_ref(v_declComponents_1731_);
lean_dec(v_a_1729_);
lean_dec(v_a_1725_);
lean_dec(v_a_1721_);
lean_dec(v_body_x3f_1715_);
lean_dec(v_pipeTk_1713_);
lean_dec(v___x_1701_);
return v___x_1732_;
}
}
else
{
lean_dec_ref(v___x_1727_);
lean_dec(v_a_1725_);
lean_dec(v_a_1721_);
lean_dec(v_body_x3f_1715_);
lean_dec(v_pipeTk_1713_);
lean_dec(v___x_1711_);
lean_dec(v___x_1701_);
return v___x_1728_;
}
}
else
{
lean_dec_ref(v___x_1723_);
lean_dec(v_a_1721_);
lean_dec(v_body_x3f_1715_);
lean_dec(v_pipeTk_1713_);
lean_dec(v___x_1711_);
lean_dec(v_colonEqTk_1709_);
lean_dec(v___x_1701_);
return v___x_1724_;
}
}
else
{
lean_dec_ref(v___x_1719_);
lean_dec(v_body_x3f_1715_);
lean_dec(v_pipeTk_1713_);
lean_dec(v___x_1711_);
lean_dec(v_colonEqTk_1709_);
lean_dec(v___x_1701_);
lean_dec(v___x_1695_);
return v___x_1720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetExpr___boxed(lean_object* v_x_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_Fmt_fmtDoLetExpr(v_x_1764_, v_a_1765_, v_a_1766_);
lean_dec_ref(v_a_1765_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1(){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1774_ = l_Lean_Fmt_fmtAttribute;
v___x_1775_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetExpr___closed__1));
v___x_1776_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___closed__1));
v___x_1777_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoLetExpr___boxed), 3, 0);
v___x_1778_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1___boxed(lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1();
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetMetaExpr(lean_object* v_x_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetMetaExpr___closed__1));
lean_inc(v_x_1787_);
v___x_1791_ = l_Lean_Syntax_isOfKind(v_x_1787_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec(v_x_1787_);
v___x_1792_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
lean_ctor_set(v___x_1793_, 1, v_a_1789_);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = l_Lean_Syntax_getArg(v_x_1787_, v___x_1794_);
v___x_1796_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetExpr___closed__3));
lean_inc(v___x_1795_);
v___x_1797_ = l_Lean_Syntax_isOfKind(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v___x_1795_);
lean_dec(v_x_1787_);
v___x_1798_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v_a_1789_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1800_ = lean_unsigned_to_nat(5u);
v___x_1801_ = l_Lean_Syntax_getArg(v_x_1787_, v___x_1800_);
v___x_1802_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqIndent___closed__1));
lean_inc(v___x_1801_);
v___x_1803_ = l_Lean_Syntax_isOfKind(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v___x_1801_);
lean_dec(v___x_1795_);
lean_dec(v_x_1787_);
v___x_1804_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v_a_1789_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v_letExprTk_1807_; lean_object* v___x_1808_; lean_object* v_leftArrowTk_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_pipeTk_1813_; lean_object* v_body_x3f_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v_letExprTk_1807_ = l_Lean_Syntax_getArg(v_x_1787_, v___x_1806_);
v___x_1808_ = lean_unsigned_to_nat(2u);
v_leftArrowTk_1809_ = l_Lean_Syntax_getArg(v_x_1787_, v___x_1808_);
v___x_1810_ = lean_unsigned_to_nat(3u);
v___x_1811_ = l_Lean_Syntax_getArg(v_x_1787_, v___x_1810_);
v___x_1812_ = lean_unsigned_to_nat(4u);
v_pipeTk_1813_ = l_Lean_Syntax_getArg(v_x_1787_, v___x_1812_);
v___x_1852_ = lean_unsigned_to_nat(6u);
v___x_1853_ = l_Lean_Syntax_getArg(v_x_1787_, v___x_1852_);
lean_dec(v_x_1787_);
v___x_1854_ = l_Lean_Syntax_isNone(v___x_1853_);
if (v___x_1854_ == 0)
{
uint8_t v___x_1855_; 
lean_inc(v___x_1853_);
v___x_1855_ = l_Lean_Syntax_matchesNull(v___x_1853_, v___x_1794_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v___x_1853_);
lean_dec(v_pipeTk_1813_);
lean_dec(v___x_1811_);
lean_dec(v_leftArrowTk_1809_);
lean_dec(v_letExprTk_1807_);
lean_dec(v___x_1801_);
lean_dec(v___x_1795_);
v___x_1856_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set(v___x_1857_, 1, v_a_1789_);
return v___x_1857_;
}
else
{
lean_object* v_body_x3f_1858_; uint8_t v___x_1859_; 
v_body_x3f_1858_ = l_Lean_Syntax_getArg(v___x_1853_, v___x_1806_);
lean_dec(v___x_1853_);
lean_inc(v_body_x3f_1858_);
v___x_1859_ = l_Lean_Syntax_isOfKind(v_body_x3f_1858_, v___x_1802_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec(v_body_x3f_1858_);
lean_dec(v_pipeTk_1813_);
lean_dec(v___x_1811_);
lean_dec(v_leftArrowTk_1809_);
lean_dec(v_letExprTk_1807_);
lean_dec(v___x_1801_);
lean_dec(v___x_1795_);
v___x_1860_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v_a_1789_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_body_x3f_1858_);
v_body_x3f_1815_ = v___x_1862_;
v___y_1816_ = v_a_1788_;
v___y_1817_ = v_a_1789_;
goto v___jp_1814_;
}
}
}
else
{
lean_object* v___x_1863_; 
lean_dec(v___x_1853_);
v___x_1863_ = lean_box(0);
v_body_x3f_1815_ = v___x_1863_;
v___y_1816_ = v_a_1788_;
v___y_1817_ = v_a_1789_;
goto v___jp_1814_;
}
v___jp_1814_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = lean_mk_empty_array_with_capacity(v___x_1812_);
lean_inc(v_letExprTk_1807_);
v___x_1819_ = lean_array_push(v___x_1818_, v_letExprTk_1807_);
v___x_1820_ = l_Lean_Fmt_fmt(v_letExprTk_1807_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v_a_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
v_a_1822_ = lean_ctor_get(v___x_1820_, 1);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1820_, 2);
lean_inc(v___x_1795_);
v___x_1823_ = lean_array_push(v___x_1819_, v___x_1795_);
v___x_1824_ = l_Lean_Fmt_fmt(v___x_1795_, v___y_1816_, v_a_1822_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
v_a_1826_ = lean_ctor_get(v___x_1824_, 1);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1824_, 2);
lean_inc(v_leftArrowTk_1809_);
v___x_1827_ = lean_array_push(v___x_1823_, v_leftArrowTk_1809_);
v___x_1828_ = l_Lean_Fmt_fmt(v_leftArrowTk_1809_, v___y_1816_, v_a_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v_a_1830_; lean_object* v_declComponents_1831_; lean_object* v___x_1832_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
v_a_1830_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1828_, 2);
lean_inc(v___x_1811_);
v_declComponents_1831_ = lean_array_push(v___x_1827_, v___x_1811_);
v___x_1832_ = l_Lean_Fmt_fmt(v___x_1811_, v___y_1816_, v_a_1830_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v_a_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
v_a_1834_ = lean_ctor_get(v___x_1832_, 1);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1832_, 2);
v___x_1835_ = 0;
v___x_1836_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1825_, v_a_1829_, v_a_1833_, v___x_1835_);
v___x_1837_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_1838_ = l_Lean_Fmt_Layouts_letDecl(v_a_1821_, v___x_1837_, v___x_1836_, v___x_1835_);
v___x_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1839_, 0, v_pipeTk_1813_);
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1801_);
if (lean_obj_tag(v_body_x3f_1815_) == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = l_Lean_Fmt_fmtDoLetElseLike(v___x_1838_, v_declComponents_1831_, v___x_1839_, v___x_1840_, v___x_1841_, v___y_1816_, v_a_1834_);
return v___x_1842_;
}
else
{
lean_object* v_val_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v_val_1843_ = lean_ctor_get(v_body_x3f_1815_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_body_x3f_1815_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1845_ = v_body_x3f_1815_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_val_1843_);
lean_dec(v_body_x3f_1815_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_val_1843_);
v___x_1848_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_Fmt_fmtDoLetElseLike(v___x_1838_, v_declComponents_1831_, v___x_1839_, v___x_1840_, v___x_1848_, v___y_1816_, v_a_1834_);
return v___x_1849_;
}
}
}
}
else
{
lean_dec_ref(v_declComponents_1831_);
lean_dec(v_a_1829_);
lean_dec(v_a_1825_);
lean_dec(v_a_1821_);
lean_dec(v_body_x3f_1815_);
lean_dec(v_pipeTk_1813_);
lean_dec(v___x_1801_);
return v___x_1832_;
}
}
else
{
lean_dec_ref(v___x_1827_);
lean_dec(v_a_1825_);
lean_dec(v_a_1821_);
lean_dec(v_body_x3f_1815_);
lean_dec(v_pipeTk_1813_);
lean_dec(v___x_1811_);
lean_dec(v___x_1801_);
return v___x_1828_;
}
}
else
{
lean_dec_ref(v___x_1823_);
lean_dec(v_a_1821_);
lean_dec(v_body_x3f_1815_);
lean_dec(v_pipeTk_1813_);
lean_dec(v___x_1811_);
lean_dec(v_leftArrowTk_1809_);
lean_dec(v___x_1801_);
return v___x_1824_;
}
}
else
{
lean_dec_ref(v___x_1819_);
lean_dec(v_body_x3f_1815_);
lean_dec(v_pipeTk_1813_);
lean_dec(v___x_1811_);
lean_dec(v_leftArrowTk_1809_);
lean_dec(v___x_1801_);
lean_dec(v___x_1795_);
return v___x_1820_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetMetaExpr___boxed(lean_object* v_x_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_Fmt_fmtDoLetMetaExpr(v_x_1864_, v_a_1865_, v_a_1866_);
lean_dec_ref(v_a_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1(){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1874_ = l_Lean_Fmt_fmtAttribute;
v___x_1875_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetMetaExpr___closed__1));
v___x_1876_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___closed__1));
v___x_1877_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoLetMetaExpr___boxed), 3, 0);
v___x_1878_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1874_, v___x_1875_, v___x_1876_, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1___boxed(lean_object* v_a_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1();
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetRec(lean_object* v_x_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetRec___closed__1));
lean_inc(v_x_1896_);
v___x_1900_ = l_Lean_Syntax_isOfKind(v_x_1896_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v_x_1896_);
v___x_1901_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v_a_1898_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1904_ = l_Lean_Syntax_getArg(v_x_1896_, v___x_1903_);
v___x_1905_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetRec___closed__3));
lean_inc(v___x_1904_);
v___x_1906_ = l_Lean_Syntax_isOfKind(v___x_1904_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
lean_dec(v___x_1904_);
lean_dec(v_x_1896_);
v___x_1907_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v_a_1898_);
return v___x_1908_;
}
else
{
lean_object* v___x_1909_; lean_object* v_decls_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1909_ = lean_unsigned_to_nat(1u);
v_decls_1910_ = l_Lean_Syntax_getArg(v_x_1896_, v___x_1909_);
lean_dec(v_x_1896_);
v___x_1911_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetRec___closed__5));
lean_inc(v_decls_1910_);
v___x_1912_ = l_Lean_Syntax_isOfKind(v_decls_1910_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_dec(v_decls_1910_);
lean_dec(v___x_1904_);
v___x_1913_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v_a_1898_);
return v___x_1914_;
}
else
{
lean_object* v_letTk_1915_; lean_object* v_recTk_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_letTk_1915_ = l_Lean_Syntax_getArg(v___x_1904_, v___x_1903_);
v_recTk_1916_ = l_Lean_Syntax_getArg(v___x_1904_, v___x_1909_);
lean_dec(v___x_1904_);
v___x_1917_ = lean_unsigned_to_nat(2u);
v___x_1918_ = lean_mk_empty_array_with_capacity(v___x_1917_);
v___x_1919_ = lean_array_push(v___x_1918_, v_letTk_1915_);
v___x_1920_ = lean_array_push(v___x_1919_, v_recTk_1916_);
v___x_1921_ = l_Lean_Fmt_fmtFullLetRecDecl(v___x_1920_, v_decls_1910_, v_a_1897_, v_a_1898_);
return v___x_1921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoLetRec___boxed(lean_object* v_x_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_Fmt_fmtDoLetRec(v_x_1922_, v_a_1923_, v_a_1924_);
lean_dec_ref(v_a_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1(){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1932_ = l_Lean_Fmt_fmtAttribute;
v___x_1933_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetRec___closed__1));
v___x_1934_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___closed__1));
v___x_1935_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoLetRec___boxed), 3, 0);
v___x_1936_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1932_, v___x_1933_, v___x_1934_, v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1___boxed(lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1();
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLetIdDeclNoBinders(lean_object* v_x_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1));
lean_inc(v_x_1951_);
v___x_1955_ = l_Lean_Syntax_isOfKind(v_x_1951_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_dec(v_x_1951_);
v___x_1956_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v_a_1953_);
return v___x_1957_;
}
else
{
lean_object* v___x_1958_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1990_ = l_Lean_Syntax_getArg(v_x_1951_, v___x_1958_);
v___x_1991_ = ((lean_object*)(l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__3));
lean_inc(v___x_1990_);
v___x_1992_ = l_Lean_Syntax_isOfKind(v___x_1990_, v___x_1991_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_dec(v___x_1990_);
lean_dec(v_x_1951_);
v___x_1993_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v_a_1953_);
return v___x_1994_;
}
else
{
lean_object* v___x_1995_; lean_object* v_typeAscriptionTk_x3f_1997_; lean_object* v_type_x3f_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_1995_ = l_Lean_Syntax_getArg(v___x_1990_, v___x_1958_);
lean_dec(v___x_1990_);
v___x_2020_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__4));
lean_inc(v___x_1995_);
v___x_2021_ = l_Lean_Syntax_isOfKind(v___x_1995_, v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v___x_1995_);
lean_dec(v_x_1951_);
v___x_2022_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v_a_1953_);
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = l_Lean_Syntax_getArg(v_x_1951_, v___x_2024_);
v___x_2026_ = l_Lean_Syntax_matchesNull(v___x_2025_, v___x_1958_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_dec(v___x_1995_);
lean_dec(v_x_1951_);
v___x_2027_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v_a_1953_);
return v___x_2028_;
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2029_ = lean_unsigned_to_nat(2u);
v___x_2030_ = l_Lean_Syntax_getArg(v_x_1951_, v___x_2029_);
v___x_2031_ = l_Lean_Syntax_isNone(v___x_2030_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; 
lean_inc(v___x_2030_);
v___x_2032_ = l_Lean_Syntax_matchesNull(v___x_2030_, v___x_2024_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec(v___x_2030_);
lean_dec(v___x_1995_);
lean_dec(v_x_1951_);
v___x_2033_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v_a_1953_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2035_ = l_Lean_Syntax_getArg(v___x_2030_, v___x_1958_);
lean_dec(v___x_2030_);
v___x_2036_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__6));
lean_inc(v___x_2035_);
v___x_2037_ = l_Lean_Syntax_isOfKind(v___x_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v___x_2035_);
lean_dec(v___x_1995_);
lean_dec(v_x_1951_);
v___x_2038_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
lean_ctor_set(v___x_2039_, 1, v_a_1953_);
return v___x_2039_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_2040_; lean_object* v_type_x3f_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_typeAscriptionTk_x3f_2040_ = l_Lean_Syntax_getArg(v___x_2035_, v___x_1958_);
v_type_x3f_2041_ = l_Lean_Syntax_getArg(v___x_2035_, v___x_2024_);
lean_dec(v___x_2035_);
v___x_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_typeAscriptionTk_x3f_2040_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_type_x3f_2041_);
v_typeAscriptionTk_x3f_1997_ = v___x_2042_;
v_type_x3f_1998_ = v___x_2043_;
v___y_1999_ = v_a_1952_;
v___y_2000_ = v_a_1953_;
goto v___jp_1996_;
}
}
}
else
{
lean_object* v___x_2044_; 
lean_dec(v___x_2030_);
v___x_2044_ = lean_box(0);
v_typeAscriptionTk_x3f_1997_ = v___x_2044_;
v_type_x3f_1998_ = v___x_2044_;
v___y_1999_ = v_a_1952_;
v___y_2000_ = v_a_1953_;
goto v___jp_1996_;
}
}
}
v___jp_1996_:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Fmt_fmt(v___x_1995_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v_a_2003_; lean_object* v___x_2004_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
v_a_2003_ = lean_ctor_get(v___x_2001_, 1);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2001_, 2);
v___x_2004_ = l_Lean_Fmt_fmt_x3f(v_typeAscriptionTk_x3f_1997_, v___y_1999_, v_a_2003_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v_a_2006_; lean_object* v___x_2007_; lean_object* v_colonEqTk_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
v_a_2006_ = lean_ctor_get(v___x_2004_, 1);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_2004_, 2);
v___x_2007_ = lean_unsigned_to_nat(3u);
v_colonEqTk_2008_ = l_Lean_Syntax_getArg(v_x_1951_, v___x_2007_);
v___x_2009_ = lean_unsigned_to_nat(4u);
v___x_2010_ = l_Lean_Syntax_getArg(v_x_1951_, v___x_2009_);
lean_dec(v_x_1951_);
if (lean_obj_tag(v_type_x3f_1998_) == 0)
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_box(0);
v___y_1960_ = v_a_2006_;
v___y_1961_ = v___x_2010_;
v___y_1962_ = v_a_2002_;
v___y_1963_ = v___y_1999_;
v___y_1964_ = v_a_2005_;
v___y_1965_ = v_colonEqTk_2008_;
v___y_1966_ = v___x_2011_;
goto v___jp_1959_;
}
else
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_val_2012_ = lean_ctor_get(v_type_x3f_1998_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_type_x3f_1998_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v_type_x3f_1998_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v_type_x3f_1998_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_val_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
v___y_1960_ = v_a_2006_;
v___y_1961_ = v___x_2010_;
v___y_1962_ = v_a_2002_;
v___y_1963_ = v___y_1999_;
v___y_1964_ = v_a_2005_;
v___y_1965_ = v_colonEqTk_2008_;
v___y_1966_ = v___x_2017_;
goto v___jp_1959_;
}
}
}
}
else
{
lean_dec(v_a_2002_);
lean_dec(v_type_x3f_1998_);
lean_dec(v_x_1951_);
return v___x_2004_;
}
}
else
{
lean_dec(v_type_x3f_1998_);
lean_dec(v_typeAscriptionTk_x3f_1997_);
lean_dec(v_x_1951_);
return v___x_2001_;
}
}
}
v___jp_1959_:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Fmt_fmt_x3f(v___y_1966_, v___y_1963_, v___y_1960_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
v_a_1969_ = lean_ctor_get(v___x_1967_, 1);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1967_, 2);
v___x_1970_ = l_Lean_Fmt_fmt(v___y_1965_, v___y_1963_, v_a_1969_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v_a_1972_; lean_object* v___x_1973_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
v_a_1972_ = lean_ctor_get(v___x_1970_, 1);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1970_, 2);
v___x_1973_ = l_Lean_Fmt_fmt(v___y_1961_, v___y_1963_, v_a_1972_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1989_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_a_1975_ = lean_ctor_get(v___x_1973_, 1);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1977_ = v___x_1973_;
v_isShared_1978_ = v_isSharedCheck_1989_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1989_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_mk_empty_array_with_capacity(v___x_1979_);
v___x_1981_ = lean_array_push(v___x_1980_, v___y_1962_);
v___x_1982_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__2));
v___x_1983_ = l_Lean_Fmt_Layouts_localSignature(v___x_1981_, v___x_1982_, v___y_1964_, v_a_1968_);
lean_dec_ref(v___x_1981_);
v___x_1984_ = 0;
v___x_1985_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_1983_, v_a_1971_, v_a_1974_, v___x_1984_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1985_);
v___x_1987_ = v___x_1977_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_a_1975_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
else
{
lean_dec(v_a_1971_);
lean_dec(v_a_1968_);
lean_dec_ref(v___y_1964_);
lean_dec_ref(v___y_1962_);
return v___x_1973_;
}
}
else
{
lean_dec(v_a_1968_);
lean_dec_ref(v___y_1964_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
return v___x_1970_;
}
}
else
{
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
return v___x_1967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLetIdDeclNoBinders___boxed(lean_object* v_x_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_Fmt_fmtLetIdDeclNoBinders(v_x_2045_, v_a_2046_, v_a_2047_);
lean_dec_ref(v_a_2046_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1(){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2055_ = l_Lean_Fmt_fmtAttribute;
v___x_2056_ = ((lean_object*)(l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1));
v___x_2057_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___closed__1));
v___x_2058_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLetIdDeclNoBinders___boxed), 3, 0);
v___x_2059_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2055_, v___x_2056_, v___x_2057_, v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1___boxed(lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1();
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReassign(lean_object* v_x_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = ((lean_object*)(l_Lean_Fmt_fmtDoReassign___closed__1));
lean_inc(v_x_2074_);
v___x_2078_ = l_Lean_Syntax_isOfKind(v_x_2074_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec(v_x_2074_);
v___x_2079_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v_a_2076_);
return v___x_2080_;
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = l_Lean_Syntax_getArg(v_x_2074_, v___x_2081_);
lean_dec(v_x_2074_);
v___x_2083_ = ((lean_object*)(l_Lean_Fmt_fmtLetIdDeclNoBinders___closed__1));
lean_inc(v___x_2082_);
v___x_2084_ = l_Lean_Syntax_isOfKind(v___x_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Lean_Fmt_fmtDoReassign___closed__3));
lean_inc(v___x_2082_);
v___x_2086_ = l_Lean_Syntax_isOfKind(v___x_2082_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec(v___x_2082_);
v___x_2087_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v_a_2076_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Fmt_fmt(v___x_2082_, v_a_2075_, v_a_2076_);
return v___x_2089_;
}
}
else
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_Fmt_fmt(v___x_2082_, v_a_2075_, v_a_2076_);
return v___x_2090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReassign___boxed(lean_object* v_x_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Fmt_fmtDoReassign(v_x_2091_, v_a_2092_, v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1(){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2101_ = l_Lean_Fmt_fmtAttribute;
v___x_2102_ = ((lean_object*)(l_Lean_Fmt_fmtDoReassign___closed__1));
v___x_2103_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___closed__1));
v___x_2104_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoReassign___boxed), 3, 0);
v___x_2105_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2101_, v___x_2102_, v___x_2103_, v___x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1___boxed(lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1();
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReassignArrow(lean_object* v_x_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = ((lean_object*)(l_Lean_Fmt_fmtDoReassignArrow___closed__1));
lean_inc(v_x_2114_);
v___x_2118_ = l_Lean_Syntax_isOfKind(v_x_2114_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_dec(v_x_2114_);
v___x_2119_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v_a_2116_);
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; lean_object* v_decl_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2121_ = lean_unsigned_to_nat(0u);
v_decl_2122_ = l_Lean_Syntax_getArg(v_x_2114_, v___x_2121_);
lean_dec(v_x_2114_);
v___x_2123_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__1));
lean_inc(v_decl_2122_);
v___x_2124_ = l_Lean_Syntax_isOfKind(v_decl_2122_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoPatDecl___closed__1));
lean_inc(v_decl_2122_);
v___x_2126_ = l_Lean_Syntax_isOfKind(v_decl_2122_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec(v_decl_2122_);
v___x_2127_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v_a_2116_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElseLike___closed__0));
v___x_2130_ = lean_box(0);
v___x_2131_ = l_Lean_Fmt_fmtWithDoPatDecl(v___x_2129_, v___x_2130_, v_decl_2122_, v_a_2115_, v_a_2116_);
return v___x_2131_;
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetElseLike___closed__0));
v___x_2133_ = lean_box(0);
v___x_2134_ = l_Lean_Fmt_fmtWithDoIdDecl(v___x_2132_, v___x_2133_, v_decl_2122_, v_a_2115_, v_a_2116_);
return v___x_2134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoReassignArrow___boxed(lean_object* v_x_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Fmt_fmtDoReassignArrow(v_x_2135_, v_a_2136_, v_a_2137_);
lean_dec_ref(v_a_2136_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1(){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2145_ = l_Lean_Fmt_fmtAttribute;
v___x_2146_ = ((lean_object*)(l_Lean_Fmt_fmtDoReassignArrow___closed__1));
v___x_2147_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___closed__1));
v___x_2148_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoReassignArrow___boxed), 3, 0);
v___x_2149_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2145_, v___x_2146_, v___x_2147_, v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1___boxed(lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1();
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfProp(lean_object* v_x_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v___x_2161_; uint8_t v___x_2162_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v_h_x3f_2189_; lean_object* v_colonTk_x3f_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; 
v___x_2161_ = ((lean_object*)(l_Lean_Fmt_fmtDoIfProp___closed__1));
lean_inc(v_x_2158_);
v___x_2162_ = l_Lean_Syntax_isOfKind(v_x_2158_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec(v_x_2158_);
v___x_2204_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v_a_2160_);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = l_Lean_Syntax_getArg(v_x_2158_, v___x_2206_);
v___x_2208_ = l_Lean_Syntax_isNone(v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2207_);
v___x_2210_ = l_Lean_Syntax_matchesNull(v___x_2207_, v___x_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_dec(v___x_2207_);
lean_dec(v_x_2158_);
v___x_2211_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v_a_2160_);
return v___x_2212_;
}
else
{
lean_object* v_h_x3f_2213_; lean_object* v___x_2214_; lean_object* v_colonTk_x3f_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_h_x3f_2213_ = l_Lean_Syntax_getArg(v___x_2207_, v___x_2206_);
v___x_2214_ = lean_unsigned_to_nat(1u);
v_colonTk_x3f_2215_ = l_Lean_Syntax_getArg(v___x_2207_, v___x_2214_);
lean_dec(v___x_2207_);
v___x_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2216_, 0, v_h_x3f_2213_);
v___x_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_colonTk_x3f_2215_);
v_h_x3f_2189_ = v___x_2216_;
v_colonTk_x3f_2190_ = v___x_2217_;
v___y_2191_ = v_a_2159_;
v___y_2192_ = v_a_2160_;
goto v___jp_2188_;
}
}
else
{
lean_object* v___x_2218_; 
lean_dec(v___x_2207_);
v___x_2218_ = lean_box(0);
v_h_x3f_2189_ = v___x_2218_;
v_colonTk_x3f_2190_ = v___x_2218_;
v___y_2191_ = v_a_2159_;
v___y_2192_ = v_a_2160_;
goto v___jp_2188_;
}
}
v___jp_2163_:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_Fmt_fmt_x3f(v___y_2168_, v___y_2167_, v___y_2166_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v_a_2171_; lean_object* v___x_2172_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
v_a_2171_ = lean_ctor_get(v___x_2169_, 1);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2169_, 2);
v___x_2172_ = l_Lean_Fmt_fmt_x3f(v___y_2165_, v___y_2167_, v_a_2171_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v_a_2174_; lean_object* v___x_2175_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
v_a_2174_ = lean_ctor_get(v___x_2172_, 1);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2172_, 2);
v___x_2175_ = l_Lean_Fmt_fmt(v___y_2164_, v___y_2167_, v_a_2174_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2187_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_a_2177_ = lean_ctor_get(v___x_2175_, 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2179_ = v___x_2175_;
v_isShared_2180_ = v_isSharedCheck_2187_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2187_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2181_ = 0;
v___x_2182_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2182_, 0, v___x_2162_);
lean_ctor_set_uint8(v___x_2182_, 1, v___x_2181_);
lean_ctor_set_uint8(v___x_2182_, 2, v___x_2162_);
lean_ctor_set_uint8(v___x_2182_, 3, v___x_2162_);
v___x_2183_ = l_Lean_Fmt_Layouts_typeAscription(v_a_2170_, v_a_2173_, v_a_2176_, v___x_2182_);
lean_dec_ref_known(v___x_2182_, 0);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2183_);
v___x_2185_ = v___x_2179_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_a_2177_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
else
{
lean_dec(v_a_2173_);
lean_dec(v_a_2170_);
return v___x_2175_;
}
}
else
{
lean_dec(v_a_2170_);
lean_dec(v___y_2164_);
return v___x_2172_;
}
}
else
{
lean_dec(v___y_2165_);
lean_dec(v___y_2164_);
return v___x_2169_;
}
}
v___jp_2188_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_unsigned_to_nat(1u);
v___x_2194_ = l_Lean_Syntax_getArg(v_x_2158_, v___x_2193_);
lean_dec(v_x_2158_);
if (lean_obj_tag(v_h_x3f_2189_) == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_box(0);
v___y_2164_ = v___x_2194_;
v___y_2165_ = v_colonTk_x3f_2190_;
v___y_2166_ = v___y_2192_;
v___y_2167_ = v___y_2191_;
v___y_2168_ = v___x_2195_;
goto v___jp_2163_;
}
else
{
lean_object* v_val_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_val_2196_ = lean_ctor_get(v_h_x3f_2189_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_h_x3f_2189_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v_h_x3f_2189_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_val_2196_);
lean_dec(v_h_x3f_2189_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_val_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
v___y_2164_ = v___x_2194_;
v___y_2165_ = v_colonTk_x3f_2190_;
v___y_2166_ = v___y_2192_;
v___y_2167_ = v___y_2191_;
v___y_2168_ = v___x_2201_;
goto v___jp_2163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfProp___boxed(lean_object* v_x_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Fmt_fmtDoIfProp(v_x_2219_, v_a_2220_, v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1(){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2229_ = l_Lean_Fmt_fmtAttribute;
v___x_2230_ = ((lean_object*)(l_Lean_Fmt_fmtDoIfProp___closed__1));
v___x_2231_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___closed__1));
v___x_2232_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoIfProp___boxed), 3, 0);
v___x_2233_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2229_, v___x_2230_, v___x_2231_, v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1___boxed(lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1();
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfLetLike(lean_object* v_letTk_2236_, lean_object* v_pat_2237_, lean_object* v_sepTk_2238_, lean_object* v_value_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Fmt_fmt(v_letTk_2236_, v_a_2240_, v_a_2241_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v_a_2244_; lean_object* v___x_2245_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2243_);
v_a_2244_ = lean_ctor_get(v___x_2242_, 1);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2242_, 2);
v___x_2245_ = l_Lean_Fmt_fmt(v_pat_2237_, v_a_2240_, v_a_2244_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v_a_2247_; lean_object* v___x_2248_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
v_a_2247_ = lean_ctor_get(v___x_2245_, 1);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2245_, 2);
v___x_2248_ = l_Lean_Fmt_fmt(v_sepTk_2238_, v_a_2240_, v_a_2247_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v_a_2250_; lean_object* v___x_2251_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
v_a_2250_ = lean_ctor_get(v___x_2248_, 1);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___x_2248_, 2);
v___x_2251_ = l_Lean_Fmt_fmt(v_value_2239_, v_a_2240_, v_a_2250_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2264_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_a_2253_ = lean_ctor_get(v___x_2251_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2255_ = v___x_2251_;
v_isShared_2256_ = v_isSharedCheck_2264_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2264_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
uint8_t v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2257_ = 0;
v___x_2258_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_2246_, v_a_2249_, v_a_2252_, v___x_2257_);
v___x_2259_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_2260_ = l_Lean_Fmt_Layouts_letDecl(v_a_2243_, v___x_2259_, v___x_2258_, v___x_2257_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2260_);
v___x_2262_ = v___x_2255_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_a_2253_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
else
{
lean_dec(v_a_2249_);
lean_dec(v_a_2246_);
lean_dec(v_a_2243_);
return v___x_2251_;
}
}
else
{
lean_dec(v_a_2246_);
lean_dec(v_a_2243_);
lean_dec(v_value_2239_);
return v___x_2248_;
}
}
else
{
lean_dec(v_a_2243_);
lean_dec(v_value_2239_);
lean_dec(v_sepTk_2238_);
return v___x_2245_;
}
}
else
{
lean_dec(v_value_2239_);
lean_dec(v_sepTk_2238_);
lean_dec(v_pat_2237_);
return v___x_2242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfLetLike___boxed(lean_object* v_letTk_2265_, lean_object* v_pat_2266_, lean_object* v_sepTk_2267_, lean_object* v_value_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Fmt_fmtDoIfLetLike(v_letTk_2265_, v_pat_2266_, v_sepTk_2267_, v_value_2268_, v_a_2269_, v_a_2270_);
lean_dec_ref(v_a_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfLet(lean_object* v_x_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = ((lean_object*)(l_Lean_Fmt_fmtDoIfLet___closed__1));
lean_inc(v_x_2290_);
v___x_2294_ = l_Lean_Syntax_isOfKind(v_x_2290_, v___x_2293_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_dec(v_x_2290_);
v___x_2295_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v_a_2292_);
return v___x_2296_;
}
else
{
lean_object* v___x_2297_; lean_object* v_letTk_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2297_ = lean_unsigned_to_nat(0u);
v_letTk_2298_ = l_Lean_Syntax_getArg(v_x_2290_, v___x_2297_);
v___x_2299_ = lean_unsigned_to_nat(1u);
v___x_2300_ = l_Lean_Syntax_getArg(v_x_2290_, v___x_2299_);
v___x_2301_ = lean_unsigned_to_nat(2u);
v___x_2302_ = l_Lean_Syntax_getArg(v_x_2290_, v___x_2301_);
lean_dec(v_x_2290_);
v___x_2303_ = ((lean_object*)(l_Lean_Fmt_fmtDoIfLet___closed__3));
lean_inc(v___x_2302_);
v___x_2304_ = l_Lean_Syntax_isOfKind(v___x_2302_, v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = ((lean_object*)(l_Lean_Fmt_fmtDoIfLet___closed__5));
lean_inc(v___x_2302_);
v___x_2306_ = l_Lean_Syntax_isOfKind(v___x_2302_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec(v___x_2302_);
lean_dec(v___x_2300_);
lean_dec(v_letTk_2298_);
v___x_2307_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v_a_2292_);
return v___x_2308_;
}
else
{
lean_object* v_leftArrowTk_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_leftArrowTk_2309_ = l_Lean_Syntax_getArg(v___x_2302_, v___x_2297_);
v___x_2310_ = l_Lean_Syntax_getArg(v___x_2302_, v___x_2299_);
lean_dec(v___x_2302_);
v___x_2311_ = l_Lean_Fmt_fmtDoIfLetLike(v_letTk_2298_, v___x_2300_, v_leftArrowTk_2309_, v___x_2310_, v_a_2291_, v_a_2292_);
return v___x_2311_;
}
}
else
{
lean_object* v_colonEqTk_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_colonEqTk_2312_ = l_Lean_Syntax_getArg(v___x_2302_, v___x_2297_);
v___x_2313_ = l_Lean_Syntax_getArg(v___x_2302_, v___x_2299_);
lean_dec(v___x_2302_);
v___x_2314_ = l_Lean_Fmt_fmtDoIfLetLike(v_letTk_2298_, v___x_2300_, v_colonEqTk_2312_, v___x_2313_, v_a_2291_, v_a_2292_);
return v___x_2314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIfLet___boxed(lean_object* v_x_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_Fmt_fmtDoIfLet(v_x_2315_, v_a_2316_, v_a_2317_);
lean_dec_ref(v_a_2316_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1(){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2325_ = l_Lean_Fmt_fmtAttribute;
v___x_2326_ = ((lean_object*)(l_Lean_Fmt_fmtDoIfLet___closed__1));
v___x_2327_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___closed__1));
v___x_2328_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoIfLet___boxed), 3, 0);
v___x_2329_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2325_, v___x_2326_, v___x_2327_, v___x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1___boxed(lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1();
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__4(size_t v_sz_2332_, size_t v_i_2333_, lean_object* v_bs_2334_){
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
lean_object* v_v_2336_; lean_object* v_snd_2337_; lean_object* v_fst_2338_; lean_object* v___x_2339_; lean_object* v_bs_x27_2340_; size_t v___x_2341_; size_t v___x_2342_; lean_object* v___x_2343_; 
v_v_2336_ = lean_array_uget_borrowed(v_bs_2334_, v_i_2333_);
v_snd_2337_ = lean_ctor_get(v_v_2336_, 1);
v_fst_2338_ = lean_ctor_get(v_snd_2337_, 0);
lean_inc(v_fst_2338_);
v___x_2339_ = lean_unsigned_to_nat(0u);
v_bs_x27_2340_ = lean_array_uset(v_bs_2334_, v_i_2333_, v___x_2339_);
v___x_2341_ = ((size_t)1ULL);
v___x_2342_ = lean_usize_add(v_i_2333_, v___x_2341_);
v___x_2343_ = lean_array_uset(v_bs_x27_2340_, v_i_2333_, v_fst_2338_);
v_i_2333_ = v___x_2342_;
v_bs_2334_ = v___x_2343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__4___boxed(lean_object* v_sz_2345_, lean_object* v_i_2346_, lean_object* v_bs_2347_){
_start:
{
size_t v_sz_boxed_2348_; size_t v_i_boxed_2349_; lean_object* v_res_2350_; 
v_sz_boxed_2348_ = lean_unbox_usize(v_sz_2345_);
lean_dec(v_sz_2345_);
v_i_boxed_2349_ = lean_unbox_usize(v_i_2346_);
lean_dec(v_i_2346_);
v_res_2350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__4(v_sz_boxed_2348_, v_i_boxed_2349_, v_bs_2347_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__1(size_t v_sz_2351_, size_t v_i_2352_, lean_object* v_bs_2353_){
_start:
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_usize_dec_lt(v_i_2352_, v_sz_2351_);
if (v___x_2354_ == 0)
{
return v_bs_2353_;
}
else
{
lean_object* v_v_2355_; lean_object* v_snd_2356_; lean_object* v_snd_2357_; lean_object* v_snd_2358_; lean_object* v_snd_2359_; lean_object* v___x_2360_; lean_object* v_bs_x27_2361_; size_t v___x_2362_; size_t v___x_2363_; lean_object* v___x_2364_; 
v_v_2355_ = lean_array_uget_borrowed(v_bs_2353_, v_i_2352_);
v_snd_2356_ = lean_ctor_get(v_v_2355_, 1);
v_snd_2357_ = lean_ctor_get(v_snd_2356_, 1);
v_snd_2358_ = lean_ctor_get(v_snd_2357_, 1);
v_snd_2359_ = lean_ctor_get(v_snd_2358_, 1);
lean_inc(v_snd_2359_);
v___x_2360_ = lean_unsigned_to_nat(0u);
v_bs_x27_2361_ = lean_array_uset(v_bs_2353_, v_i_2352_, v___x_2360_);
v___x_2362_ = ((size_t)1ULL);
v___x_2363_ = lean_usize_add(v_i_2352_, v___x_2362_);
v___x_2364_ = lean_array_uset(v_bs_x27_2361_, v_i_2352_, v_snd_2359_);
v_i_2352_ = v___x_2363_;
v_bs_2353_ = v___x_2364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__1___boxed(lean_object* v_sz_2366_, lean_object* v_i_2367_, lean_object* v_bs_2368_){
_start:
{
size_t v_sz_boxed_2369_; size_t v_i_boxed_2370_; lean_object* v_res_2371_; 
v_sz_boxed_2369_ = lean_unbox_usize(v_sz_2366_);
lean_dec(v_sz_2366_);
v_i_boxed_2370_ = lean_unbox_usize(v_i_2367_);
lean_dec(v_i_2367_);
v_res_2371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__1(v_sz_boxed_2369_, v_i_boxed_2370_, v_bs_2368_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__0(size_t v_sz_2372_, size_t v_i_2373_, lean_object* v_bs_2374_){
_start:
{
uint8_t v___x_2375_; 
v___x_2375_ = lean_usize_dec_lt(v_i_2373_, v_sz_2372_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2376_, 0, v_bs_2374_);
return v___x_2376_;
}
else
{
lean_object* v_v_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
v_v_2377_ = lean_array_uget(v_bs_2374_, v_i_2373_);
v___x_2378_ = ((lean_object*)(l_Lean_Fmt_fmtDoLetRec___closed__3));
lean_inc(v_v_2377_);
v___x_2379_ = l_Lean_Syntax_isOfKind(v_v_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_dec(v_v_2377_);
lean_dec_ref(v_bs_2374_);
v___x_2380_ = lean_box(0);
return v___x_2380_;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2381_ = lean_unsigned_to_nat(0u);
v___x_2382_ = l_Lean_Syntax_getArg(v_v_2377_, v___x_2381_);
lean_inc(v___x_2382_);
v___x_2383_ = l_Lean_Syntax_isOfKind(v___x_2382_, v___x_2378_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; 
lean_dec(v___x_2382_);
lean_dec(v_v_2377_);
lean_dec_ref(v_bs_2374_);
v___x_2384_ = lean_box(0);
return v___x_2384_;
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v_bs_x27_2388_; lean_object* v_elseIfElseTks_2389_; lean_object* v_elseIfIfTks_2390_; lean_object* v_elseIfConds_2391_; lean_object* v_elseIfThenTks_2392_; lean_object* v_elseIfBlocks_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; size_t v___x_2398_; size_t v___x_2399_; lean_object* v___x_2400_; 
v___x_2385_ = lean_unsigned_to_nat(1u);
v___x_2386_ = lean_unsigned_to_nat(2u);
v___x_2387_ = lean_unsigned_to_nat(3u);
v_bs_x27_2388_ = lean_array_uset(v_bs_2374_, v_i_2373_, v___x_2381_);
v_elseIfElseTks_2389_ = l_Lean_Syntax_getArg(v___x_2382_, v___x_2381_);
v_elseIfIfTks_2390_ = l_Lean_Syntax_getArg(v___x_2382_, v___x_2385_);
lean_dec(v___x_2382_);
v_elseIfConds_2391_ = l_Lean_Syntax_getArg(v_v_2377_, v___x_2385_);
v_elseIfThenTks_2392_ = l_Lean_Syntax_getArg(v_v_2377_, v___x_2386_);
v_elseIfBlocks_2393_ = l_Lean_Syntax_getArg(v_v_2377_, v___x_2387_);
lean_dec(v_v_2377_);
v___x_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2394_, 0, v_elseIfThenTks_2392_);
lean_ctor_set(v___x_2394_, 1, v_elseIfBlocks_2393_);
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_elseIfConds_2391_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v_elseIfIfTks_2390_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v_elseIfElseTks_2389_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = ((size_t)1ULL);
v___x_2399_ = lean_usize_add(v_i_2373_, v___x_2398_);
v___x_2400_ = lean_array_uset(v_bs_x27_2388_, v_i_2373_, v___x_2397_);
v_i_2373_ = v___x_2399_;
v_bs_2374_ = v___x_2400_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__0___boxed(lean_object* v_sz_2402_, lean_object* v_i_2403_, lean_object* v_bs_2404_){
_start:
{
size_t v_sz_boxed_2405_; size_t v_i_boxed_2406_; lean_object* v_res_2407_; 
v_sz_boxed_2405_ = lean_unbox_usize(v_sz_2402_);
lean_dec(v_sz_2402_);
v_i_boxed_2406_ = lean_unbox_usize(v_i_2403_);
lean_dec(v_i_2403_);
v_res_2407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__0(v_sz_boxed_2405_, v_i_boxed_2406_, v_bs_2404_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtDoIf_spec__6(lean_object* v_as_2408_, size_t v_sz_2409_, size_t v_i_2410_, lean_object* v_b_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
uint8_t v___x_2414_; 
v___x_2414_ = lean_usize_dec_lt(v_i_2410_, v_sz_2409_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v_b_2411_);
lean_ctor_set(v___x_2415_, 1, v___y_2413_);
return v___x_2415_;
}
else
{
lean_object* v_snd_2416_; lean_object* v_snd_2417_; lean_object* v_snd_2418_; lean_object* v_snd_2419_; lean_object* v_fst_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2589_; 
v_snd_2416_ = lean_ctor_get(v_b_2411_, 1);
lean_inc(v_snd_2416_);
v_snd_2417_ = lean_ctor_get(v_snd_2416_, 1);
lean_inc(v_snd_2417_);
v_snd_2418_ = lean_ctor_get(v_snd_2417_, 1);
lean_inc(v_snd_2418_);
v_snd_2419_ = lean_ctor_get(v_snd_2418_, 1);
lean_inc(v_snd_2419_);
v_fst_2420_ = lean_ctor_get(v_b_2411_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_b_2411_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; 
v_unused_2590_ = lean_ctor_get(v_b_2411_, 1);
lean_dec(v_unused_2590_);
v___x_2422_ = v_b_2411_;
v_isShared_2423_ = v_isSharedCheck_2589_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_fst_2420_);
lean_dec(v_b_2411_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2589_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_fst_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2587_; 
v_fst_2424_ = lean_ctor_get(v_snd_2416_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_snd_2416_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v_snd_2416_, 1);
lean_dec(v_unused_2588_);
v___x_2426_ = v_snd_2416_;
v_isShared_2427_ = v_isSharedCheck_2587_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_fst_2424_);
lean_dec(v_snd_2416_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2587_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_fst_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2585_; 
v_fst_2428_ = lean_ctor_get(v_snd_2417_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_snd_2417_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v_snd_2417_, 1);
lean_dec(v_unused_2586_);
v___x_2430_ = v_snd_2417_;
v_isShared_2431_ = v_isSharedCheck_2585_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_fst_2428_);
lean_dec(v_snd_2417_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2585_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v_fst_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2583_; 
v_fst_2432_ = lean_ctor_get(v_snd_2418_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_snd_2418_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; 
v_unused_2584_ = lean_ctor_get(v_snd_2418_, 1);
lean_dec(v_unused_2584_);
v___x_2434_ = v_snd_2418_;
v_isShared_2435_ = v_isSharedCheck_2583_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_fst_2432_);
lean_dec(v_snd_2418_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2583_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v_array_2436_; lean_object* v_start_2437_; lean_object* v_stop_2438_; uint8_t v___x_2439_; 
v_array_2436_ = lean_ctor_get(v_snd_2419_, 0);
v_start_2437_ = lean_ctor_get(v_snd_2419_, 1);
v_stop_2438_ = lean_ctor_get(v_snd_2419_, 2);
v___x_2439_ = lean_nat_dec_lt(v_start_2437_, v_stop_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2441_; 
if (v_isShared_2435_ == 0)
{
v___x_2441_ = v___x_2434_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_fst_2432_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_snd_2419_);
v___x_2441_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2443_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 1, v___x_2441_);
v___x_2443_ = v___x_2430_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_fst_2428_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2445_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2443_);
v___x_2445_ = v___x_2426_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_fst_2424_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2447_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___x_2445_);
v___x_2447_ = v___x_2422_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_fst_2420_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___y_2413_);
return v___x_2448_;
}
}
}
}
}
else
{
lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2579_; 
lean_inc(v_stop_2438_);
lean_inc(v_start_2437_);
lean_inc_ref(v_array_2436_);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_snd_2419_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; lean_object* v_unused_2581_; lean_object* v_unused_2582_; 
v_unused_2580_ = lean_ctor_get(v_snd_2419_, 2);
lean_dec(v_unused_2580_);
v_unused_2581_ = lean_ctor_get(v_snd_2419_, 1);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_snd_2419_, 0);
lean_dec(v_unused_2582_);
v___x_2454_ = v_snd_2419_;
v_isShared_2455_ = v_isSharedCheck_2579_;
goto v_resetjp_2453_;
}
else
{
lean_dec(v_snd_2419_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2579_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v_array_2456_; lean_object* v_start_2457_; lean_object* v_stop_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2463_; 
v_array_2456_ = lean_ctor_get(v_fst_2432_, 0);
v_start_2457_ = lean_ctor_get(v_fst_2432_, 1);
v_stop_2458_ = lean_ctor_get(v_fst_2432_, 2);
v___x_2459_ = lean_array_fget(v_array_2436_, v_start_2437_);
v___x_2460_ = lean_unsigned_to_nat(1u);
v___x_2461_ = lean_nat_add(v_start_2437_, v___x_2460_);
lean_dec(v_start_2437_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 1, v___x_2461_);
v___x_2463_ = v___x_2454_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_array_2436_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_stop_2438_);
v___x_2463_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
uint8_t v___x_2464_; 
v___x_2464_ = lean_nat_dec_lt(v_start_2457_, v_stop_2458_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2466_; 
lean_dec(v___x_2459_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 1, v___x_2463_);
v___x_2466_ = v___x_2434_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_fst_2432_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2463_);
v___x_2466_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2468_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 1, v___x_2466_);
v___x_2468_ = v___x_2430_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_fst_2428_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2470_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2468_);
v___x_2470_ = v___x_2426_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_fst_2424_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2472_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___x_2470_);
v___x_2472_ = v___x_2422_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_fst_2420_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v___y_2413_);
return v___x_2473_;
}
}
}
}
}
else
{
lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2574_; 
lean_inc(v_stop_2458_);
lean_inc(v_start_2457_);
lean_inc_ref(v_array_2456_);
v_isSharedCheck_2574_ = !lean_is_exclusive(v_fst_2432_);
if (v_isSharedCheck_2574_ == 0)
{
lean_object* v_unused_2575_; lean_object* v_unused_2576_; lean_object* v_unused_2577_; 
v_unused_2575_ = lean_ctor_get(v_fst_2432_, 2);
lean_dec(v_unused_2575_);
v_unused_2576_ = lean_ctor_get(v_fst_2432_, 1);
lean_dec(v_unused_2576_);
v_unused_2577_ = lean_ctor_get(v_fst_2432_, 0);
lean_dec(v_unused_2577_);
v___x_2479_ = v_fst_2432_;
v_isShared_2480_ = v_isSharedCheck_2574_;
goto v_resetjp_2478_;
}
else
{
lean_dec(v_fst_2432_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2574_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v_array_2481_; lean_object* v_start_2482_; lean_object* v_stop_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v_array_2481_ = lean_ctor_get(v_fst_2428_, 0);
v_start_2482_ = lean_ctor_get(v_fst_2428_, 1);
v_stop_2483_ = lean_ctor_get(v_fst_2428_, 2);
v___x_2484_ = lean_array_fget(v_array_2456_, v_start_2457_);
v___x_2485_ = lean_nat_add(v_start_2457_, v___x_2460_);
lean_dec(v_start_2457_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___x_2485_);
v___x_2487_ = v___x_2479_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_array_2456_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2573_, 2, v_stop_2458_);
v___x_2487_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
uint8_t v___x_2488_; 
v___x_2488_ = lean_nat_dec_lt(v_start_2482_, v_stop_2483_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2490_; 
lean_dec(v___x_2484_);
lean_dec(v___x_2459_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 1, v___x_2463_);
lean_ctor_set(v___x_2434_, 0, v___x_2487_);
v___x_2490_ = v___x_2434_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2463_);
v___x_2490_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2492_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 1, v___x_2490_);
v___x_2492_ = v___x_2430_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_fst_2428_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2494_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2492_);
v___x_2494_ = v___x_2426_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_fst_2424_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2496_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___x_2494_);
v___x_2496_ = v___x_2422_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_fst_2420_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___y_2413_);
return v___x_2497_;
}
}
}
}
}
else
{
lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2569_; 
lean_inc(v_stop_2483_);
lean_inc(v_start_2482_);
lean_inc_ref(v_array_2481_);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_fst_2428_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; lean_object* v_unused_2571_; lean_object* v_unused_2572_; 
v_unused_2570_ = lean_ctor_get(v_fst_2428_, 2);
lean_dec(v_unused_2570_);
v_unused_2571_ = lean_ctor_get(v_fst_2428_, 1);
lean_dec(v_unused_2571_);
v_unused_2572_ = lean_ctor_get(v_fst_2428_, 0);
lean_dec(v_unused_2572_);
v___x_2503_ = v_fst_2428_;
v_isShared_2504_ = v_isSharedCheck_2569_;
goto v_resetjp_2502_;
}
else
{
lean_dec(v_fst_2428_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2569_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v_array_2505_; lean_object* v_start_2506_; lean_object* v_stop_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v_array_2505_ = lean_ctor_get(v_fst_2424_, 0);
v_start_2506_ = lean_ctor_get(v_fst_2424_, 1);
v_stop_2507_ = lean_ctor_get(v_fst_2424_, 2);
v___x_2508_ = lean_array_fget(v_array_2481_, v_start_2482_);
v___x_2509_ = lean_nat_add(v_start_2482_, v___x_2460_);
lean_dec(v_start_2482_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 1, v___x_2509_);
v___x_2511_ = v___x_2503_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_array_2481_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v_stop_2483_);
v___x_2511_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
uint8_t v___x_2512_; 
v___x_2512_ = lean_nat_dec_lt(v_start_2506_, v_stop_2507_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2514_; 
lean_dec(v___x_2508_);
lean_dec(v___x_2484_);
lean_dec(v___x_2459_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 1, v___x_2463_);
lean_ctor_set(v___x_2434_, 0, v___x_2487_);
v___x_2514_ = v___x_2434_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___x_2463_);
v___x_2514_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 1, v___x_2514_);
lean_ctor_set(v___x_2430_, 0, v___x_2511_);
v___x_2516_ = v___x_2430_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2518_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2516_);
v___x_2518_ = v___x_2426_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_fst_2424_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___x_2518_);
v___x_2520_ = v___x_2422_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_fst_2420_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v___y_2413_);
return v___x_2521_;
}
}
}
}
}
else
{
lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2564_; 
lean_inc(v_stop_2507_);
lean_inc(v_start_2506_);
lean_inc_ref(v_array_2505_);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_fst_2424_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; lean_object* v_unused_2566_; lean_object* v_unused_2567_; 
v_unused_2565_ = lean_ctor_get(v_fst_2424_, 2);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_fst_2424_, 1);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_fst_2424_, 0);
lean_dec(v_unused_2567_);
v___x_2527_ = v_fst_2424_;
v_isShared_2528_ = v_isSharedCheck_2564_;
goto v_resetjp_2526_;
}
else
{
lean_dec(v_fst_2424_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2564_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Fmt_fmt(v___x_2508_, v___y_2412_, v___y_2413_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v_a_2531_; lean_object* v_a_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
v_a_2531_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2529_, 2);
v_a_2532_ = lean_array_uget_borrowed(v_as_2408_, v_i_2410_);
v___x_2533_ = lean_array_fget(v_array_2505_, v_start_2506_);
v___x_2534_ = lean_nat_add(v_start_2506_, v___x_2460_);
lean_dec(v_start_2506_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v___x_2534_);
v___x_2536_ = v___x_2527_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_array_2505_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_stop_2507_);
v___x_2536_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_inc(v_a_2532_);
v___x_2537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2537_, 0, v_a_2532_);
lean_ctor_set(v___x_2537_, 1, v___x_2533_);
lean_ctor_set(v___x_2537_, 2, v_a_2530_);
lean_ctor_set(v___x_2537_, 3, v___x_2484_);
lean_ctor_set(v___x_2537_, 4, v___x_2459_);
v___x_2538_ = lean_array_push(v_fst_2420_, v___x_2537_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 1, v___x_2463_);
lean_ctor_set(v___x_2434_, 0, v___x_2487_);
v___x_2540_ = v___x_2434_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2463_);
v___x_2540_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2542_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 1, v___x_2540_);
lean_ctor_set(v___x_2430_, 0, v___x_2511_);
v___x_2542_ = v___x_2430_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2542_);
lean_ctor_set(v___x_2426_, 0, v___x_2536_);
v___x_2544_ = v___x_2426_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2546_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___x_2544_);
lean_ctor_set(v___x_2422_, 0, v___x_2538_);
v___x_2546_ = v___x_2422_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
size_t v___x_2547_; size_t v___x_2548_; 
v___x_2547_ = ((size_t)1ULL);
v___x_2548_ = lean_usize_add(v_i_2410_, v___x_2547_);
v_i_2410_ = v___x_2548_;
v_b_2411_ = v___x_2546_;
v___y_2413_ = v_a_2531_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_del_object(v___x_2527_);
lean_dec_ref(v___x_2511_);
lean_dec(v_stop_2507_);
lean_dec(v_start_2506_);
lean_dec_ref(v_array_2505_);
lean_dec_ref(v___x_2487_);
lean_dec(v___x_2484_);
lean_dec_ref(v___x_2463_);
lean_dec(v___x_2459_);
lean_del_object(v___x_2434_);
lean_del_object(v___x_2430_);
lean_del_object(v___x_2426_);
lean_del_object(v___x_2422_);
lean_dec(v_fst_2420_);
v_a_2555_ = lean_ctor_get(v___x_2529_, 0);
v_a_2556_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2529_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_inc(v_a_2555_);
lean_dec(v___x_2529_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2555_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_a_2556_);
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
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtDoIf_spec__6___boxed(lean_object* v_as_2591_, lean_object* v_sz_2592_, lean_object* v_i_2593_, lean_object* v_b_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
size_t v_sz_boxed_2597_; size_t v_i_boxed_2598_; lean_object* v_res_2599_; 
v_sz_boxed_2597_ = lean_unbox_usize(v_sz_2592_);
lean_dec(v_sz_2592_);
v_i_boxed_2598_ = lean_unbox_usize(v_i_2593_);
lean_dec(v_i_2593_);
v_res_2599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtDoIf_spec__6(v_as_2591_, v_sz_boxed_2597_, v_i_boxed_2598_, v_b_2594_, v___y_2595_, v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec_ref(v_as_2591_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__3(size_t v_sz_2600_, size_t v_i_2601_, lean_object* v_bs_2602_){
_start:
{
uint8_t v___x_2603_; 
v___x_2603_ = lean_usize_dec_lt(v_i_2601_, v_sz_2600_);
if (v___x_2603_ == 0)
{
return v_bs_2602_;
}
else
{
lean_object* v_v_2604_; lean_object* v_snd_2605_; lean_object* v_snd_2606_; lean_object* v_fst_2607_; lean_object* v___x_2608_; lean_object* v_bs_x27_2609_; size_t v___x_2610_; size_t v___x_2611_; lean_object* v___x_2612_; 
v_v_2604_ = lean_array_uget_borrowed(v_bs_2602_, v_i_2601_);
v_snd_2605_ = lean_ctor_get(v_v_2604_, 1);
v_snd_2606_ = lean_ctor_get(v_snd_2605_, 1);
v_fst_2607_ = lean_ctor_get(v_snd_2606_, 0);
lean_inc(v_fst_2607_);
v___x_2608_ = lean_unsigned_to_nat(0u);
v_bs_x27_2609_ = lean_array_uset(v_bs_2602_, v_i_2601_, v___x_2608_);
v___x_2610_ = ((size_t)1ULL);
v___x_2611_ = lean_usize_add(v_i_2601_, v___x_2610_);
v___x_2612_ = lean_array_uset(v_bs_x27_2609_, v_i_2601_, v_fst_2607_);
v_i_2601_ = v___x_2611_;
v_bs_2602_ = v___x_2612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__3___boxed(lean_object* v_sz_2614_, lean_object* v_i_2615_, lean_object* v_bs_2616_){
_start:
{
size_t v_sz_boxed_2617_; size_t v_i_boxed_2618_; lean_object* v_res_2619_; 
v_sz_boxed_2617_ = lean_unbox_usize(v_sz_2614_);
lean_dec(v_sz_2614_);
v_i_boxed_2618_ = lean_unbox_usize(v_i_2615_);
lean_dec(v_i_2615_);
v_res_2619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__3(v_sz_boxed_2617_, v_i_boxed_2618_, v_bs_2616_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__2(size_t v_sz_2620_, size_t v_i_2621_, lean_object* v_bs_2622_){
_start:
{
uint8_t v___x_2623_; 
v___x_2623_ = lean_usize_dec_lt(v_i_2621_, v_sz_2620_);
if (v___x_2623_ == 0)
{
return v_bs_2622_;
}
else
{
lean_object* v_v_2624_; lean_object* v_snd_2625_; lean_object* v_snd_2626_; lean_object* v_snd_2627_; lean_object* v_fst_2628_; lean_object* v___x_2629_; lean_object* v_bs_x27_2630_; size_t v___x_2631_; size_t v___x_2632_; lean_object* v___x_2633_; 
v_v_2624_ = lean_array_uget_borrowed(v_bs_2622_, v_i_2621_);
v_snd_2625_ = lean_ctor_get(v_v_2624_, 1);
v_snd_2626_ = lean_ctor_get(v_snd_2625_, 1);
v_snd_2627_ = lean_ctor_get(v_snd_2626_, 1);
v_fst_2628_ = lean_ctor_get(v_snd_2627_, 0);
lean_inc(v_fst_2628_);
v___x_2629_ = lean_unsigned_to_nat(0u);
v_bs_x27_2630_ = lean_array_uset(v_bs_2622_, v_i_2621_, v___x_2629_);
v___x_2631_ = ((size_t)1ULL);
v___x_2632_ = lean_usize_add(v_i_2621_, v___x_2631_);
v___x_2633_ = lean_array_uset(v_bs_x27_2630_, v_i_2621_, v_fst_2628_);
v_i_2621_ = v___x_2632_;
v_bs_2622_ = v___x_2633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__2___boxed(lean_object* v_sz_2635_, lean_object* v_i_2636_, lean_object* v_bs_2637_){
_start:
{
size_t v_sz_boxed_2638_; size_t v_i_boxed_2639_; lean_object* v_res_2640_; 
v_sz_boxed_2638_ = lean_unbox_usize(v_sz_2635_);
lean_dec(v_sz_2635_);
v_i_boxed_2639_ = lean_unbox_usize(v_i_2636_);
lean_dec(v_i_2636_);
v_res_2640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__2(v_sz_boxed_2638_, v_i_boxed_2639_, v_bs_2637_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__5(size_t v_sz_2641_, size_t v_i_2642_, lean_object* v_bs_2643_){
_start:
{
uint8_t v___x_2644_; 
v___x_2644_ = lean_usize_dec_lt(v_i_2642_, v_sz_2641_);
if (v___x_2644_ == 0)
{
return v_bs_2643_;
}
else
{
lean_object* v_v_2645_; lean_object* v_fst_2646_; lean_object* v___x_2647_; lean_object* v_bs_x27_2648_; size_t v___x_2649_; size_t v___x_2650_; lean_object* v___x_2651_; 
v_v_2645_ = lean_array_uget_borrowed(v_bs_2643_, v_i_2642_);
v_fst_2646_ = lean_ctor_get(v_v_2645_, 0);
lean_inc(v_fst_2646_);
v___x_2647_ = lean_unsigned_to_nat(0u);
v_bs_x27_2648_ = lean_array_uset(v_bs_2643_, v_i_2642_, v___x_2647_);
v___x_2649_ = ((size_t)1ULL);
v___x_2650_ = lean_usize_add(v_i_2642_, v___x_2649_);
v___x_2651_ = lean_array_uset(v_bs_x27_2648_, v_i_2642_, v_fst_2646_);
v_i_2642_ = v___x_2650_;
v_bs_2643_ = v___x_2651_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__5___boxed(lean_object* v_sz_2653_, lean_object* v_i_2654_, lean_object* v_bs_2655_){
_start:
{
size_t v_sz_boxed_2656_; size_t v_i_boxed_2657_; lean_object* v_res_2658_; 
v_sz_boxed_2656_ = lean_unbox_usize(v_sz_2653_);
lean_dec(v_sz_2653_);
v_i_boxed_2657_ = lean_unbox_usize(v_i_2654_);
lean_dec(v_i_2654_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__5(v_sz_boxed_2656_, v_i_boxed_2657_, v_bs_2655_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIf(lean_object* v_x_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = ((lean_object*)(l_Lean_Fmt_fmtDoIf___closed__1));
lean_inc(v_x_2667_);
v___x_2671_ = l_Lean_Syntax_isOfKind(v_x_2667_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_dec(v_x_2667_);
v___x_2672_ = lean_box(0);
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
lean_ctor_set(v___x_2673_, 1, v_a_2669_);
return v___x_2673_;
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; size_t v_sz_2677_; size_t v___x_2678_; lean_object* v___x_2679_; 
v___x_2674_ = lean_unsigned_to_nat(4u);
v___x_2675_ = l_Lean_Syntax_getArg(v_x_2667_, v___x_2674_);
v___x_2676_ = l_Lean_Syntax_getArgs(v___x_2675_);
lean_dec(v___x_2675_);
v_sz_2677_ = lean_array_size(v___x_2676_);
v___x_2678_ = ((size_t)0ULL);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__0(v_sz_2677_, v___x_2678_, v___x_2676_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_dec(v_x_2667_);
v___x_2680_ = lean_box(0);
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
lean_ctor_set(v___x_2681_, 1, v_a_2669_);
return v___x_2681_;
}
else
{
lean_object* v_val_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2777_; 
v_val_2682_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2684_ = v___x_2679_;
v_isShared_2685_ = v_isSharedCheck_2777_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_val_2682_);
lean_dec(v___x_2679_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2777_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v_ifTk_2690_; lean_object* v___x_2691_; lean_object* v_thenTk_2692_; lean_object* v___x_2693_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; size_t v_sz_2705_; lean_object* v_elseIfBlocks_2706_; lean_object* v_elseIfThenTks_2707_; lean_object* v_elseIfConds_2708_; lean_object* v_elseIfIfTks_2709_; lean_object* v_elseIfElseTks_2710_; lean_object* v_elseTk_x3f_2712_; lean_object* v_elseBody_x3f_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2686_ = lean_unsigned_to_nat(0u);
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_unsigned_to_nat(2u);
v___x_2689_ = lean_unsigned_to_nat(3u);
v_ifTk_2690_ = l_Lean_Syntax_getArg(v_x_2667_, v___x_2686_);
v___x_2691_ = l_Lean_Syntax_getArg(v_x_2667_, v___x_2687_);
v_thenTk_2692_ = l_Lean_Syntax_getArg(v_x_2667_, v___x_2688_);
v___x_2693_ = l_Lean_Syntax_getArg(v_x_2667_, v___x_2689_);
v_sz_2705_ = lean_array_size(v_val_2682_);
lean_inc_n(v_val_2682_, 4);
v_elseIfBlocks_2706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__1(v_sz_2705_, v___x_2678_, v_val_2682_);
v_elseIfThenTks_2707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__2(v_sz_2705_, v___x_2678_, v_val_2682_);
v_elseIfConds_2708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__3(v_sz_2705_, v___x_2678_, v_val_2682_);
v_elseIfIfTks_2709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__4(v_sz_2705_, v___x_2678_, v_val_2682_);
v_elseIfElseTks_2710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoIf_spec__5(v_sz_2705_, v___x_2678_, v_val_2682_);
v___x_2766_ = lean_unsigned_to_nat(5u);
v___x_2767_ = l_Lean_Syntax_getArg(v_x_2667_, v___x_2766_);
lean_dec(v_x_2667_);
v___x_2768_ = l_Lean_Syntax_isNone(v___x_2767_);
if (v___x_2768_ == 0)
{
uint8_t v___x_2769_; 
lean_inc(v___x_2767_);
v___x_2769_ = l_Lean_Syntax_matchesNull(v___x_2767_, v___x_2688_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_dec(v___x_2767_);
lean_dec_ref(v_elseIfElseTks_2710_);
lean_dec_ref(v_elseIfIfTks_2709_);
lean_dec_ref(v_elseIfConds_2708_);
lean_dec_ref(v_elseIfThenTks_2707_);
lean_dec_ref(v_elseIfBlocks_2706_);
lean_dec(v___x_2693_);
lean_dec(v_thenTk_2692_);
lean_dec(v___x_2691_);
lean_dec(v_ifTk_2690_);
lean_del_object(v___x_2684_);
v___x_2770_ = lean_box(0);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
lean_ctor_set(v___x_2771_, 1, v_a_2669_);
return v___x_2771_;
}
else
{
lean_object* v_elseTk_x3f_2772_; lean_object* v_elseBody_x3f_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_elseTk_x3f_2772_ = l_Lean_Syntax_getArg(v___x_2767_, v___x_2686_);
v_elseBody_x3f_2773_ = l_Lean_Syntax_getArg(v___x_2767_, v___x_2687_);
lean_dec(v___x_2767_);
v___x_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2774_, 0, v_elseTk_x3f_2772_);
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_elseBody_x3f_2773_);
v_elseTk_x3f_2712_ = v___x_2774_;
v_elseBody_x3f_2713_ = v___x_2775_;
v___y_2714_ = v_a_2668_;
v___y_2715_ = v_a_2669_;
goto v___jp_2711_;
}
}
else
{
lean_object* v___x_2776_; 
lean_dec(v___x_2767_);
v___x_2776_ = lean_box(0);
v_elseTk_x3f_2712_ = v___x_2776_;
v_elseBody_x3f_2713_ = v___x_2776_;
v___y_2714_ = v_a_2668_;
v___y_2715_ = v_a_2669_;
goto v___jp_2711_;
}
v___jp_2694_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2700_, 0, v_ifTk_2690_);
lean_ctor_set(v___x_2700_, 1, v___y_2697_);
lean_ctor_set(v___x_2700_, 2, v_thenTk_2692_);
lean_ctor_set(v___x_2700_, 3, v___x_2693_);
lean_ctor_set(v___x_2700_, 4, v___y_2698_);
lean_ctor_set(v___x_2700_, 5, v___y_2695_);
lean_ctor_set(v___x_2700_, 6, v___y_2699_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 0, v___x_2700_);
v___x_2702_ = v___x_2684_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v___y_2696_);
return v___x_2703_;
}
}
v___jp_2711_:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_Fmt_fmt(v___x_2691_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v_a_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; size_t v_sz_2732_; lean_object* v___x_2733_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
v_a_2718_ = lean_ctor_get(v___x_2716_, 1);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2716_, 2);
v___x_2719_ = ((lean_object*)(l_Lean_Fmt_fmtDoIf___closed__2));
v___x_2720_ = lean_array_get_size(v_elseIfIfTks_2709_);
v___x_2721_ = l_Array_toSubarray___redArg(v_elseIfIfTks_2709_, v___x_2686_, v___x_2720_);
v___x_2722_ = lean_array_get_size(v_elseIfConds_2708_);
v___x_2723_ = l_Array_toSubarray___redArg(v_elseIfConds_2708_, v___x_2686_, v___x_2722_);
v___x_2724_ = lean_array_get_size(v_elseIfThenTks_2707_);
v___x_2725_ = l_Array_toSubarray___redArg(v_elseIfThenTks_2707_, v___x_2686_, v___x_2724_);
v___x_2726_ = lean_array_get_size(v_elseIfBlocks_2706_);
v___x_2727_ = l_Array_toSubarray___redArg(v_elseIfBlocks_2706_, v___x_2686_, v___x_2726_);
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2725_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2723_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2721_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2719_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v_sz_2732_ = lean_array_size(v_elseIfElseTks_2710_);
v___x_2733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtDoIf_spec__6(v_elseIfElseTks_2710_, v_sz_2732_, v___x_2678_, v___x_2731_, v___y_2714_, v_a_2718_);
lean_dec_ref(v_elseIfElseTks_2710_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
if (lean_obj_tag(v_elseBody_x3f_2713_) == 0)
{
lean_object* v_a_2735_; lean_object* v_fst_2736_; lean_object* v___x_2737_; 
v_a_2735_ = lean_ctor_get(v___x_2733_, 1);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2733_, 2);
v_fst_2736_ = lean_ctor_get(v_a_2734_, 0);
lean_inc(v_fst_2736_);
lean_dec(v_a_2734_);
v___x_2737_ = lean_box(0);
v___y_2695_ = v_elseTk_x3f_2712_;
v___y_2696_ = v_a_2735_;
v___y_2697_ = v_a_2717_;
v___y_2698_ = v_fst_2736_;
v___y_2699_ = v___x_2737_;
goto v___jp_2694_;
}
else
{
lean_object* v_a_2738_; lean_object* v_fst_2739_; lean_object* v_val_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
v_a_2738_ = lean_ctor_get(v___x_2733_, 1);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2733_, 2);
v_fst_2739_ = lean_ctor_get(v_a_2734_, 0);
lean_inc(v_fst_2739_);
lean_dec(v_a_2734_);
v_val_2740_ = lean_ctor_get(v_elseBody_x3f_2713_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_elseBody_x3f_2713_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v_elseBody_x3f_2713_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_val_2740_);
lean_dec(v_elseBody_x3f_2713_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_val_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
v___y_2695_ = v_elseTk_x3f_2712_;
v___y_2696_ = v_a_2738_;
v___y_2697_ = v_a_2717_;
v___y_2698_ = v_fst_2739_;
v___y_2699_ = v___x_2745_;
goto v___jp_2694_;
}
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec(v_a_2717_);
lean_dec(v_elseBody_x3f_2713_);
lean_dec(v_elseTk_x3f_2712_);
lean_dec(v___x_2693_);
lean_dec(v_thenTk_2692_);
lean_dec(v_ifTk_2690_);
lean_del_object(v___x_2684_);
v_a_2748_ = lean_ctor_get(v___x_2733_, 0);
v_a_2749_ = lean_ctor_get(v___x_2733_, 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2733_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_inc(v_a_2748_);
lean_dec(v___x_2733_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2748_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_elseBody_x3f_2713_);
lean_dec(v_elseTk_x3f_2712_);
lean_dec_ref(v_elseIfElseTks_2710_);
lean_dec_ref(v_elseIfIfTks_2709_);
lean_dec_ref(v_elseIfConds_2708_);
lean_dec_ref(v_elseIfThenTks_2707_);
lean_dec_ref(v_elseIfBlocks_2706_);
lean_dec(v___x_2693_);
lean_dec(v_thenTk_2692_);
lean_dec(v_ifTk_2690_);
lean_del_object(v___x_2684_);
v_a_2757_ = lean_ctor_get(v___x_2716_, 0);
v_a_2758_ = lean_ctor_get(v___x_2716_, 1);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2716_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_inc(v_a_2757_);
lean_dec(v___x_2716_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2757_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoIf___boxed(lean_object* v_x_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lean_Fmt_fmtDoIf(v_x_2778_, v_a_2779_, v_a_2780_);
lean_dec_ref(v_a_2779_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1(){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2788_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_2789_ = ((lean_object*)(l_Lean_Fmt_fmtDoIf___closed__1));
v___x_2790_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___closed__1));
v___x_2791_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoIf___boxed), 3, 0);
v___x_2792_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2788_, v___x_2789_, v___x_2790_, v___x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1___boxed(lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1();
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnlessLike(lean_object* v_unlessTk_2801_, lean_object* v_cond_2802_, lean_object* v_doTk_2803_, lean_object* v_seq_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_Fmt_fmt(v_unlessTk_2801_, v_a_2805_, v_a_2806_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v_a_2809_; lean_object* v___x_2810_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
v_a_2809_ = lean_ctor_get(v___x_2807_, 1);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2807_, 2);
v___x_2810_ = l_Lean_Fmt_fmt(v_cond_2802_, v_a_2805_, v_a_2809_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v_a_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
v_a_2812_ = lean_ctor_get(v___x_2810_, 1);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2810_, 2);
v___x_2813_ = ((lean_object*)(l_Lean_Fmt_fmtUnlessLike___closed__0));
v___x_2814_ = l_Lean_Fmt_fmt(v_doTk_2803_, v_a_2805_, v_a_2812_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
v_a_2816_ = lean_ctor_get(v___x_2814_, 1);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2814_, 2);
v___x_2817_ = l_Lean_Fmt_fmt(v_seq_2804_, v_a_2805_, v_a_2816_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2833_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_a_2819_ = lean_ctor_get(v___x_2817_, 1);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2821_ = v___x_2817_;
v_isShared_2822_ = v_isSharedCheck_2833_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2833_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
v___x_2823_ = lean_unsigned_to_nat(2u);
v___x_2824_ = lean_mk_empty_array_with_capacity(v___x_2823_);
v___x_2825_ = lean_array_push(v___x_2824_, v_a_2808_);
v___x_2826_ = lean_array_push(v___x_2825_, v_a_2811_);
v___x_2827_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2826_, v___x_2813_);
v___x_2828_ = ((lean_object*)(l_Lean_Fmt_fmtUnlessLike___closed__1));
v___x_2829_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_2827_, v_a_2815_, v_a_2818_, v___x_2828_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2829_);
v___x_2831_ = v___x_2821_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_a_2819_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
else
{
lean_dec(v_a_2815_);
lean_dec(v_a_2811_);
lean_dec(v_a_2808_);
return v___x_2817_;
}
}
else
{
lean_dec(v_a_2811_);
lean_dec(v_a_2808_);
lean_dec(v_seq_2804_);
return v___x_2814_;
}
}
else
{
lean_dec(v_a_2808_);
lean_dec(v_seq_2804_);
lean_dec(v_doTk_2803_);
return v___x_2810_;
}
}
else
{
lean_dec(v_seq_2804_);
lean_dec(v_doTk_2803_);
lean_dec(v_cond_2802_);
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnlessLike___boxed(lean_object* v_unlessTk_2834_, lean_object* v_cond_2835_, lean_object* v_doTk_2836_, lean_object* v_seq_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_Fmt_fmtUnlessLike(v_unlessTk_2834_, v_cond_2835_, v_doTk_2836_, v_seq_2837_, v_a_2838_, v_a_2839_);
lean_dec_ref(v_a_2838_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoUnless(lean_object* v_x_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2850_ = ((lean_object*)(l_Lean_Fmt_fmtDoUnless___closed__1));
lean_inc(v_x_2847_);
v___x_2851_ = l_Lean_Syntax_isOfKind(v_x_2847_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec(v_x_2847_);
v___x_2852_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v_a_2849_);
return v___x_2853_;
}
else
{
lean_object* v___x_2854_; lean_object* v_unlessTk_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v_doTk_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2854_ = lean_unsigned_to_nat(0u);
v_unlessTk_2855_ = l_Lean_Syntax_getArg(v_x_2847_, v___x_2854_);
v___x_2856_ = lean_unsigned_to_nat(1u);
v___x_2857_ = l_Lean_Syntax_getArg(v_x_2847_, v___x_2856_);
v___x_2858_ = lean_unsigned_to_nat(2u);
v_doTk_2859_ = l_Lean_Syntax_getArg(v_x_2847_, v___x_2858_);
v___x_2860_ = lean_unsigned_to_nat(3u);
v___x_2861_ = l_Lean_Syntax_getArg(v_x_2847_, v___x_2860_);
lean_dec(v_x_2847_);
v___x_2862_ = l_Lean_Fmt_fmtUnlessLike(v_unlessTk_2855_, v___x_2857_, v_doTk_2859_, v___x_2861_, v_a_2848_, v_a_2849_);
return v___x_2862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoUnless___boxed(lean_object* v_x_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_Fmt_fmtDoUnless(v_x_2863_, v_a_2864_, v_a_2865_);
lean_dec_ref(v_a_2864_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1(){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2873_ = l_Lean_Fmt_fmtAttribute;
v___x_2874_ = ((lean_object*)(l_Lean_Fmt_fmtDoUnless___closed__1));
v___x_2875_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___closed__1));
v___x_2876_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoUnless___boxed), 3, 0);
v___x_2877_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2873_, v___x_2874_, v___x_2875_, v___x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1___boxed(lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1();
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermUnless(lean_object* v_x_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v___x_2889_; uint8_t v___x_2890_; 
v___x_2889_ = ((lean_object*)(l_Lean_Fmt_fmtTermUnless___closed__1));
lean_inc(v_x_2886_);
v___x_2890_ = l_Lean_Syntax_isOfKind(v_x_2886_, v___x_2889_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_dec(v_x_2886_);
v___x_2891_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
lean_ctor_set(v___x_2892_, 1, v_a_2888_);
return v___x_2892_;
}
else
{
lean_object* v___x_2893_; lean_object* v_unlessTk_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v_doTk_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2893_ = lean_unsigned_to_nat(0u);
v_unlessTk_2894_ = l_Lean_Syntax_getArg(v_x_2886_, v___x_2893_);
v___x_2895_ = lean_unsigned_to_nat(1u);
v___x_2896_ = l_Lean_Syntax_getArg(v_x_2886_, v___x_2895_);
v___x_2897_ = lean_unsigned_to_nat(2u);
v_doTk_2898_ = l_Lean_Syntax_getArg(v_x_2886_, v___x_2897_);
v___x_2899_ = lean_unsigned_to_nat(3u);
v___x_2900_ = l_Lean_Syntax_getArg(v_x_2886_, v___x_2899_);
lean_dec(v_x_2886_);
v___x_2901_ = l_Lean_Fmt_fmtUnlessLike(v_unlessTk_2894_, v___x_2896_, v_doTk_2898_, v___x_2900_, v_a_2887_, v_a_2888_);
return v___x_2901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermUnless___boxed(lean_object* v_x_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Fmt_fmtTermUnless(v_x_2902_, v_a_2903_, v_a_2904_);
lean_dec_ref(v_a_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1(){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2912_ = l_Lean_Fmt_fmtAttribute;
v___x_2913_ = ((lean_object*)(l_Lean_Fmt_fmtTermUnless___closed__1));
v___x_2914_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___closed__1));
v___x_2915_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermUnless___boxed), 3, 0);
v___x_2916_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2912_, v___x_2913_, v___x_2914_, v___x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1___boxed(lean_object* v_a_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1();
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoForDecl(lean_object* v_x_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v___x_2928_; uint8_t v___x_2929_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v_id_x3f_2971_; lean_object* v_colonTk_x3f_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; 
v___x_2928_ = ((lean_object*)(l_Lean_Fmt_fmtDoForDecl___closed__1));
lean_inc(v_x_2925_);
v___x_2929_ = l_Lean_Syntax_isOfKind(v_x_2925_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_dec(v_x_2925_);
v___x_2990_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set(v___x_2991_, 1, v_a_2927_);
return v___x_2991_;
}
else
{
lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2992_ = lean_unsigned_to_nat(0u);
v___x_2993_ = l_Lean_Syntax_getArg(v_x_2925_, v___x_2992_);
v___x_2994_ = l_Lean_Syntax_isNone(v___x_2993_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; uint8_t v___x_2996_; 
v___x_2995_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2993_);
v___x_2996_ = l_Lean_Syntax_matchesNull(v___x_2993_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v___x_2993_);
lean_dec(v_x_2925_);
v___x_2997_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
lean_ctor_set(v___x_2998_, 1, v_a_2927_);
return v___x_2998_;
}
else
{
lean_object* v_id_x3f_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v_id_x3f_2999_ = l_Lean_Syntax_getArg(v___x_2993_, v___x_2992_);
v___x_3000_ = ((lean_object*)(l_Lean_Fmt_fmtWithDoIdDecl___closed__4));
lean_inc(v_id_x3f_2999_);
v___x_3001_ = l_Lean_Syntax_isOfKind(v_id_x3f_2999_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec(v_id_x3f_2999_);
lean_dec(v___x_2993_);
lean_dec(v_x_2925_);
v___x_3002_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
lean_ctor_set(v___x_3003_, 1, v_a_2927_);
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; lean_object* v_colonTk_x3f_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3004_ = lean_unsigned_to_nat(1u);
v_colonTk_x3f_3005_ = l_Lean_Syntax_getArg(v___x_2993_, v___x_3004_);
lean_dec(v___x_2993_);
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_id_x3f_2999_);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_colonTk_x3f_3005_);
v_id_x3f_2971_ = v___x_3006_;
v_colonTk_x3f_2972_ = v___x_3007_;
v___y_2973_ = v_a_2926_;
v___y_2974_ = v_a_2927_;
goto v___jp_2970_;
}
}
}
else
{
lean_object* v___x_3008_; 
lean_dec(v___x_2993_);
v___x_3008_ = lean_box(0);
v_id_x3f_2971_ = v___x_3008_;
v_colonTk_x3f_2972_ = v___x_3008_;
v___y_2973_ = v_a_2926_;
v___y_2974_ = v_a_2927_;
goto v___jp_2970_;
}
}
v___jp_2930_:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Fmt_fmt_x3f(v___y_2938_, v___y_2936_, v___y_2935_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v_a_2941_; lean_object* v___x_2942_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
v_a_2941_ = lean_ctor_get(v___x_2939_, 1);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2939_, 2);
v___x_2942_ = l_Lean_Fmt_fmt_x3f(v___y_2934_, v___y_2936_, v_a_2941_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v_a_2944_; lean_object* v___x_2945_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
v_a_2944_ = lean_ctor_get(v___x_2942_, 1);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2942_, 2);
v___x_2945_ = l_Lean_Fmt_fmt(v___y_2937_, v___y_2936_, v_a_2944_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v_a_2947_; lean_object* v___x_2948_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
v_a_2947_ = lean_ctor_get(v___x_2945_, 1);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2945_, 2);
v___x_2948_ = l_Lean_Fmt_fmt(v___y_2931_, v___y_2936_, v_a_2947_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
v_a_2950_ = lean_ctor_get(v___x_2948_, 1);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2948_, 2);
v___x_2951_ = l_Lean_Fmt_fmt(v___y_2932_, v___y_2936_, v_a_2950_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2969_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_a_2953_ = lean_ctor_get(v___x_2951_, 1);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2955_ = v___x_2951_;
v_isShared_2956_ = v_isSharedCheck_2969_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2969_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
uint8_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2957_ = 0;
v___x_2958_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2958_, 0, v___x_2929_);
lean_ctor_set_uint8(v___x_2958_, 1, v___x_2957_);
lean_ctor_set_uint8(v___x_2958_, 2, v___x_2929_);
lean_ctor_set_uint8(v___x_2958_, 3, v___x_2929_);
v___x_2959_ = l_Lean_Fmt_Layouts_typeAscription(v_a_2940_, v_a_2943_, v_a_2946_, v___x_2958_);
lean_dec_ref_known(v___x_2958_, 0);
v___x_2960_ = lean_mk_empty_array_with_capacity(v___y_2933_);
v___x_2961_ = lean_array_push(v___x_2960_, v___x_2959_);
v___x_2962_ = lean_array_push(v___x_2961_, v_a_2949_);
v___x_2963_ = lean_array_push(v___x_2962_, v_a_2952_);
v___x_2964_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_2964_, 0, v___x_2929_);
lean_ctor_set_uint8(v___x_2964_, 1, v___x_2957_);
lean_ctor_set_uint8(v___x_2964_, 2, v___x_2929_);
lean_ctor_set_uint8(v___x_2964_, 3, v___x_2957_);
lean_ctor_set_uint8(v___x_2964_, 4, v___x_2957_);
v___x_2965_ = l_Lean_Fmt_Layouts_infixOperator(v___x_2963_, v___x_2964_);
lean_dec_ref_known(v___x_2964_, 0);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2965_);
v___x_2967_ = v___x_2955_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_a_2953_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
else
{
lean_dec(v_a_2949_);
lean_dec(v_a_2946_);
lean_dec(v_a_2943_);
lean_dec(v_a_2940_);
return v___x_2951_;
}
}
else
{
lean_dec(v_a_2946_);
lean_dec(v_a_2943_);
lean_dec(v_a_2940_);
lean_dec(v___y_2932_);
return v___x_2948_;
}
}
else
{
lean_dec(v_a_2943_);
lean_dec(v_a_2940_);
lean_dec(v___y_2932_);
lean_dec(v___y_2931_);
return v___x_2945_;
}
}
else
{
lean_dec(v_a_2940_);
lean_dec(v___y_2937_);
lean_dec(v___y_2932_);
lean_dec(v___y_2931_);
return v___x_2942_;
}
}
else
{
lean_dec(v___y_2937_);
lean_dec(v___y_2934_);
lean_dec(v___y_2932_);
lean_dec(v___y_2931_);
return v___x_2939_;
}
}
v___jp_2970_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v_inTk_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2975_ = lean_unsigned_to_nat(1u);
v___x_2976_ = l_Lean_Syntax_getArg(v_x_2925_, v___x_2975_);
v___x_2977_ = lean_unsigned_to_nat(2u);
v_inTk_2978_ = l_Lean_Syntax_getArg(v_x_2925_, v___x_2977_);
v___x_2979_ = lean_unsigned_to_nat(3u);
v___x_2980_ = l_Lean_Syntax_getArg(v_x_2925_, v___x_2979_);
lean_dec(v_x_2925_);
if (lean_obj_tag(v_id_x3f_2971_) == 0)
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_box(0);
v___y_2931_ = v_inTk_2978_;
v___y_2932_ = v___x_2980_;
v___y_2933_ = v___x_2979_;
v___y_2934_ = v_colonTk_x3f_2972_;
v___y_2935_ = v___y_2974_;
v___y_2936_ = v___y_2973_;
v___y_2937_ = v___x_2976_;
v___y_2938_ = v___x_2981_;
goto v___jp_2930_;
}
else
{
lean_object* v_val_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
v_val_2982_ = lean_ctor_get(v_id_x3f_2971_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_id_x3f_2971_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v_id_x3f_2971_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_val_2982_);
lean_dec(v_id_x3f_2971_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_val_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
v___y_2931_ = v_inTk_2978_;
v___y_2932_ = v___x_2980_;
v___y_2933_ = v___x_2979_;
v___y_2934_ = v_colonTk_x3f_2972_;
v___y_2935_ = v___y_2974_;
v___y_2936_ = v___y_2973_;
v___y_2937_ = v___x_2976_;
v___y_2938_ = v___x_2987_;
goto v___jp_2930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoForDecl___boxed(lean_object* v_x_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_Fmt_fmtDoForDecl(v_x_3009_, v_a_3010_, v_a_3011_);
lean_dec_ref(v_a_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1(){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3019_ = l_Lean_Fmt_fmtAttribute;
v___x_3020_ = ((lean_object*)(l_Lean_Fmt_fmtDoForDecl___closed__1));
v___x_3021_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___closed__1));
v___x_3022_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoForDecl___boxed), 3, 0);
v___x_3023_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3019_, v___x_3020_, v___x_3021_, v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1___boxed(lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1();
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoFor(lean_object* v_x_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = ((lean_object*)(l_Lean_Fmt_fmtDoFor___closed__1));
lean_inc(v_x_3033_);
v___x_3037_ = l_Lean_Syntax_isOfKind(v_x_3033_, v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_dec(v_x_3033_);
v___x_3038_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v_a_3035_);
return v___x_3039_;
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = lean_unsigned_to_nat(2u);
v___x_3042_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3041_);
v___x_3043_ = l_Lean_Syntax_matchesNull(v___x_3042_, v___x_3040_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_dec(v_x_3033_);
v___x_3044_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v_a_3035_);
return v___x_3045_;
}
else
{
lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3046_ = lean_unsigned_to_nat(3u);
v___x_3047_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3046_);
v___x_3048_ = l_Lean_Syntax_matchesNull(v___x_3047_, v___x_3040_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec(v_x_3033_);
v___x_3049_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v_a_3035_);
return v___x_3050_;
}
else
{
lean_object* v_forTk_3051_; lean_object* v___x_3052_; 
v_forTk_3051_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3040_);
v___x_3052_ = l_Lean_Fmt_fmt(v_forTk_3051_, v_a_3034_, v_a_3035_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v_a_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v_decls_3057_; lean_object* v___x_3058_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
v_a_3054_ = lean_ctor_get(v___x_3052_, 1);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3052_, 2);
v___x_3055_ = lean_unsigned_to_nat(1u);
v___x_3056_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3055_);
v_decls_3057_ = l_Lean_Syntax_getArgs(v___x_3056_);
lean_dec(v___x_3056_);
v___x_3058_ = l_Lean_Fmt_fmtTSepArray___redArg(v_decls_3057_, v_a_3034_, v_a_3054_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v_a_3060_; lean_object* v___x_3061_; lean_object* v_doTk_3062_; lean_object* v___x_3063_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
v_a_3060_ = lean_ctor_get(v___x_3058_, 1);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3058_, 2);
v___x_3061_ = lean_unsigned_to_nat(4u);
v_doTk_3062_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3061_);
v___x_3063_ = l_Lean_Fmt_fmt(v_doTk_3062_, v_a_3034_, v_a_3060_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v_a_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
v_a_3065_ = lean_ctor_get(v___x_3063_, 1);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3063_, 2);
v___x_3066_ = lean_unsigned_to_nat(5u);
v___x_3067_ = l_Lean_Syntax_getArg(v_x_3033_, v___x_3066_);
lean_dec(v_x_3033_);
v___x_3068_ = l_Lean_Fmt_fmt(v___x_3067_, v_a_3034_, v_a_3065_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3083_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_a_3070_ = lean_ctor_get(v___x_3068_, 1);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3072_ = v___x_3068_;
v_isShared_3073_ = v_isSharedCheck_3083_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3083_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; uint8_t v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3074_ = ((lean_object*)(l_Lean_Fmt_fmtDoFor___closed__2));
v___x_3075_ = 1;
v___x_3076_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v___x_3074_, v_a_3053_, v_a_3059_, v___x_3075_);
lean_dec(v_a_3059_);
v___x_3077_ = 0;
v___x_3078_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3078_, 0, v___x_3077_);
lean_ctor_set_uint8(v___x_3078_, 1, v___x_3048_);
v___x_3079_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_3076_, v_a_3064_, v_a_3069_, v___x_3078_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3079_);
v___x_3081_ = v___x_3072_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_a_3070_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
else
{
lean_dec(v_a_3064_);
lean_dec(v_a_3059_);
lean_dec(v_a_3053_);
return v___x_3068_;
}
}
else
{
lean_dec(v_a_3059_);
lean_dec(v_a_3053_);
lean_dec(v_x_3033_);
return v___x_3063_;
}
}
else
{
lean_object* v_a_3084_; lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_a_3053_);
lean_dec(v_x_3033_);
v_a_3084_ = lean_ctor_get(v___x_3058_, 0);
v_a_3085_ = lean_ctor_get(v___x_3058_, 1);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3058_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_inc(v_a_3084_);
lean_dec(v___x_3058_);
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
lean_dec(v_x_3033_);
return v___x_3052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoFor___boxed(lean_object* v_x_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_Fmt_fmtDoFor(v_x_3093_, v_a_3094_, v_a_3095_);
lean_dec_ref(v_a_3094_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1(){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3103_ = l_Lean_Fmt_fmtAttribute;
v___x_3104_ = ((lean_object*)(l_Lean_Fmt_fmtDoFor___closed__1));
v___x_3105_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___closed__1));
v___x_3106_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoFor___boxed), 3, 0);
v___x_3107_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3103_, v___x_3104_, v___x_3105_, v___x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1___boxed(lean_object* v_a_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1();
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermFor(lean_object* v_x_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_){
_start:
{
lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Lean_Fmt_fmtTermFor___closed__1));
lean_inc(v_x_3116_);
v___x_3120_ = l_Lean_Syntax_isOfKind(v_x_3116_, v___x_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_dec(v_x_3116_);
v___x_3121_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
lean_ctor_set(v___x_3122_, 1, v_a_3118_);
return v___x_3122_;
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; 
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = lean_unsigned_to_nat(2u);
v___x_3125_ = l_Lean_Syntax_getArg(v_x_3116_, v___x_3124_);
v___x_3126_ = l_Lean_Syntax_matchesNull(v___x_3125_, v___x_3123_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec(v_x_3116_);
v___x_3127_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set(v___x_3128_, 1, v_a_3118_);
return v___x_3128_;
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3129_ = lean_unsigned_to_nat(3u);
v___x_3130_ = l_Lean_Syntax_getArg(v_x_3116_, v___x_3129_);
v___x_3131_ = l_Lean_Syntax_matchesNull(v___x_3130_, v___x_3123_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec(v_x_3116_);
v___x_3132_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
lean_ctor_set(v___x_3133_, 1, v_a_3118_);
return v___x_3133_;
}
else
{
lean_object* v_forTk_3134_; lean_object* v___x_3135_; 
v_forTk_3134_ = l_Lean_Syntax_getArg(v_x_3116_, v___x_3123_);
v___x_3135_ = l_Lean_Fmt_fmt(v_forTk_3134_, v_a_3117_, v_a_3118_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v_a_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v_decls_3140_; lean_object* v___x_3141_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
v_a_3137_ = lean_ctor_get(v___x_3135_, 1);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___x_3135_, 2);
v___x_3138_ = lean_unsigned_to_nat(1u);
v___x_3139_ = l_Lean_Syntax_getArg(v_x_3116_, v___x_3138_);
v_decls_3140_ = l_Lean_Syntax_getArgs(v___x_3139_);
lean_dec(v___x_3139_);
v___x_3141_ = l_Lean_Fmt_fmtTSepArray___redArg(v_decls_3140_, v_a_3117_, v_a_3137_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v_a_3143_; lean_object* v___x_3144_; lean_object* v_doTk_3145_; lean_object* v___x_3146_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
v_a_3143_ = lean_ctor_get(v___x_3141_, 1);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3141_, 2);
v___x_3144_ = lean_unsigned_to_nat(4u);
v_doTk_3145_ = l_Lean_Syntax_getArg(v_x_3116_, v___x_3144_);
v___x_3146_ = l_Lean_Fmt_fmt(v_doTk_3145_, v_a_3117_, v_a_3143_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v_a_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
v_a_3148_ = lean_ctor_get(v___x_3146_, 1);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3146_, 2);
v___x_3149_ = lean_unsigned_to_nat(5u);
v___x_3150_ = l_Lean_Syntax_getArg(v_x_3116_, v___x_3149_);
lean_dec(v_x_3116_);
v___x_3151_ = l_Lean_Fmt_fmt(v___x_3150_, v_a_3117_, v_a_3148_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3166_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_a_3153_ = lean_ctor_get(v___x_3151_, 1);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3155_ = v___x_3151_;
v_isShared_3156_ = v_isSharedCheck_3166_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3166_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; uint8_t v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3157_ = ((lean_object*)(l_Lean_Fmt_fmtDoFor___closed__2));
v___x_3158_ = 1;
v___x_3159_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v___x_3157_, v_a_3136_, v_a_3142_, v___x_3158_);
lean_dec(v_a_3142_);
v___x_3160_ = 0;
v___x_3161_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3161_, 0, v___x_3160_);
lean_ctor_set_uint8(v___x_3161_, 1, v___x_3131_);
v___x_3162_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_3159_, v_a_3147_, v_a_3152_, v___x_3161_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3162_);
v___x_3164_ = v___x_3155_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_a_3153_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
else
{
lean_dec(v_a_3147_);
lean_dec(v_a_3142_);
lean_dec(v_a_3136_);
return v___x_3151_;
}
}
else
{
lean_dec(v_a_3142_);
lean_dec(v_a_3136_);
lean_dec(v_x_3116_);
return v___x_3146_;
}
}
else
{
lean_object* v_a_3167_; lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v_a_3136_);
lean_dec(v_x_3116_);
v_a_3167_ = lean_ctor_get(v___x_3141_, 0);
v_a_3168_ = lean_ctor_get(v___x_3141_, 1);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3141_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_inc(v_a_3167_);
lean_dec(v___x_3141_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3167_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_dec(v_x_3116_);
return v___x_3135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermFor___boxed(lean_object* v_x_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_Fmt_fmtTermFor(v_x_3176_, v_a_3177_, v_a_3178_);
lean_dec_ref(v_a_3177_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1(){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3186_ = l_Lean_Fmt_fmtAttribute;
v___x_3187_ = ((lean_object*)(l_Lean_Fmt_fmtTermFor___closed__1));
v___x_3188_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___closed__1));
v___x_3189_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermFor___boxed), 3, 0);
v___x_3190_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3186_, v___x_3187_, v___x_3188_, v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1___boxed(lean_object* v_a_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1();
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDependentParam(lean_object* v_x_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___x_3202_; uint8_t v___x_3203_; 
v___x_3202_ = ((lean_object*)(l_Lean_Fmt_fmtDependentParam___closed__1));
lean_inc(v_x_3199_);
v___x_3203_ = l_Lean_Syntax_isOfKind(v_x_3199_, v___x_3202_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
lean_dec(v_x_3199_);
v___x_3204_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
lean_ctor_set(v___x_3205_, 1, v_a_3201_);
return v___x_3205_;
}
else
{
lean_object* v___x_3206_; lean_object* v_lbTk_3207_; lean_object* v___x_3208_; lean_object* v_dependentTk_3209_; lean_object* v___x_3210_; lean_object* v_colonEqTk_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v_rbTk_3215_; lean_object* v___x_3216_; 
v___x_3206_ = lean_unsigned_to_nat(0u);
v_lbTk_3207_ = l_Lean_Syntax_getArg(v_x_3199_, v___x_3206_);
v___x_3208_ = lean_unsigned_to_nat(1u);
v_dependentTk_3209_ = l_Lean_Syntax_getArg(v_x_3199_, v___x_3208_);
v___x_3210_ = lean_unsigned_to_nat(2u);
v_colonEqTk_3211_ = l_Lean_Syntax_getArg(v_x_3199_, v___x_3210_);
v___x_3212_ = lean_unsigned_to_nat(3u);
v___x_3213_ = l_Lean_Syntax_getArg(v_x_3199_, v___x_3212_);
v___x_3214_ = lean_unsigned_to_nat(4u);
v_rbTk_3215_ = l_Lean_Syntax_getArg(v_x_3199_, v___x_3214_);
lean_dec(v_x_3199_);
v___x_3216_ = l_Lean_Fmt_fmtNamedArgumentTerm(v_lbTk_3207_, v_dependentTk_3209_, v_colonEqTk_3211_, v___x_3213_, v_rbTk_3215_, v_a_3200_, v_a_3201_);
return v___x_3216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDependentParam___boxed(lean_object* v_x_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_Fmt_fmtDependentParam(v_x_3217_, v_a_3218_, v_a_3219_);
lean_dec_ref(v_a_3218_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1(){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3227_ = l_Lean_Fmt_fmtAttribute;
v___x_3228_ = ((lean_object*)(l_Lean_Fmt_fmtDependentParam___closed__1));
v___x_3229_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___closed__1));
v___x_3230_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDependentParam___boxed), 3, 0);
v___x_3231_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3227_, v___x_3228_, v___x_3229_, v___x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1___boxed(lean_object* v_a_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1();
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoMatch(lean_object* v_x_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v___x_3263_; uint8_t v___x_3264_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; 
v___x_3263_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatch___closed__1));
lean_inc(v_x_3260_);
v___x_3264_ = l_Lean_Syntax_isOfKind(v_x_3260_, v___x_3263_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec(v_x_3260_);
v___x_3369_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
lean_ctor_set(v___x_3370_, 1, v_a_3262_);
return v___x_3370_;
}
else
{
lean_object* v___x_3371_; lean_object* v_matchTk_3372_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v_motive_x3f_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___x_3403_; lean_object* v___y_3405_; lean_object* v_generalizingParam_x3f_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v_dependentParam_x3f_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3371_ = lean_unsigned_to_nat(0u);
v_matchTk_3372_ = l_Lean_Syntax_getArg(v_x_3260_, v___x_3371_);
v___x_3403_ = lean_unsigned_to_nat(1u);
v___x_3439_ = l_Lean_Syntax_getArg(v_x_3260_, v___x_3403_);
v___x_3440_ = l_Lean_Syntax_isNone(v___x_3439_);
if (v___x_3440_ == 0)
{
uint8_t v___x_3441_; 
lean_inc(v___x_3439_);
v___x_3441_ = l_Lean_Syntax_matchesNull(v___x_3439_, v___x_3403_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec(v___x_3439_);
lean_dec(v_matchTk_3372_);
lean_dec(v_x_3260_);
v___x_3442_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
lean_ctor_set(v___x_3443_, 1, v_a_3262_);
return v___x_3443_;
}
else
{
lean_object* v_dependentParam_x3f_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v_dependentParam_x3f_3444_ = l_Lean_Syntax_getArg(v___x_3439_, v___x_3371_);
lean_dec(v___x_3439_);
v___x_3445_ = ((lean_object*)(l_Lean_Fmt_fmtDependentParam___closed__1));
lean_inc(v_dependentParam_x3f_3444_);
v___x_3446_ = l_Lean_Syntax_isOfKind(v_dependentParam_x3f_3444_, v___x_3445_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec(v_dependentParam_x3f_3444_);
lean_dec(v_matchTk_3372_);
lean_dec(v_x_3260_);
v___x_3447_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
lean_ctor_set(v___x_3448_, 1, v_a_3262_);
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; 
v___x_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3449_, 0, v_dependentParam_x3f_3444_);
v_dependentParam_x3f_3423_ = v___x_3449_;
v___y_3424_ = v_a_3261_;
v___y_3425_ = v_a_3262_;
goto v___jp_3422_;
}
}
}
else
{
lean_object* v___x_3450_; 
lean_dec(v___x_3439_);
v___x_3450_ = lean_box(0);
v_dependentParam_x3f_3423_ = v___x_3450_;
v___y_3424_ = v_a_3261_;
v___y_3425_ = v_a_3262_;
goto v___jp_3422_;
}
v___jp_3373_:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3379_ = lean_unsigned_to_nat(6u);
v___x_3380_ = l_Lean_Syntax_getArg(v_x_3260_, v___x_3379_);
v___x_3381_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatch___closed__4));
lean_inc(v___x_3380_);
v___x_3382_ = l_Lean_Syntax_isOfKind(v___x_3380_, v___x_3381_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
lean_dec(v___x_3380_);
lean_dec(v_motive_x3f_3376_);
lean_dec(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec(v_matchTk_3372_);
lean_dec(v_x_3260_);
v___x_3383_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
lean_ctor_set(v___x_3384_, 1, v___y_3378_);
return v___x_3384_;
}
else
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Fmt_fmt(v_matchTk_3372_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v_a_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v_withTk_3391_; lean_object* v___x_3392_; lean_object* v_discrs_3393_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
v_a_3387_ = lean_ctor_get(v___x_3385_, 1);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3385_, 2);
v___x_3388_ = lean_unsigned_to_nat(4u);
v___x_3389_ = l_Lean_Syntax_getArg(v_x_3260_, v___x_3388_);
v___x_3390_ = lean_unsigned_to_nat(5u);
v_withTk_3391_ = l_Lean_Syntax_getArg(v_x_3260_, v___x_3390_);
lean_dec(v_x_3260_);
v___x_3392_ = ((lean_object*)(l_Lean_Fmt_fmtDoFor___closed__2));
v_discrs_3393_ = l_Lean_Syntax_getArgs(v___x_3389_);
lean_dec(v___x_3389_);
if (lean_obj_tag(v___y_3375_) == 0)
{
lean_object* v___x_3394_; 
v___x_3394_ = lean_box(0);
v___y_3344_ = v___x_3388_;
v___y_3345_ = v_withTk_3391_;
v___y_3346_ = v_motive_x3f_3376_;
v___y_3347_ = v___x_3392_;
v___y_3348_ = v_a_3387_;
v___y_3349_ = v___y_3374_;
v___y_3350_ = v_a_3386_;
v___y_3351_ = v___x_3380_;
v___y_3352_ = v_discrs_3393_;
v___y_3353_ = v___y_3377_;
v___y_3354_ = v___x_3394_;
goto v___jp_3343_;
}
else
{
lean_object* v_val_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
v_val_3395_ = lean_ctor_get(v___y_3375_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___y_3375_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___y_3375_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_val_3395_);
lean_dec(v___y_3375_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_val_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
v___y_3344_ = v___x_3388_;
v___y_3345_ = v_withTk_3391_;
v___y_3346_ = v_motive_x3f_3376_;
v___y_3347_ = v___x_3392_;
v___y_3348_ = v_a_3387_;
v___y_3349_ = v___y_3374_;
v___y_3350_ = v_a_3386_;
v___y_3351_ = v___x_3380_;
v___y_3352_ = v_discrs_3393_;
v___y_3353_ = v___y_3377_;
v___y_3354_ = v___x_3400_;
goto v___jp_3343_;
}
}
}
}
else
{
lean_dec(v___x_3380_);
lean_dec(v_motive_x3f_3376_);
lean_dec(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec(v_x_3260_);
return v___x_3385_;
}
}
}
v___jp_3404_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3409_ = lean_unsigned_to_nat(3u);
v___x_3410_ = l_Lean_Syntax_getArg(v_x_3260_, v___x_3409_);
v___x_3411_ = l_Lean_Syntax_isNone(v___x_3410_);
if (v___x_3411_ == 0)
{
uint8_t v___x_3412_; 
lean_inc(v___x_3410_);
v___x_3412_ = l_Lean_Syntax_matchesNull(v___x_3410_, v___x_3403_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec(v___x_3410_);
lean_dec(v_generalizingParam_x3f_3406_);
lean_dec(v___y_3405_);
lean_dec(v_matchTk_3372_);
lean_dec(v_x_3260_);
v___x_3413_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set(v___x_3414_, 1, v___y_3408_);
return v___x_3414_;
}
else
{
lean_object* v_motive_x3f_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
v_motive_x3f_3415_ = l_Lean_Syntax_getArg(v___x_3410_, v___x_3371_);
lean_dec(v___x_3410_);
v___x_3416_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatch___closed__6));
lean_inc(v_motive_x3f_3415_);
v___x_3417_ = l_Lean_Syntax_isOfKind(v_motive_x3f_3415_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec(v_motive_x3f_3415_);
lean_dec(v_generalizingParam_x3f_3406_);
lean_dec(v___y_3405_);
lean_dec(v_matchTk_3372_);
lean_dec(v_x_3260_);
v___x_3418_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
lean_ctor_set(v___x_3419_, 1, v___y_3408_);
return v___x_3419_;
}
else
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3420_, 0, v_motive_x3f_3415_);
v___y_3374_ = v_generalizingParam_x3f_3406_;
v___y_3375_ = v___y_3405_;
v_motive_x3f_3376_ = v___x_3420_;
v___y_3377_ = v___y_3407_;
v___y_3378_ = v___y_3408_;
goto v___jp_3373_;
}
}
}
else
{
lean_object* v___x_3421_; 
lean_dec(v___x_3410_);
v___x_3421_ = lean_box(0);
v___y_3374_ = v_generalizingParam_x3f_3406_;
v___y_3375_ = v___y_3405_;
v_motive_x3f_3376_ = v___x_3421_;
v___y_3377_ = v___y_3407_;
v___y_3378_ = v___y_3408_;
goto v___jp_3373_;
}
}
v___jp_3422_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3426_ = lean_unsigned_to_nat(2u);
v___x_3427_ = l_Lean_Syntax_getArg(v_x_3260_, v___x_3426_);
v___x_3428_ = l_Lean_Syntax_isNone(v___x_3427_);
if (v___x_3428_ == 0)
{
uint8_t v___x_3429_; 
lean_inc(v___x_3427_);
v___x_3429_ = l_Lean_Syntax_matchesNull(v___x_3427_, v___x_3403_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
lean_dec(v___x_3427_);
lean_dec(v_dependentParam_x3f_3423_);
lean_dec(v_matchTk_3372_);
lean_dec(v_x_3260_);
v___x_3430_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
lean_ctor_set(v___x_3431_, 1, v___y_3425_);
return v___x_3431_;
}
else
{
lean_object* v_generalizingParam_x3f_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v_generalizingParam_x3f_3432_ = l_Lean_Syntax_getArg(v___x_3427_, v___x_3371_);
lean_dec(v___x_3427_);
v___x_3433_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatch___closed__8));
lean_inc(v_generalizingParam_x3f_3432_);
v___x_3434_ = l_Lean_Syntax_isOfKind(v_generalizingParam_x3f_3432_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
lean_dec(v_generalizingParam_x3f_3432_);
lean_dec(v_dependentParam_x3f_3423_);
lean_dec(v_matchTk_3372_);
lean_dec(v_x_3260_);
v___x_3435_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
lean_ctor_set(v___x_3436_, 1, v___y_3425_);
return v___x_3436_;
}
else
{
lean_object* v___x_3437_; 
v___x_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3437_, 0, v_generalizingParam_x3f_3432_);
v___y_3405_ = v_dependentParam_x3f_3423_;
v_generalizingParam_x3f_3406_ = v___x_3437_;
v___y_3407_ = v___y_3424_;
v___y_3408_ = v___y_3425_;
goto v___jp_3404_;
}
}
}
else
{
lean_object* v___x_3438_; 
lean_dec(v___x_3427_);
v___x_3438_ = lean_box(0);
v___y_3405_ = v_dependentParam_x3f_3423_;
v_generalizingParam_x3f_3406_ = v___x_3438_;
v___y_3407_ = v___y_3424_;
v___y_3408_ = v___y_3425_;
goto v___jp_3404_;
}
}
}
v___jp_3265_:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_Fmt_fmt_x3f(v___y_3276_, v___y_3275_, v___y_3270_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v_a_3279_; uint8_t v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
v_a_3279_ = lean_ctor_get(v___x_3277_, 1);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3277_, 2);
v___x_3280_ = 0;
v___x_3281_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3281_, 0, v___x_3264_);
lean_ctor_set_uint8(v___x_3281_, 1, v___x_3280_);
lean_ctor_set_uint8(v___x_3281_, 2, v___x_3280_);
lean_ctor_set_uint8(v___x_3281_, 3, v___x_3280_);
v___x_3282_ = l_Lean_Fmt_fmtTSepArray___redArg(v___y_3273_, v___y_3275_, v_a_3279_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v_a_3284_; lean_object* v___x_3285_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
v_a_3284_ = lean_ctor_get(v___x_3282_, 1);
lean_inc(v_a_3284_);
lean_dec_ref_known(v___x_3282_, 2);
v___x_3285_ = l_Lean_Fmt_fmt(v___y_3267_, v___y_3275_, v_a_3284_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v_a_3287_; lean_object* v___x_3288_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
v_a_3287_ = lean_ctor_get(v___x_3285_, 1);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3285_, 2);
v___x_3288_ = l_Lean_Fmt_fmt(v___y_3272_, v___y_3275_, v_a_3287_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3307_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_a_3290_ = lean_ctor_get(v___x_3288_, 1);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3292_ = v___x_3288_;
v_isShared_3293_ = v_isSharedCheck_3307_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3307_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3305_; 
v___x_3294_ = lean_mk_empty_array_with_capacity(v___y_3266_);
v___x_3295_ = lean_array_push(v___x_3294_, v___y_3269_);
v___x_3296_ = lean_array_push(v___x_3295_, v___y_3274_);
v___x_3297_ = lean_array_push(v___x_3296_, v___y_3271_);
v___x_3298_ = lean_array_push(v___x_3297_, v_a_3278_);
v___x_3299_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3298_, v___x_3281_);
v___x_3300_ = 1;
lean_inc_ref(v___y_3268_);
v___x_3301_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v___y_3268_, v___x_3299_, v_a_3283_, v___x_3300_);
lean_dec(v_a_3283_);
v___x_3302_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatch___closed__2));
v___x_3303_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_3301_, v_a_3286_, v_a_3289_, v___x_3302_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3303_);
v___x_3305_ = v___x_3292_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v_a_3290_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
else
{
lean_dec(v_a_3286_);
lean_dec(v_a_3283_);
lean_dec_ref_known(v___x_3281_, 0);
lean_dec(v_a_3278_);
lean_dec_ref(v___y_3274_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v___y_3269_);
return v___x_3288_;
}
}
else
{
lean_dec(v_a_3283_);
lean_dec_ref_known(v___x_3281_, 0);
lean_dec(v_a_3278_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v___y_3269_);
return v___x_3285_;
}
}
else
{
lean_object* v_a_3308_; lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref_known(v___x_3281_, 0);
lean_dec(v_a_3278_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3267_);
v_a_3308_ = lean_ctor_get(v___x_3282_, 0);
v_a_3309_ = lean_ctor_get(v___x_3282_, 1);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3282_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_inc(v_a_3308_);
lean_dec(v___x_3282_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3308_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
else
{
lean_dec_ref(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3267_);
return v___x_3277_;
}
}
v___jp_3317_:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_Fmt_fmt_x3f(v___y_3328_, v___y_3327_, v___y_3323_);
if (lean_obj_tag(v___x_3329_) == 0)
{
if (lean_obj_tag(v___y_3319_) == 0)
{
lean_object* v_a_3330_; lean_object* v_a_3331_; lean_object* v___x_3332_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
v_a_3331_ = lean_ctor_get(v___x_3329_, 1);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3329_, 2);
v___x_3332_ = lean_box(0);
v___y_3266_ = v___y_3318_;
v___y_3267_ = v___y_3320_;
v___y_3268_ = v___y_3321_;
v___y_3269_ = v___y_3322_;
v___y_3270_ = v_a_3331_;
v___y_3271_ = v_a_3330_;
v___y_3272_ = v___y_3325_;
v___y_3273_ = v___y_3324_;
v___y_3274_ = v___y_3326_;
v___y_3275_ = v___y_3327_;
v___y_3276_ = v___x_3332_;
goto v___jp_3265_;
}
else
{
lean_object* v_a_3333_; lean_object* v_a_3334_; lean_object* v_val_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
v_a_3333_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3333_);
v_a_3334_ = lean_ctor_get(v___x_3329_, 1);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___x_3329_, 2);
v_val_3335_ = lean_ctor_get(v___y_3319_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___y_3319_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___y_3319_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_val_3335_);
lean_dec(v___y_3319_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_val_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
v___y_3266_ = v___y_3318_;
v___y_3267_ = v___y_3320_;
v___y_3268_ = v___y_3321_;
v___y_3269_ = v___y_3322_;
v___y_3270_ = v_a_3334_;
v___y_3271_ = v_a_3333_;
v___y_3272_ = v___y_3325_;
v___y_3273_ = v___y_3324_;
v___y_3274_ = v___y_3326_;
v___y_3275_ = v___y_3327_;
v___y_3276_ = v___x_3340_;
goto v___jp_3265_;
}
}
}
}
else
{
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3320_);
lean_dec(v___y_3319_);
return v___x_3329_;
}
}
v___jp_3343_:
{
lean_object* v___x_3355_; 
v___x_3355_ = l_Lean_Fmt_fmt_x3f(v___y_3354_, v___y_3353_, v___y_3348_);
if (lean_obj_tag(v___x_3355_) == 0)
{
if (lean_obj_tag(v___y_3349_) == 0)
{
lean_object* v_a_3356_; lean_object* v_a_3357_; lean_object* v___x_3358_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
v_a_3357_ = lean_ctor_get(v___x_3355_, 1);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3355_, 2);
v___x_3358_ = lean_box(0);
v___y_3318_ = v___y_3344_;
v___y_3319_ = v___y_3346_;
v___y_3320_ = v___y_3345_;
v___y_3321_ = v___y_3347_;
v___y_3322_ = v___y_3350_;
v___y_3323_ = v_a_3357_;
v___y_3324_ = v___y_3352_;
v___y_3325_ = v___y_3351_;
v___y_3326_ = v_a_3356_;
v___y_3327_ = v___y_3353_;
v___y_3328_ = v___x_3358_;
goto v___jp_3317_;
}
else
{
lean_object* v_a_3359_; lean_object* v_a_3360_; lean_object* v_val_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
v_a_3359_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3359_);
v_a_3360_ = lean_ctor_get(v___x_3355_, 1);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3355_, 2);
v_val_3361_ = lean_ctor_get(v___y_3349_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___y_3349_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___y_3349_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_val_3361_);
lean_dec(v___y_3349_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_val_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
v___y_3318_ = v___y_3344_;
v___y_3319_ = v___y_3346_;
v___y_3320_ = v___y_3345_;
v___y_3321_ = v___y_3347_;
v___y_3322_ = v___y_3350_;
v___y_3323_ = v_a_3360_;
v___y_3324_ = v___y_3352_;
v___y_3325_ = v___y_3351_;
v___y_3326_ = v_a_3359_;
v___y_3327_ = v___y_3353_;
v___y_3328_ = v___x_3366_;
goto v___jp_3317_;
}
}
}
}
else
{
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
return v___x_3355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoMatch___boxed(lean_object* v_x_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_Fmt_fmtDoMatch(v_x_3451_, v_a_3452_, v_a_3453_);
lean_dec_ref(v_a_3452_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1(){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3461_ = l_Lean_Fmt_fmtAttribute;
v___x_3462_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatch___closed__1));
v___x_3463_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___closed__1));
v___x_3464_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoMatch___boxed), 3, 0);
v___x_3465_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3461_, v___x_3462_, v___x_3463_, v___x_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1___boxed(lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1();
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoMatchExpr(lean_object* v_x_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v___x_3483_; uint8_t v___x_3484_; 
v___x_3483_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatchExpr___closed__1));
lean_inc(v_x_3480_);
v___x_3484_ = l_Lean_Syntax_isOfKind(v_x_3480_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
lean_dec(v_x_3480_);
v___x_3485_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v_a_3482_);
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; lean_object* v_matchExprTk_3488_; lean_object* v_lbTk_x3f_3490_; lean_object* v_metaTk_x3f_3491_; lean_object* v_metaColonEqTk_x3f_3492_; lean_object* v_falseTk_x3f_3493_; lean_object* v_rbTk_x3f_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3487_ = lean_unsigned_to_nat(0u);
v_matchExprTk_3488_ = l_Lean_Syntax_getArg(v_x_3480_, v___x_3487_);
v___x_3540_ = lean_unsigned_to_nat(1u);
v___x_3541_ = l_Lean_Syntax_getArg(v_x_3480_, v___x_3540_);
v___x_3542_ = l_Lean_Syntax_isNone(v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; uint8_t v___x_3544_; 
v___x_3543_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_3541_);
v___x_3544_ = l_Lean_Syntax_matchesNull(v___x_3541_, v___x_3543_);
if (v___x_3544_ == 0)
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec(v___x_3541_);
lean_dec(v_matchExprTk_3488_);
lean_dec(v_x_3480_);
v___x_3545_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
lean_ctor_set(v___x_3546_, 1, v_a_3482_);
return v___x_3546_;
}
else
{
lean_object* v_lbTk_x3f_3547_; lean_object* v_metaTk_x3f_3548_; lean_object* v___x_3549_; lean_object* v_metaColonEqTk_x3f_3550_; lean_object* v___x_3551_; lean_object* v_falseTk_x3f_3552_; lean_object* v___x_3553_; lean_object* v_rbTk_x3f_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v_lbTk_x3f_3547_ = l_Lean_Syntax_getArg(v___x_3541_, v___x_3487_);
v_metaTk_x3f_3548_ = l_Lean_Syntax_getArg(v___x_3541_, v___x_3540_);
v___x_3549_ = lean_unsigned_to_nat(2u);
v_metaColonEqTk_x3f_3550_ = l_Lean_Syntax_getArg(v___x_3541_, v___x_3549_);
v___x_3551_ = lean_unsigned_to_nat(3u);
v_falseTk_x3f_3552_ = l_Lean_Syntax_getArg(v___x_3541_, v___x_3551_);
v___x_3553_ = lean_unsigned_to_nat(4u);
v_rbTk_x3f_3554_ = l_Lean_Syntax_getArg(v___x_3541_, v___x_3553_);
lean_dec(v___x_3541_);
v___x_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3555_, 0, v_lbTk_x3f_3547_);
v___x_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_metaTk_x3f_3548_);
v___x_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_metaColonEqTk_x3f_3550_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v_falseTk_x3f_3552_);
v___x_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_rbTk_x3f_3554_);
v_lbTk_x3f_3490_ = v___x_3555_;
v_metaTk_x3f_3491_ = v___x_3556_;
v_metaColonEqTk_x3f_3492_ = v___x_3557_;
v_falseTk_x3f_3493_ = v___x_3558_;
v_rbTk_x3f_3494_ = v___x_3559_;
v___y_3495_ = v_a_3481_;
v___y_3496_ = v_a_3482_;
goto v___jp_3489_;
}
}
else
{
lean_object* v___x_3560_; 
lean_dec(v___x_3541_);
v___x_3560_ = lean_box(0);
v_lbTk_x3f_3490_ = v___x_3560_;
v_metaTk_x3f_3491_ = v___x_3560_;
v_metaColonEqTk_x3f_3492_ = v___x_3560_;
v_falseTk_x3f_3493_ = v___x_3560_;
v_rbTk_x3f_3494_ = v___x_3560_;
v___y_3495_ = v_a_3481_;
v___y_3496_ = v_a_3482_;
goto v___jp_3489_;
}
v___jp_3489_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3497_ = lean_unsigned_to_nat(4u);
v___x_3498_ = l_Lean_Syntax_getArg(v_x_3480_, v___x_3497_);
v___x_3499_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatchExpr___closed__3));
lean_inc(v___x_3498_);
v___x_3500_ = l_Lean_Syntax_isOfKind(v___x_3498_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_dec(v___x_3498_);
lean_dec(v_rbTk_x3f_3494_);
lean_dec(v_falseTk_x3f_3493_);
lean_dec(v_metaColonEqTk_x3f_3492_);
lean_dec(v_metaTk_x3f_3491_);
lean_dec(v_lbTk_x3f_3490_);
lean_dec(v_matchExprTk_3488_);
lean_dec(v_x_3480_);
v___x_3501_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v___y_3496_);
return v___x_3502_;
}
else
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Fmt_fmt(v_matchExprTk_3488_, v___y_3495_, v___y_3496_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v_a_3505_; lean_object* v___x_3506_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
v_a_3505_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3503_, 2);
v___x_3506_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v_lbTk_x3f_3490_, v_metaTk_x3f_3491_, v_metaColonEqTk_x3f_3492_, v_falseTk_x3f_3493_, v_rbTk_x3f_3494_, v___y_3495_, v_a_3505_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3507_);
v_a_3508_ = lean_ctor_get(v___x_3506_, 1);
lean_inc(v_a_3508_);
lean_dec_ref_known(v___x_3506_, 2);
v___x_3509_ = lean_unsigned_to_nat(2u);
v___x_3510_ = l_Lean_Syntax_getArg(v_x_3480_, v___x_3509_);
v___x_3511_ = 0;
v___x_3512_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3512_, 0, v___x_3484_);
lean_ctor_set_uint8(v___x_3512_, 1, v___x_3511_);
lean_ctor_set_uint8(v___x_3512_, 2, v___x_3511_);
lean_ctor_set_uint8(v___x_3512_, 3, v___x_3511_);
v___x_3513_ = l_Lean_Fmt_fmt(v___x_3510_, v___y_3495_, v_a_3508_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v_a_3515_; lean_object* v___x_3516_; lean_object* v_withTk_3517_; lean_object* v___x_3518_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
v_a_3515_ = lean_ctor_get(v___x_3513_, 1);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3513_, 2);
v___x_3516_ = lean_unsigned_to_nat(3u);
v_withTk_3517_ = l_Lean_Syntax_getArg(v_x_3480_, v___x_3516_);
lean_dec(v_x_3480_);
v___x_3518_ = l_Lean_Fmt_fmt(v_withTk_3517_, v___y_3495_, v_a_3515_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v_a_3520_; lean_object* v___x_3521_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
v_a_3520_ = lean_ctor_get(v___x_3518_, 1);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3518_, 2);
v___x_3521_ = l_Lean_Fmt_fmt(v___x_3498_, v___y_3495_, v_a_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3539_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
v_a_3523_ = lean_ctor_get(v___x_3521_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3525_ = v___x_3521_;
v_isShared_3526_ = v_isSharedCheck_3539_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_inc(v_a_3522_);
lean_dec(v___x_3521_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3539_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3527_ = lean_mk_empty_array_with_capacity(v___x_3509_);
lean_inc_ref(v___x_3527_);
v___x_3528_ = lean_array_push(v___x_3527_, v_a_3504_);
v___x_3529_ = lean_array_push(v___x_3528_, v_a_3507_);
lean_inc_ref(v___x_3512_);
v___x_3530_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3529_, v___x_3512_);
v___x_3531_ = lean_array_push(v___x_3527_, v___x_3530_);
v___x_3532_ = lean_array_push(v___x_3531_, v_a_3514_);
v___x_3533_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3532_, v___x_3512_);
v___x_3534_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatch___closed__2));
v___x_3535_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_3533_, v_a_3519_, v_a_3522_, v___x_3534_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3535_);
v___x_3537_ = v___x_3525_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_a_3523_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
else
{
lean_dec(v_a_3519_);
lean_dec(v_a_3514_);
lean_dec_ref_known(v___x_3512_, 0);
lean_dec(v_a_3507_);
lean_dec(v_a_3504_);
return v___x_3521_;
}
}
else
{
lean_dec(v_a_3514_);
lean_dec_ref_known(v___x_3512_, 0);
lean_dec(v_a_3507_);
lean_dec(v_a_3504_);
lean_dec(v___x_3498_);
return v___x_3518_;
}
}
else
{
lean_dec_ref_known(v___x_3512_, 0);
lean_dec(v_a_3507_);
lean_dec(v_a_3504_);
lean_dec(v___x_3498_);
lean_dec(v_x_3480_);
return v___x_3513_;
}
}
else
{
lean_dec(v_a_3504_);
lean_dec(v___x_3498_);
lean_dec(v_x_3480_);
return v___x_3506_;
}
}
else
{
lean_dec(v___x_3498_);
lean_dec(v_rbTk_x3f_3494_);
lean_dec(v_falseTk_x3f_3493_);
lean_dec(v_metaColonEqTk_x3f_3492_);
lean_dec(v_metaTk_x3f_3491_);
lean_dec(v_lbTk_x3f_3490_);
lean_dec(v_x_3480_);
return v___x_3503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoMatchExpr___boxed(lean_object* v_x_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_Fmt_fmtDoMatchExpr(v_x_3561_, v_a_3562_, v_a_3563_);
lean_dec_ref(v_a_3562_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1(){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3571_ = l_Lean_Fmt_fmtAttribute;
v___x_3572_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatchExpr___closed__1));
v___x_3573_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___closed__1));
v___x_3574_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoMatchExpr___boxed), 3, 0);
v___x_3575_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3571_, v___x_3572_, v___x_3573_, v___x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1___boxed(lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1();
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorIdx___impl(lean_object* v_x_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = lean_obj_tag_nat(v_x_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorIdx___impl___boxed(lean_object* v_x_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorIdx___impl(v_x_3580_);
lean_dec_ref(v_x_3580_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim___redArg(lean_object* v_t_3582_, lean_object* v_k_3583_){
_start:
{
if (lean_obj_tag(v_t_3582_) == 0)
{
lean_object* v_lhsWithArrow_3584_; lean_object* v_seq_3585_; lean_object* v___x_3586_; 
v_lhsWithArrow_3584_ = lean_ctor_get(v_t_3582_, 0);
lean_inc_ref(v_lhsWithArrow_3584_);
v_seq_3585_ = lean_ctor_get(v_t_3582_, 1);
lean_inc_ref(v_seq_3585_);
lean_dec_ref_known(v_t_3582_, 2);
v___x_3586_ = lean_apply_2(v_k_3583_, v_lhsWithArrow_3584_, v_seq_3585_);
return v___x_3586_;
}
else
{
lean_object* v_doc_3587_; lean_object* v___x_3588_; 
v_doc_3587_ = lean_ctor_get(v_t_3582_, 0);
lean_inc_ref(v_doc_3587_);
lean_dec_ref_known(v_t_3582_, 1);
v___x_3588_ = lean_apply_1(v_k_3583_, v_doc_3587_);
return v___x_3588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim(lean_object* v_motive_3589_, lean_object* v_ctorIdx_3590_, lean_object* v_t_3591_, lean_object* v_h_3592_, lean_object* v_k_3593_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim___redArg(v_t_3591_, v_k_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim___boxed(lean_object* v_motive_3595_, lean_object* v_ctorIdx_3596_, lean_object* v_t_3597_, lean_object* v_h_3598_, lean_object* v_k_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim(v_motive_3595_, v_ctorIdx_3596_, v_t_3597_, v_h_3598_, v_k_3599_);
lean_dec(v_ctorIdx_3596_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_doCatch_elim___redArg(lean_object* v_t_3601_, lean_object* v_doCatch_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim___redArg(v_t_3601_, v_doCatch_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_doCatch_elim(lean_object* v_motive_3604_, lean_object* v_t_3605_, lean_object* v_h_3606_, lean_object* v_doCatch_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim___redArg(v_t_3605_, v_doCatch_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_doCatchMatch_elim___redArg(lean_object* v_t_3609_, lean_object* v_doCatchMatch_3610_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim___redArg(v_t_3609_, v_doCatchMatch_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_doCatchMatch_elim(lean_object* v_motive_3612_, lean_object* v_t_3613_, lean_object* v_h_3614_, lean_object* v_doCatchMatch_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_Handler_ctorElim___redArg(v_t_3613_, v_doCatchMatch_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_hasNewline(lean_object* v_stx_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_){
_start:
{
uint8_t v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = 0;
v___x_3621_ = l_Lean_Syntax_getPos_x3f(v_stx_3617_, v___x_3620_);
if (lean_obj_tag(v___x_3621_) == 1)
{
lean_object* v_val_3622_; lean_object* v___x_3623_; 
v_val_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_val_3622_);
lean_dec_ref_known(v___x_3621_, 1);
v___x_3623_ = l_Lean_Syntax_getTailPos_x3f(v_stx_3617_, v___x_3620_);
if (lean_obj_tag(v___x_3623_) == 1)
{
lean_object* v_val_3624_; lean_object* v___x_3625_; 
v_val_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_val_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v___x_3625_ = l_Lean_Fmt_getLineInfos(v_val_3622_, v_val_3624_, v_a_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3638_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
v_a_3627_ = lean_ctor_get(v___x_3625_, 1);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3629_ = v___x_3625_;
v_isShared_3630_ = v_isSharedCheck_3638_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_inc(v_a_3626_);
lean_dec(v___x_3625_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3638_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3636_; 
v___x_3631_ = lean_unsigned_to_nat(1u);
v___x_3632_ = lean_array_get_size(v_a_3626_);
lean_dec(v_a_3626_);
v___x_3633_ = lean_nat_dec_lt(v___x_3631_, v___x_3632_);
v___x_3634_ = lean_box(v___x_3633_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3634_);
v___x_3636_ = v___x_3629_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_a_3627_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
v_a_3639_ = lean_ctor_get(v___x_3625_, 0);
v_a_3640_ = lean_ctor_get(v___x_3625_, 1);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3625_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_inc(v_a_3639_);
lean_dec(v___x_3625_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3639_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_dec(v___x_3623_);
lean_dec(v_val_3622_);
v___x_3648_ = lean_box(v___x_3620_);
v___x_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3648_);
lean_ctor_set(v___x_3649_, 1, v_a_3619_);
return v___x_3649_;
}
}
else
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_dec(v___x_3621_);
v___x_3650_ = lean_box(v___x_3620_);
v___x_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
lean_ctor_set(v___x_3651_, 1, v_a_3619_);
return v___x_3651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_hasNewline___boxed(lean_object* v_stx_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_hasNewline(v_stx_3652_, v_a_3653_, v_a_3654_);
lean_dec_ref(v_a_3653_);
lean_dec(v_stx_3652_);
return v_res_3655_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__0));
v___x_3658_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
lean_ctor_set(v___x_3659_, 1, v___x_3657_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0(uint8_t v_allowFlattening_3660_, size_t v_sz_3661_, size_t v_i_3662_, lean_object* v_bs_3663_){
_start:
{
uint8_t v___x_3664_; 
v___x_3664_ = lean_usize_dec_lt(v_i_3662_, v_sz_3661_);
if (v___x_3664_ == 0)
{
return v_bs_3663_;
}
else
{
lean_object* v_v_3665_; lean_object* v___x_3666_; lean_object* v_bs_x27_3667_; lean_object* v___y_3669_; 
v_v_3665_ = lean_array_uget(v_bs_3663_, v_i_3662_);
v___x_3666_ = lean_unsigned_to_nat(0u);
v_bs_x27_3667_ = lean_array_uset(v_bs_3663_, v_i_3662_, v___x_3666_);
if (lean_obj_tag(v_v_3665_) == 0)
{
lean_object* v_lhsWithArrow_3674_; lean_object* v_seq_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v_lhsWithArrow_3674_ = lean_ctor_get(v_v_3665_, 0);
lean_inc_ref(v_lhsWithArrow_3674_);
v_seq_3675_ = lean_ctor_get(v_v_3665_, 1);
lean_inc_ref(v_seq_3675_);
lean_dec_ref_known(v_v_3665_, 2);
v___x_3676_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__1);
v___x_3677_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhsWithArrow_3674_, v___x_3676_, v_seq_3675_, v_allowFlattening_3660_);
v___y_3669_ = v___x_3677_;
goto v___jp_3668_;
}
else
{
lean_object* v_doc_3678_; 
v_doc_3678_ = lean_ctor_get(v_v_3665_, 0);
lean_inc_ref(v_doc_3678_);
lean_dec_ref_known(v_v_3665_, 1);
v___y_3669_ = v_doc_3678_;
goto v___jp_3668_;
}
v___jp_3668_:
{
size_t v___x_3670_; size_t v___x_3671_; lean_object* v___x_3672_; 
v___x_3670_ = ((size_t)1ULL);
v___x_3671_ = lean_usize_add(v_i_3662_, v___x_3670_);
v___x_3672_ = lean_array_uset(v_bs_x27_3667_, v_i_3662_, v___y_3669_);
v_i_3662_ = v___x_3671_;
v_bs_3663_ = v___x_3672_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___boxed(lean_object* v_allowFlattening_3679_, lean_object* v_sz_3680_, lean_object* v_i_3681_, lean_object* v_bs_3682_){
_start:
{
uint8_t v_allowFlattening_boxed_3683_; size_t v_sz_boxed_3684_; size_t v_i_boxed_3685_; lean_object* v_res_3686_; 
v_allowFlattening_boxed_3683_ = lean_unbox(v_allowFlattening_3679_);
v_sz_boxed_3684_ = lean_unbox_usize(v_sz_3680_);
lean_dec(v_sz_3680_);
v_i_boxed_3685_ = lean_unbox_usize(v_i_3681_);
lean_dec(v_i_3681_);
v_res_3686_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0(v_allowFlattening_boxed_3683_, v_sz_boxed_3684_, v_i_boxed_3685_, v_bs_3682_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___lam__0(lean_object* v___y_3687_){
_start:
{
lean_inc_ref(v___y_3687_);
return v___y_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___lam__0___boxed(lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___lam__0(v___y_3688_);
lean_dec_ref(v___y_3688_);
return v_res_3689_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___closed__1(void){
_start:
{
lean_object* v___f_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___f_3691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___closed__0));
v___x_3692_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
lean_ctor_set(v___x_3693_, 1, v___f_3691_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1(size_t v_sz_3694_, size_t v_i_3695_, lean_object* v_bs_3696_){
_start:
{
uint8_t v___x_3697_; 
v___x_3697_ = lean_usize_dec_lt(v_i_3695_, v_sz_3694_);
if (v___x_3697_ == 0)
{
return v_bs_3696_;
}
else
{
lean_object* v_v_3698_; lean_object* v___x_3699_; lean_object* v_bs_x27_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; size_t v___x_3704_; size_t v___x_3705_; lean_object* v___x_3706_; 
v_v_3698_ = lean_array_uget(v_bs_3696_, v_i_3695_);
v___x_3699_ = lean_unsigned_to_nat(0u);
v_bs_x27_3700_ = lean_array_uset(v_bs_3696_, v_i_3695_, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3701_, 0, v_v_3698_);
v___x_3702_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___closed__1);
v___x_3703_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3701_, v___x_3702_);
v___x_3704_ = ((size_t)1ULL);
v___x_3705_ = lean_usize_add(v_i_3695_, v___x_3704_);
v___x_3706_ = lean_array_uset(v_bs_x27_3700_, v_i_3695_, v___x_3703_);
v_i_3695_ = v___x_3705_;
v_bs_3696_ = v___x_3706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1___boxed(lean_object* v_sz_3708_, lean_object* v_i_3709_, lean_object* v_bs_3710_){
_start:
{
size_t v_sz_boxed_3711_; size_t v_i_boxed_3712_; lean_object* v_res_3713_; 
v_sz_boxed_3711_ = lean_unbox_usize(v_sz_3708_);
lean_dec(v_sz_3708_);
v_i_boxed_3712_ = lean_unbox_usize(v_i_3709_);
lean_dec(v_i_3709_);
v_res_3713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1(v_sz_boxed_3711_, v_i_boxed_3712_, v_bs_3710_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk(lean_object* v_tryTk_3714_, lean_object* v_trySeq_3715_, lean_object* v_handlers_3716_, lean_object* v_finallyTk_3717_, lean_object* v_finallySeq_3718_, uint8_t v_allowFlattening_3719_){
_start:
{
lean_object* v___x_3720_; lean_object* v_tryBlock_3721_; size_t v_sz_3722_; size_t v___x_3723_; lean_object* v_handlerBlocks_3724_; lean_object* v_finallyBlock_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v_blocks_3731_; size_t v_sz_3732_; lean_object* v_blocks_3733_; lean_object* v_doc_3734_; lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3720_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0___closed__1);
v_tryBlock_3721_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_tryTk_3714_, v___x_3720_, v_trySeq_3715_, v_allowFlattening_3719_);
v_sz_3722_ = lean_array_size(v_handlers_3716_);
v___x_3723_ = ((size_t)0ULL);
v_handlerBlocks_3724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__0(v_allowFlattening_3719_, v_sz_3722_, v___x_3723_, v_handlers_3716_);
v_finallyBlock_3725_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_finallyTk_3717_, v___x_3720_, v_finallySeq_3718_, v_allowFlattening_3719_);
v___x_3726_ = lean_unsigned_to_nat(1u);
v___x_3727_ = lean_mk_empty_array_with_capacity(v___x_3726_);
lean_inc_ref(v___x_3727_);
v___x_3728_ = lean_array_push(v___x_3727_, v_tryBlock_3721_);
v___x_3729_ = l_Array_append___redArg(v___x_3728_, v_handlerBlocks_3724_);
lean_dec_ref(v_handlerBlocks_3724_);
v___x_3730_ = lean_array_push(v___x_3727_, v_finallyBlock_3725_);
v_blocks_3731_ = l_Array_append___redArg(v___x_3729_, v___x_3730_);
lean_dec_ref(v___x_3730_);
v_sz_3732_ = lean_array_size(v_blocks_3731_);
v_blocks_3733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk_spec__1(v_sz_3732_, v___x_3723_, v_blocks_3731_);
v_doc_3734_ = l_Lean_Fmt_TaggedDoc_combine(v_blocks_3733_);
v___x_3735_ = lean_array_get_size(v_blocks_3733_);
lean_dec_ref(v_blocks_3733_);
v___x_3736_ = lean_nat_dec_lt(v___x_3726_, v___x_3735_);
if (v___x_3736_ == 0)
{
return v_doc_3734_;
}
else
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lean_Fmt_TaggedDoc_aligned(v_doc_3734_);
return v___x_3737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk___boxed(lean_object* v_tryTk_3738_, lean_object* v_trySeq_3739_, lean_object* v_handlers_3740_, lean_object* v_finallyTk_3741_, lean_object* v_finallySeq_3742_, lean_object* v_allowFlattening_3743_){
_start:
{
uint8_t v_allowFlattening_boxed_3744_; lean_object* v_res_3745_; 
v_allowFlattening_boxed_3744_ = lean_unbox(v_allowFlattening_3743_);
v_res_3745_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk(v_tryTk_3738_, v_trySeq_3739_, v_handlers_3740_, v_finallyTk_3741_, v_finallySeq_3742_, v_allowFlattening_boxed_3744_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0(size_t v_sz_3758_, size_t v_i_3759_, lean_object* v_bs_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
uint8_t v___x_3763_; 
v___x_3763_ = lean_usize_dec_lt(v_i_3759_, v_sz_3758_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; 
v___x_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3764_, 0, v_bs_3760_);
lean_ctor_set(v___x_3764_, 1, v___y_3762_);
return v___x_3764_;
}
else
{
lean_object* v___x_3765_; lean_object* v_v_3766_; lean_object* v___x_3767_; lean_object* v_bs_x27_3768_; lean_object* v_a_3770_; lean_object* v_a_3771_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3765_ = lean_unsigned_to_nat(1u);
v_v_3766_ = lean_array_uget(v_bs_3760_, v_i_3759_);
v___x_3767_ = lean_unsigned_to_nat(0u);
v_bs_x27_3768_ = lean_array_uset(v_bs_3760_, v_i_3759_, v___x_3767_);
v___x_3776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__1));
lean_inc(v_v_3766_);
v___x_3777_ = l_Lean_Syntax_isOfKind(v_v_3766_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; uint8_t v___x_3779_; 
v___x_3778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___closed__3));
lean_inc(v_v_3766_);
v___x_3779_ = l_Lean_Syntax_isOfKind(v_v_3766_, v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
lean_dec_ref(v_bs_x27_3768_);
lean_dec(v_v_3766_);
v___x_3780_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
lean_ctor_set(v___x_3781_, 1, v___y_3762_);
return v___x_3781_;
}
else
{
lean_object* v___x_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3782_ = l_Lean_Syntax_getArg(v_v_3766_, v___x_3765_);
v___x_3783_ = ((lean_object*)(l_Lean_Fmt_fmtDoMatch___closed__4));
lean_inc(v___x_3782_);
v___x_3784_ = l_Lean_Syntax_isOfKind(v___x_3782_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_dec(v___x_3782_);
lean_dec_ref(v_bs_x27_3768_);
lean_dec(v_v_3766_);
v___x_3785_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
lean_ctor_set(v___x_3786_, 1, v___y_3762_);
return v___x_3786_;
}
else
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = l_Lean_Syntax_getArg(v_v_3766_, v___x_3767_);
lean_dec(v_v_3766_);
v___x_3788_ = l_Lean_Fmt_fmt(v___x_3787_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v_a_3790_; lean_object* v___x_3791_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
v_a_3790_ = lean_ctor_get(v___x_3788_, 1);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3788_, 2);
v___x_3791_ = l_Lean_Fmt_fmt(v___x_3782_, v___y_3761_, v_a_3790_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v_a_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
v_a_3793_ = lean_ctor_get(v___x_3791_, 1);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3791_, 2);
v___x_3794_ = l_Lean_Fmt_Layouts_matchDeclaration(v_a_3789_, v_a_3792_);
v___x_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
v_a_3770_ = v___x_3795_;
v_a_3771_ = v_a_3793_;
goto v___jp_3769_;
}
else
{
lean_object* v_a_3796_; lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_a_3789_);
lean_dec_ref(v_bs_x27_3768_);
v_a_3796_ = lean_ctor_get(v___x_3791_, 0);
v_a_3797_ = lean_ctor_get(v___x_3791_, 1);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3791_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_inc(v_a_3796_);
lean_dec(v___x_3791_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3796_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec(v___x_3782_);
lean_dec_ref(v_bs_x27_3768_);
v_a_3805_ = lean_ctor_get(v___x_3788_, 0);
v_a_3806_ = lean_ctor_get(v___x_3788_, 1);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3788_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_inc(v_a_3805_);
lean_dec(v___x_3788_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3805_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
else
{
lean_object* v___x_3814_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v_colonTk_x3f_3876_; lean_object* v_type_x3f_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___x_3929_; uint8_t v___x_3930_; 
v___x_3814_ = lean_unsigned_to_nat(2u);
v___x_3873_ = l_Lean_Syntax_getArg(v_v_3766_, v___x_3767_);
v___x_3874_ = l_Lean_Syntax_getArg(v_v_3766_, v___x_3765_);
v___x_3929_ = l_Lean_Syntax_getArg(v_v_3766_, v___x_3814_);
v___x_3930_ = l_Lean_Syntax_isNone(v___x_3929_);
if (v___x_3930_ == 0)
{
uint8_t v___x_3931_; 
lean_inc(v___x_3929_);
v___x_3931_ = l_Lean_Syntax_matchesNull(v___x_3929_, v___x_3814_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec(v___x_3929_);
lean_dec(v___x_3874_);
lean_dec(v___x_3873_);
lean_dec_ref(v_bs_x27_3768_);
lean_dec(v_v_3766_);
v___x_3932_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
lean_ctor_set(v___x_3933_, 1, v___y_3762_);
return v___x_3933_;
}
else
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3934_ = l_Lean_Syntax_getArg(v___x_3929_, v___x_3767_);
v___x_3935_ = l_Lean_Syntax_getArg(v___x_3929_, v___x_3765_);
lean_dec(v___x_3929_);
v___x_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3934_);
v___x_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3935_);
v_colonTk_x3f_3876_ = v___x_3936_;
v_type_x3f_3877_ = v___x_3937_;
v___y_3878_ = v___y_3761_;
v___y_3879_ = v___y_3762_;
goto v___jp_3875_;
}
}
else
{
lean_object* v___x_3938_; 
lean_dec(v___x_3929_);
v___x_3938_ = lean_box(0);
v_colonTk_x3f_3876_ = v___x_3938_;
v_type_x3f_3877_ = v___x_3938_;
v___y_3878_ = v___y_3761_;
v___y_3879_ = v___y_3762_;
goto v___jp_3875_;
}
v___jp_3815_:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Lean_Fmt_fmt_x3f(v___y_3823_, v___y_3819_, v___y_3816_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v_a_3826_; lean_object* v___x_3827_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
v_a_3826_ = lean_ctor_get(v___x_3824_, 1);
lean_inc(v_a_3826_);
lean_dec_ref_known(v___x_3824_, 2);
v___x_3827_ = l_Lean_Fmt_fmt(v___y_3817_, v___y_3819_, v_a_3826_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v_a_3829_; lean_object* v___x_3830_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
v_a_3829_ = lean_ctor_get(v___x_3827_, 1);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3827_, 2);
v___x_3830_ = l_Lean_Fmt_fmt(v___y_3820_, v___y_3819_, v_a_3829_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v_a_3832_; uint8_t v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
v_a_3832_ = lean_ctor_get(v___x_3830_, 1);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___x_3830_, 2);
v___x_3833_ = 0;
v___x_3834_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3834_, 0, v___x_3777_);
lean_ctor_set_uint8(v___x_3834_, 1, v___x_3833_);
lean_ctor_set_uint8(v___x_3834_, 2, v___x_3777_);
lean_ctor_set_uint8(v___x_3834_, 3, v___x_3777_);
v___x_3835_ = l_Lean_Fmt_Layouts_typeAscription(v___y_3822_, v___y_3821_, v_a_3825_, v___x_3834_);
lean_dec_ref_known(v___x_3834_, 0);
v___x_3836_ = lean_mk_empty_array_with_capacity(v___x_3814_);
lean_inc_ref(v___x_3836_);
v___x_3837_ = lean_array_push(v___x_3836_, v___y_3818_);
v___x_3838_ = lean_array_push(v___x_3837_, v___x_3835_);
v___x_3839_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3839_, 0, v___x_3777_);
lean_ctor_set_uint8(v___x_3839_, 1, v___x_3833_);
lean_ctor_set_uint8(v___x_3839_, 2, v___x_3833_);
lean_ctor_set_uint8(v___x_3839_, 3, v___x_3833_);
v___x_3840_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3838_, v___x_3839_);
v___x_3841_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_3840_);
v___x_3842_ = lean_array_push(v___x_3836_, v___x_3841_);
v___x_3843_ = lean_array_push(v___x_3842_, v_a_3828_);
v___x_3844_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3843_);
lean_dec_ref(v___x_3843_);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
lean_ctor_set(v___x_3845_, 1, v_a_3831_);
v_a_3770_ = v___x_3845_;
v_a_3771_ = v_a_3832_;
goto v___jp_3769_;
}
else
{
lean_object* v_a_3846_; lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_dec(v_a_3828_);
lean_dec(v_a_3825_);
lean_dec_ref(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec_ref(v___y_3818_);
lean_dec_ref(v_bs_x27_3768_);
v_a_3846_ = lean_ctor_get(v___x_3830_, 0);
v_a_3847_ = lean_ctor_get(v___x_3830_, 1);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3830_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_inc(v_a_3846_);
lean_dec(v___x_3830_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3846_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec(v_a_3825_);
lean_dec_ref(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3818_);
lean_dec_ref(v_bs_x27_3768_);
v_a_3855_ = lean_ctor_get(v___x_3827_, 0);
v_a_3856_ = lean_ctor_get(v___x_3827_, 1);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3827_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_inc(v_a_3855_);
lean_dec(v___x_3827_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3855_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
else
{
lean_object* v_a_3864_; lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_dec_ref(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v_bs_x27_3768_);
v_a_3864_ = lean_ctor_get(v___x_3824_, 0);
v_a_3865_ = lean_ctor_get(v___x_3824_, 1);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3824_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_inc(v_a_3864_);
lean_dec(v___x_3824_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3864_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
v___jp_3875_:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Lean_Fmt_fmt(v___x_3873_, v___y_3878_, v___y_3879_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v_a_3882_; lean_object* v___x_3883_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
v_a_3882_ = lean_ctor_get(v___x_3880_, 1);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3880_, 2);
v___x_3883_ = l_Lean_Fmt_fmt(v___x_3874_, v___y_3878_, v_a_3882_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v_a_3885_; lean_object* v___x_3886_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
v_a_3885_ = lean_ctor_get(v___x_3883_, 1);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3883_, 2);
v___x_3886_ = l_Lean_Fmt_fmt_x3f(v_colonTk_x3f_3876_, v___y_3878_, v_a_3885_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v_a_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
v_a_3888_ = lean_ctor_get(v___x_3886_, 1);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3886_, 2);
v___x_3889_ = lean_unsigned_to_nat(3u);
v___x_3890_ = l_Lean_Syntax_getArg(v_v_3766_, v___x_3889_);
v___x_3891_ = lean_unsigned_to_nat(4u);
v___x_3892_ = l_Lean_Syntax_getArg(v_v_3766_, v___x_3891_);
lean_dec(v_v_3766_);
if (lean_obj_tag(v_type_x3f_3877_) == 0)
{
lean_object* v___x_3893_; 
v___x_3893_ = lean_box(0);
v___y_3816_ = v_a_3888_;
v___y_3817_ = v___x_3890_;
v___y_3818_ = v_a_3881_;
v___y_3819_ = v___y_3878_;
v___y_3820_ = v___x_3892_;
v___y_3821_ = v_a_3887_;
v___y_3822_ = v_a_3884_;
v___y_3823_ = v___x_3893_;
goto v___jp_3815_;
}
else
{
lean_object* v_val_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
v_val_3894_ = lean_ctor_get(v_type_x3f_3877_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_type_x3f_3877_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v_type_x3f_3877_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_val_3894_);
lean_dec(v_type_x3f_3877_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_val_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
v___y_3816_ = v_a_3888_;
v___y_3817_ = v___x_3890_;
v___y_3818_ = v_a_3881_;
v___y_3819_ = v___y_3878_;
v___y_3820_ = v___x_3892_;
v___y_3821_ = v_a_3887_;
v___y_3822_ = v_a_3884_;
v___y_3823_ = v___x_3899_;
goto v___jp_3815_;
}
}
}
}
else
{
lean_object* v_a_3902_; lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec(v_a_3884_);
lean_dec(v_a_3881_);
lean_dec(v_type_x3f_3877_);
lean_dec_ref(v_bs_x27_3768_);
lean_dec(v_v_3766_);
v_a_3902_ = lean_ctor_get(v___x_3886_, 0);
v_a_3903_ = lean_ctor_get(v___x_3886_, 1);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3886_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_inc(v_a_3902_);
lean_dec(v___x_3886_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3902_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
else
{
lean_object* v_a_3911_; lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec(v_a_3881_);
lean_dec(v_type_x3f_3877_);
lean_dec(v_colonTk_x3f_3876_);
lean_dec_ref(v_bs_x27_3768_);
lean_dec(v_v_3766_);
v_a_3911_ = lean_ctor_get(v___x_3883_, 0);
v_a_3912_ = lean_ctor_get(v___x_3883_, 1);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3883_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_inc(v_a_3911_);
lean_dec(v___x_3883_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3911_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v_a_3920_; lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec(v_type_x3f_3877_);
lean_dec(v_colonTk_x3f_3876_);
lean_dec(v___x_3874_);
lean_dec_ref(v_bs_x27_3768_);
lean_dec(v_v_3766_);
v_a_3920_ = lean_ctor_get(v___x_3880_, 0);
v_a_3921_ = lean_ctor_get(v___x_3880_, 1);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3880_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_inc(v_a_3920_);
lean_dec(v___x_3880_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3920_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
v___jp_3769_:
{
size_t v___x_3772_; size_t v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = ((size_t)1ULL);
v___x_3773_ = lean_usize_add(v_i_3759_, v___x_3772_);
v___x_3774_ = lean_array_uset(v_bs_x27_3768_, v_i_3759_, v_a_3770_);
v_i_3759_ = v___x_3773_;
v_bs_3760_ = v___x_3774_;
v___y_3762_ = v_a_3771_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0___boxed(lean_object* v_sz_3939_, lean_object* v_i_3940_, lean_object* v_bs_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
size_t v_sz_boxed_3944_; size_t v_i_boxed_3945_; lean_object* v_res_3946_; 
v_sz_boxed_3944_ = lean_unbox_usize(v_sz_3939_);
lean_dec(v_sz_3939_);
v_i_boxed_3945_ = lean_unbox_usize(v_i_3940_);
lean_dec(v_i_3940_);
v_res_3946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0(v_sz_boxed_3944_, v_i_boxed_3945_, v_bs_3941_, v___y_3942_, v___y_3943_);
lean_dec_ref(v___y_3942_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryCatchFinally(lean_object* v_stx_3953_, lean_object* v_tryTk_3954_, lean_object* v_trySeq_3955_, lean_object* v_handlers_3956_, lean_object* v_finally_x3f_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v___y_3961_; uint8_t v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; uint8_t v___y_3966_; lean_object* v_fst_3967_; lean_object* v_snd_3968_; lean_object* v___y_3969_; lean_object* v___x_3982_; lean_object* v___y_3984_; lean_object* v___y_3985_; uint8_t v___y_3986_; uint8_t v___y_3987_; lean_object* v___x_4031_; lean_object* v___x_4032_; uint8_t v___y_4034_; lean_object* v___y_4035_; 
v___x_3982_ = lean_unsigned_to_nat(1u);
v___x_4031_ = lean_array_get_size(v_handlers_3956_);
v___x_4032_ = lean_nat_add(v___x_3982_, v___x_4031_);
if (lean_obj_tag(v_finally_x3f_3957_) == 0)
{
uint8_t v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = 1;
v___x_4054_ = lean_unsigned_to_nat(0u);
v___y_4034_ = v___x_4053_;
v___y_4035_ = v___x_4054_;
goto v___jp_4033_;
}
else
{
uint8_t v___x_4055_; 
v___x_4055_ = 1;
v___y_4034_ = v___x_4055_;
v___y_4035_ = v___x_3982_;
goto v___jp_4033_;
}
v___jp_3960_:
{
if (v___y_3962_ == 0)
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3970_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk(v___y_3965_, v___y_3961_, v___y_3963_, v_fst_3967_, v_snd_3968_, v___y_3962_);
v___x_3971_ = l_Lean_Fmt_TaggedDoc_unflattenable(v___x_3970_);
v___x_3972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set(v___x_3972_, 1, v___y_3969_);
return v___x_3972_;
}
else
{
lean_object* v___x_3973_; lean_object* v___x_3974_; uint8_t v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
lean_inc_ref(v_snd_3968_);
lean_inc_ref(v_fst_3967_);
lean_inc_ref(v___y_3963_);
lean_inc_ref(v___y_3961_);
lean_inc_ref(v___y_3965_);
v___x_3973_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk(v___y_3965_, v___y_3961_, v___y_3963_, v_fst_3967_, v_snd_3968_, v___y_3966_);
v___x_3974_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3973_);
v___x_3975_ = 0;
v___x_3976_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_mk(v___y_3965_, v___y_3961_, v___y_3963_, v_fst_3967_, v_snd_3968_, v___x_3975_);
v___x_3977_ = lean_mk_empty_array_with_capacity(v___y_3964_);
v___x_3978_ = lean_array_push(v___x_3977_, v___x_3974_);
v___x_3979_ = lean_array_push(v___x_3978_, v___x_3976_);
v___x_3980_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3979_);
v___x_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
lean_ctor_set(v___x_3981_, 1, v___y_3969_);
return v___x_3981_;
}
}
v___jp_3983_:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Lean_Fmt_fmt(v_tryTk_3954_, v_a_3958_, v___y_3985_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v_a_3990_; lean_object* v___x_3991_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_a_3989_);
v_a_3990_ = lean_ctor_get(v___x_3988_, 1);
lean_inc(v_a_3990_);
lean_dec_ref_known(v___x_3988_, 2);
v___x_3991_ = l_Lean_Fmt_fmt(v_trySeq_3955_, v_a_3958_, v_a_3990_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v_a_3993_; size_t v_sz_3994_; size_t v___x_3995_; lean_object* v___x_3996_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_a_3992_);
v_a_3993_ = lean_ctor_get(v___x_3991_, 1);
lean_inc(v_a_3993_);
lean_dec_ref_known(v___x_3991_, 2);
v_sz_3994_ = lean_array_size(v_handlers_3956_);
v___x_3995_ = ((size_t)0ULL);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTryCatchFinally_spec__0(v_sz_3994_, v___x_3995_, v_handlers_3956_, v_a_3958_, v_a_3993_);
if (lean_obj_tag(v___x_3996_) == 0)
{
if (lean_obj_tag(v_finally_x3f_3957_) == 1)
{
lean_object* v_a_3997_; lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4018_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
v_a_3998_ = lean_ctor_get(v___x_3996_, 1);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4000_ = v___x_3996_;
v_isShared_4001_ = v_isSharedCheck_4018_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_inc(v_a_3997_);
lean_dec(v___x_3996_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4018_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v_val_4002_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v_val_4002_ = lean_ctor_get(v_finally_x3f_3957_, 0);
lean_inc_n(v_val_4002_, 2);
lean_dec_ref_known(v_finally_x3f_3957_, 1);
v___x_4003_ = ((lean_object*)(l_Lean_Fmt_fmtTryCatchFinally___closed__1));
v___x_4004_ = l_Lean_Syntax_isOfKind(v_val_4002_, v___x_4003_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4007_; 
lean_dec(v_val_4002_);
lean_dec(v_a_3997_);
lean_dec(v_a_3992_);
lean_dec(v_a_3989_);
v___x_4005_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4001_ == 0)
{
lean_ctor_set_tag(v___x_4000_, 1);
lean_ctor_set(v___x_4000_, 0, v___x_4005_);
v___x_4007_ = v___x_4000_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
lean_ctor_set(v_reuseFailAlloc_4008_, 1, v_a_3998_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_del_object(v___x_4000_);
v___x_4009_ = lean_unsigned_to_nat(0u);
v___x_4010_ = l_Lean_Syntax_getArg(v_val_4002_, v___x_4009_);
v___x_4011_ = l_Lean_Fmt_fmt(v___x_4010_, v_a_3958_, v_a_3998_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v_a_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
v_a_4013_ = lean_ctor_get(v___x_4011_, 1);
lean_inc(v_a_4013_);
lean_dec_ref_known(v___x_4011_, 2);
v___x_4014_ = l_Lean_Syntax_getArg(v_val_4002_, v___x_3982_);
lean_dec(v_val_4002_);
v___x_4015_ = l_Lean_Fmt_fmt(v___x_4014_, v_a_3958_, v_a_4013_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v_a_4017_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
v_a_4017_ = lean_ctor_get(v___x_4015_, 1);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___x_4015_, 2);
v___y_3961_ = v_a_3992_;
v___y_3962_ = v___y_3987_;
v___y_3963_ = v_a_3997_;
v___y_3964_ = v___y_3984_;
v___y_3965_ = v_a_3989_;
v___y_3966_ = v___y_3986_;
v_fst_3967_ = v_a_4012_;
v_snd_3968_ = v_a_4016_;
v___y_3969_ = v_a_4017_;
goto v___jp_3960_;
}
else
{
lean_dec(v_a_4012_);
lean_dec(v_a_3997_);
lean_dec(v_a_3992_);
lean_dec(v_a_3989_);
return v___x_4015_;
}
}
else
{
lean_dec(v_val_4002_);
lean_dec(v_a_3997_);
lean_dec(v_a_3992_);
lean_dec(v_a_3989_);
return v___x_4011_;
}
}
}
}
else
{
lean_object* v_a_4019_; lean_object* v_a_4020_; lean_object* v___x_4021_; 
lean_dec(v_finally_x3f_3957_);
v_a_4019_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_4019_);
v_a_4020_ = lean_ctor_get(v___x_3996_, 1);
lean_inc(v_a_4020_);
lean_dec_ref_known(v___x_3996_, 2);
v___x_4021_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_3961_ = v_a_3992_;
v___y_3962_ = v___y_3987_;
v___y_3963_ = v_a_4019_;
v___y_3964_ = v___y_3984_;
v___y_3965_ = v_a_3989_;
v___y_3966_ = v___y_3986_;
v_fst_3967_ = v___x_4021_;
v_snd_3968_ = v___x_4021_;
v___y_3969_ = v_a_4020_;
goto v___jp_3960_;
}
}
else
{
lean_object* v_a_4022_; lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec(v_a_3992_);
lean_dec(v_a_3989_);
lean_dec(v_finally_x3f_3957_);
v_a_4022_ = lean_ctor_get(v___x_3996_, 0);
v_a_4023_ = lean_ctor_get(v___x_3996_, 1);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_3996_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_inc(v_a_4022_);
lean_dec(v___x_3996_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4022_);
lean_ctor_set(v_reuseFailAlloc_4029_, 1, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_dec(v_a_3989_);
lean_dec(v_finally_x3f_3957_);
lean_dec_ref(v_handlers_3956_);
return v___x_3991_;
}
}
else
{
lean_dec(v_finally_x3f_3957_);
lean_dec_ref(v_handlers_3956_);
lean_dec(v_trySeq_3955_);
return v___x_3988_;
}
}
v___jp_4033_:
{
lean_object* v___x_4036_; 
v___x_4036_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTryCatchFinally_hasNewline(v_stx_3953_, v_a_3958_, v_a_3959_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v_a_4038_; lean_object* v_blockCount_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
v_a_4038_ = lean_ctor_get(v___x_4036_, 1);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4036_, 2);
v_blockCount_4039_ = lean_nat_add(v___x_4032_, v___y_4035_);
lean_dec(v___x_4032_);
v___x_4040_ = lean_unsigned_to_nat(2u);
v___x_4041_ = lean_nat_dec_le(v_blockCount_4039_, v___x_4040_);
lean_dec(v_blockCount_4039_);
if (v___x_4041_ == 0)
{
lean_dec(v_a_4037_);
v___y_3984_ = v___x_4040_;
v___y_3985_ = v_a_4038_;
v___y_3986_ = v___y_4034_;
v___y_3987_ = v___x_4041_;
goto v___jp_3983_;
}
else
{
uint8_t v___x_4042_; 
v___x_4042_ = lean_unbox(v_a_4037_);
lean_dec(v_a_4037_);
if (v___x_4042_ == 0)
{
v___y_3984_ = v___x_4040_;
v___y_3985_ = v_a_4038_;
v___y_3986_ = v___y_4034_;
v___y_3987_ = v___x_4041_;
goto v___jp_3983_;
}
else
{
uint8_t v___x_4043_; 
v___x_4043_ = 0;
v___y_3984_ = v___x_4040_;
v___y_3985_ = v_a_4038_;
v___y_3986_ = v___y_4034_;
v___y_3987_ = v___x_4043_;
goto v___jp_3983_;
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v___x_4032_);
lean_dec(v_finally_x3f_3957_);
lean_dec_ref(v_handlers_3956_);
lean_dec(v_trySeq_3955_);
lean_dec(v_tryTk_3954_);
v_a_4044_ = lean_ctor_get(v___x_4036_, 0);
v_a_4045_ = lean_ctor_get(v___x_4036_, 1);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4036_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_inc(v_a_4044_);
lean_dec(v___x_4036_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4044_);
lean_ctor_set(v_reuseFailAlloc_4051_, 1, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTryCatchFinally___boxed(lean_object* v_stx_4056_, lean_object* v_tryTk_4057_, lean_object* v_trySeq_4058_, lean_object* v_handlers_4059_, lean_object* v_finally_x3f_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Lean_Fmt_fmtTryCatchFinally(v_stx_4056_, v_tryTk_4057_, v_trySeq_4058_, v_handlers_4059_, v_finally_x3f_4060_, v_a_4061_, v_a_4062_);
lean_dec_ref(v_a_4061_);
lean_dec(v_stx_4056_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoTry_spec__0(size_t v_sz_4064_, size_t v_i_4065_, lean_object* v_bs_4066_){
_start:
{
uint8_t v___x_4067_; 
v___x_4067_ = lean_usize_dec_lt(v_i_4065_, v_sz_4064_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4068_; 
v___x_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4068_, 0, v_bs_4066_);
return v___x_4068_;
}
else
{
lean_object* v_v_4069_; lean_object* v___x_4070_; lean_object* v_bs_x27_4071_; size_t v___x_4072_; size_t v___x_4073_; lean_object* v___x_4074_; 
v_v_4069_ = lean_array_uget(v_bs_4066_, v_i_4065_);
v___x_4070_ = lean_unsigned_to_nat(0u);
v_bs_x27_4071_ = lean_array_uset(v_bs_4066_, v_i_4065_, v___x_4070_);
v___x_4072_ = ((size_t)1ULL);
v___x_4073_ = lean_usize_add(v_i_4065_, v___x_4072_);
v___x_4074_ = lean_array_uset(v_bs_x27_4071_, v_i_4065_, v_v_4069_);
v_i_4065_ = v___x_4073_;
v_bs_4066_ = v___x_4074_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoTry_spec__0___boxed(lean_object* v_sz_4076_, lean_object* v_i_4077_, lean_object* v_bs_4078_){
_start:
{
size_t v_sz_boxed_4079_; size_t v_i_boxed_4080_; lean_object* v_res_4081_; 
v_sz_boxed_4079_ = lean_unbox_usize(v_sz_4076_);
lean_dec(v_sz_4076_);
v_i_boxed_4080_ = lean_unbox_usize(v_i_4077_);
lean_dec(v_i_4077_);
v_res_4081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoTry_spec__0(v_sz_boxed_4079_, v_i_boxed_4080_, v_bs_4078_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoTry(lean_object* v_x_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v___x_4091_; uint8_t v___x_4092_; 
v___x_4091_ = ((lean_object*)(l_Lean_Fmt_fmtDoTry___closed__1));
lean_inc(v_x_4088_);
v___x_4092_ = l_Lean_Syntax_isOfKind(v_x_4088_, v___x_4091_);
if (v___x_4092_ == 0)
{
lean_object* v___x_4093_; lean_object* v___x_4094_; 
lean_dec(v_x_4088_);
v___x_4093_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4093_);
lean_ctor_set(v___x_4094_, 1, v_a_4090_);
return v___x_4094_;
}
else
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; size_t v_sz_4098_; size_t v___x_4099_; lean_object* v___x_4100_; 
v___x_4095_ = lean_unsigned_to_nat(2u);
v___x_4096_ = l_Lean_Syntax_getArg(v_x_4088_, v___x_4095_);
v___x_4097_ = l_Lean_Syntax_getArgs(v___x_4096_);
lean_dec(v___x_4096_);
v_sz_4098_ = lean_array_size(v___x_4097_);
v___x_4099_ = ((size_t)0ULL);
v___x_4100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoTry_spec__0(v_sz_4098_, v___x_4099_, v___x_4097_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
lean_dec(v_x_4088_);
v___x_4101_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
lean_ctor_set(v___x_4102_, 1, v_a_4090_);
return v___x_4102_;
}
else
{
lean_object* v_val_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4128_; 
v_val_4103_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4105_ = v___x_4100_;
v_isShared_4106_ = v_isSharedCheck_4128_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_val_4103_);
lean_dec(v___x_4100_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4128_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4107_; lean_object* v_tryTk_4108_; lean_object* v___x_4109_; lean_object* v_seq_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; 
v___x_4107_ = lean_unsigned_to_nat(0u);
v_tryTk_4108_ = l_Lean_Syntax_getArg(v_x_4088_, v___x_4107_);
v___x_4109_ = lean_unsigned_to_nat(1u);
v_seq_4110_ = l_Lean_Syntax_getArg(v_x_4088_, v___x_4109_);
v___x_4111_ = lean_unsigned_to_nat(3u);
v___x_4112_ = l_Lean_Syntax_getArg(v_x_4088_, v___x_4111_);
v___x_4113_ = l_Lean_Syntax_isNone(v___x_4112_);
if (v___x_4113_ == 0)
{
uint8_t v___x_4114_; 
lean_inc(v___x_4112_);
v___x_4114_ = l_Lean_Syntax_matchesNull(v___x_4112_, v___x_4109_);
if (v___x_4114_ == 0)
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
lean_dec(v___x_4112_);
lean_dec(v_seq_4110_);
lean_dec(v_tryTk_4108_);
lean_del_object(v___x_4105_);
lean_dec(v_val_4103_);
lean_dec(v_x_4088_);
v___x_4115_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
lean_ctor_set(v___x_4116_, 1, v_a_4090_);
return v___x_4116_;
}
else
{
lean_object* v_finally_x3f_4117_; lean_object* v___x_4118_; uint8_t v___x_4119_; 
v_finally_x3f_4117_ = l_Lean_Syntax_getArg(v___x_4112_, v___x_4107_);
lean_dec(v___x_4112_);
v___x_4118_ = ((lean_object*)(l_Lean_Fmt_fmtTryCatchFinally___closed__1));
lean_inc(v_finally_x3f_4117_);
v___x_4119_ = l_Lean_Syntax_isOfKind(v_finally_x3f_4117_, v___x_4118_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
lean_dec(v_finally_x3f_4117_);
lean_dec(v_seq_4110_);
lean_dec(v_tryTk_4108_);
lean_del_object(v___x_4105_);
lean_dec(v_val_4103_);
lean_dec(v_x_4088_);
v___x_4120_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
lean_ctor_set(v___x_4121_, 1, v_a_4090_);
return v___x_4121_;
}
else
{
lean_object* v___x_4123_; 
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v_finally_x3f_4117_);
v___x_4123_ = v___x_4105_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_finally_x3f_4117_);
v___x_4123_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Lean_Fmt_fmtTryCatchFinally(v_x_4088_, v_tryTk_4108_, v_seq_4110_, v_val_4103_, v___x_4123_, v_a_4089_, v_a_4090_);
lean_dec(v_x_4088_);
return v___x_4124_;
}
}
}
}
else
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_dec(v___x_4112_);
lean_del_object(v___x_4105_);
v___x_4126_ = lean_box(0);
v___x_4127_ = l_Lean_Fmt_fmtTryCatchFinally(v_x_4088_, v_tryTk_4108_, v_seq_4110_, v_val_4103_, v___x_4126_, v_a_4089_, v_a_4090_);
lean_dec(v_x_4088_);
return v___x_4127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoTry___boxed(lean_object* v_x_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Lean_Fmt_fmtDoTry(v_x_4129_, v_a_4130_, v_a_4131_);
lean_dec_ref(v_a_4130_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1(){
_start:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4139_ = l_Lean_Fmt_fmtAttribute;
v___x_4140_ = ((lean_object*)(l_Lean_Fmt_fmtDoTry___closed__1));
v___x_4141_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___closed__1));
v___x_4142_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoTry___boxed), 3, 0);
v___x_4143_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4139_, v___x_4140_, v___x_4141_, v___x_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1___boxed(lean_object* v_a_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1();
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermTry(lean_object* v_x_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v___x_4155_; uint8_t v___x_4156_; 
v___x_4155_ = ((lean_object*)(l_Lean_Fmt_fmtTermTry___closed__1));
lean_inc(v_x_4152_);
v___x_4156_ = l_Lean_Syntax_isOfKind(v_x_4152_, v___x_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_dec(v_x_4152_);
v___x_4157_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
lean_ctor_set(v___x_4158_, 1, v_a_4154_);
return v___x_4158_;
}
else
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; size_t v_sz_4162_; size_t v___x_4163_; lean_object* v___x_4164_; 
v___x_4159_ = lean_unsigned_to_nat(2u);
v___x_4160_ = l_Lean_Syntax_getArg(v_x_4152_, v___x_4159_);
v___x_4161_ = l_Lean_Syntax_getArgs(v___x_4160_);
lean_dec(v___x_4160_);
v_sz_4162_ = lean_array_size(v___x_4161_);
v___x_4163_ = ((size_t)0ULL);
v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtDoTry_spec__0(v_sz_4162_, v___x_4163_, v___x_4161_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v___x_4165_; lean_object* v___x_4166_; 
lean_dec(v_x_4152_);
v___x_4165_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
lean_ctor_set(v___x_4166_, 1, v_a_4154_);
return v___x_4166_;
}
else
{
lean_object* v_val_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4192_; 
v_val_4167_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4169_ = v___x_4164_;
v_isShared_4170_ = v_isSharedCheck_4192_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_val_4167_);
lean_dec(v___x_4164_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4192_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; lean_object* v_tryTk_4172_; lean_object* v___x_4173_; lean_object* v_seq_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; uint8_t v___x_4177_; 
v___x_4171_ = lean_unsigned_to_nat(0u);
v_tryTk_4172_ = l_Lean_Syntax_getArg(v_x_4152_, v___x_4171_);
v___x_4173_ = lean_unsigned_to_nat(1u);
v_seq_4174_ = l_Lean_Syntax_getArg(v_x_4152_, v___x_4173_);
v___x_4175_ = lean_unsigned_to_nat(3u);
v___x_4176_ = l_Lean_Syntax_getArg(v_x_4152_, v___x_4175_);
v___x_4177_ = l_Lean_Syntax_isNone(v___x_4176_);
if (v___x_4177_ == 0)
{
uint8_t v___x_4178_; 
lean_inc(v___x_4176_);
v___x_4178_ = l_Lean_Syntax_matchesNull(v___x_4176_, v___x_4173_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
lean_dec(v___x_4176_);
lean_dec(v_seq_4174_);
lean_dec(v_tryTk_4172_);
lean_del_object(v___x_4169_);
lean_dec(v_val_4167_);
lean_dec(v_x_4152_);
v___x_4179_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
lean_ctor_set(v___x_4180_, 1, v_a_4154_);
return v___x_4180_;
}
else
{
lean_object* v_finally_x3f_4181_; lean_object* v___x_4182_; uint8_t v___x_4183_; 
v_finally_x3f_4181_ = l_Lean_Syntax_getArg(v___x_4176_, v___x_4171_);
lean_dec(v___x_4176_);
v___x_4182_ = ((lean_object*)(l_Lean_Fmt_fmtTryCatchFinally___closed__1));
lean_inc(v_finally_x3f_4181_);
v___x_4183_ = l_Lean_Syntax_isOfKind(v_finally_x3f_4181_, v___x_4182_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_dec(v_finally_x3f_4181_);
lean_dec(v_seq_4174_);
lean_dec(v_tryTk_4172_);
lean_del_object(v___x_4169_);
lean_dec(v_val_4167_);
lean_dec(v_x_4152_);
v___x_4184_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
lean_ctor_set(v___x_4185_, 1, v_a_4154_);
return v___x_4185_;
}
else
{
lean_object* v___x_4187_; 
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v_finally_x3f_4181_);
v___x_4187_ = v___x_4169_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_finally_x3f_4181_);
v___x_4187_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
lean_object* v___x_4188_; 
v___x_4188_ = l_Lean_Fmt_fmtTryCatchFinally(v_x_4152_, v_tryTk_4172_, v_seq_4174_, v_val_4167_, v___x_4187_, v_a_4153_, v_a_4154_);
lean_dec(v_x_4152_);
return v___x_4188_;
}
}
}
}
else
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
lean_dec(v___x_4176_);
lean_del_object(v___x_4169_);
v___x_4190_ = lean_box(0);
v___x_4191_ = l_Lean_Fmt_fmtTryCatchFinally(v_x_4152_, v_tryTk_4172_, v_seq_4174_, v_val_4167_, v___x_4190_, v_a_4153_, v_a_4154_);
lean_dec(v_x_4152_);
return v___x_4191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermTry___boxed(lean_object* v_x_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Lean_Fmt_fmtTermTry(v_x_4193_, v_a_4194_, v_a_4195_);
lean_dec_ref(v_a_4194_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1(){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4203_ = l_Lean_Fmt_fmtAttribute;
v___x_4204_ = ((lean_object*)(l_Lean_Fmt_fmtTermTry___closed__1));
v___x_4205_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___closed__1));
v___x_4206_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermTry___boxed), 3, 0);
v___x_4207_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4203_, v___x_4204_, v___x_4205_, v___x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1___boxed(lean_object* v_a_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1();
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoForward(lean_object* v_x_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4219_ = ((lean_object*)(l_Lean_Fmt_fmtDoForward___closed__1));
lean_inc(v_x_4216_);
v___x_4220_ = l_Lean_Syntax_isOfKind(v_x_4216_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
lean_dec(v_x_4216_);
v___x_4221_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4221_);
lean_ctor_set(v___x_4222_, 1, v_a_4218_);
return v___x_4222_;
}
else
{
lean_object* v___x_4223_; lean_object* v_doTk_4224_; lean_object* v___x_4225_; 
v___x_4223_ = lean_unsigned_to_nat(0u);
v_doTk_4224_ = l_Lean_Syntax_getArg(v_x_4216_, v___x_4223_);
v___x_4225_ = l_Lean_Fmt_fmt(v_doTk_4224_, v_a_4217_, v_a_4218_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v_a_4227_; lean_object* v___x_4228_; lean_object* v_leftArrowTk_4229_; lean_object* v___x_4230_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
v_a_4227_ = lean_ctor_get(v___x_4225_, 1);
lean_inc(v_a_4227_);
lean_dec_ref_known(v___x_4225_, 2);
v___x_4228_ = lean_unsigned_to_nat(1u);
v_leftArrowTk_4229_ = l_Lean_Syntax_getArg(v_x_4216_, v___x_4228_);
v___x_4230_ = l_Lean_Fmt_fmt(v_leftArrowTk_4229_, v_a_4217_, v_a_4227_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; lean_object* v_a_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
lean_inc(v_a_4231_);
v_a_4232_ = lean_ctor_get(v___x_4230_, 1);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4230_, 2);
v___x_4233_ = lean_unsigned_to_nat(2u);
v___x_4234_ = l_Lean_Syntax_getArg(v_x_4216_, v___x_4233_);
lean_dec(v_x_4216_);
v___x_4235_ = l_Lean_Fmt_fmt(v___x_4234_, v_a_4217_, v_a_4232_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4250_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
v_a_4237_ = lean_ctor_get(v___x_4235_, 1);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4239_ = v___x_4235_;
v_isShared_4240_ = v_isSharedCheck_4250_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_inc(v_a_4236_);
lean_dec(v___x_4235_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4250_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; uint8_t v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4248_; 
v___x_4241_ = lean_mk_empty_array_with_capacity(v___x_4233_);
v___x_4242_ = lean_array_push(v___x_4241_, v_a_4226_);
v___x_4243_ = lean_array_push(v___x_4242_, v_a_4231_);
v___x_4244_ = l_Lean_Fmt_Layouts_atomic(v___x_4243_);
lean_dec_ref(v___x_4243_);
v___x_4245_ = 0;
v___x_4246_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v___x_4244_, v_a_4236_, v___x_4245_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4246_);
v___x_4248_ = v___x_4239_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_a_4237_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
else
{
lean_dec(v_a_4231_);
lean_dec(v_a_4226_);
return v___x_4235_;
}
}
else
{
lean_dec(v_a_4226_);
lean_dec(v_x_4216_);
return v___x_4230_;
}
}
else
{
lean_dec(v_x_4216_);
return v___x_4225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoForward___boxed(lean_object* v_x_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_Fmt_fmtDoForward(v_x_4251_, v_a_4252_, v_a_4253_);
lean_dec_ref(v_a_4252_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1(){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4261_ = l_Lean_Fmt_fmtAttribute;
v___x_4262_ = ((lean_object*)(l_Lean_Fmt_fmtDoForward___closed__1));
v___x_4263_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___closed__1));
v___x_4264_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoForward___boxed), 3, 0);
v___x_4265_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4261_, v___x_4262_, v___x_4263_, v___x_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1___boxed(lean_object* v_a_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1();
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoWhile(lean_object* v_x_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v___x_4277_; uint8_t v___x_4278_; 
v___x_4277_ = ((lean_object*)(l_Lean_Fmt_fmtDoWhile___closed__1));
lean_inc(v_x_4274_);
v___x_4278_ = l_Lean_Syntax_isOfKind(v_x_4274_, v___x_4277_);
if (v___x_4278_ == 0)
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
lean_dec(v_x_4274_);
v___x_4279_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
lean_ctor_set(v___x_4280_, 1, v_a_4276_);
return v___x_4280_;
}
else
{
lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; uint8_t v___x_4284_; 
v___x_4281_ = lean_unsigned_to_nat(0u);
v___x_4282_ = lean_unsigned_to_nat(2u);
v___x_4283_ = l_Lean_Syntax_getArg(v_x_4274_, v___x_4282_);
v___x_4284_ = l_Lean_Syntax_matchesNull(v___x_4283_, v___x_4281_);
if (v___x_4284_ == 0)
{
lean_object* v___x_4285_; lean_object* v___x_4286_; 
lean_dec(v_x_4274_);
v___x_4285_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
lean_ctor_set(v___x_4286_, 1, v_a_4276_);
return v___x_4286_;
}
else
{
lean_object* v___x_4287_; lean_object* v___x_4288_; uint8_t v___x_4289_; 
v___x_4287_ = lean_unsigned_to_nat(3u);
v___x_4288_ = l_Lean_Syntax_getArg(v_x_4274_, v___x_4287_);
v___x_4289_ = l_Lean_Syntax_matchesNull(v___x_4288_, v___x_4281_);
if (v___x_4289_ == 0)
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
lean_dec(v_x_4274_);
v___x_4290_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
lean_ctor_set(v___x_4291_, 1, v_a_4276_);
return v___x_4291_;
}
else
{
lean_object* v_whileTk_4292_; lean_object* v___x_4293_; 
v_whileTk_4292_ = l_Lean_Syntax_getArg(v_x_4274_, v___x_4281_);
v___x_4293_ = l_Lean_Fmt_fmt(v_whileTk_4292_, v_a_4275_, v_a_4276_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; lean_object* v_a_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
v_a_4295_ = lean_ctor_get(v___x_4293_, 1);
lean_inc(v_a_4295_);
lean_dec_ref_known(v___x_4293_, 2);
v___x_4296_ = lean_unsigned_to_nat(1u);
v___x_4297_ = l_Lean_Syntax_getArg(v_x_4274_, v___x_4296_);
v___x_4298_ = l_Lean_Fmt_fmt(v___x_4297_, v_a_4275_, v_a_4295_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v_a_4300_; lean_object* v___x_4301_; lean_object* v_doTk_4302_; uint8_t v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
v_a_4300_ = lean_ctor_get(v___x_4298_, 1);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4298_, 2);
v___x_4301_ = lean_unsigned_to_nat(4u);
v_doTk_4302_ = l_Lean_Syntax_getArg(v_x_4274_, v___x_4301_);
v___x_4303_ = 0;
v___x_4304_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4304_, 0, v___x_4289_);
lean_ctor_set_uint8(v___x_4304_, 1, v___x_4303_);
lean_ctor_set_uint8(v___x_4304_, 2, v___x_4303_);
lean_ctor_set_uint8(v___x_4304_, 3, v___x_4303_);
v___x_4305_ = l_Lean_Fmt_fmt(v_doTk_4302_, v_a_4275_, v_a_4300_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v_a_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4306_);
v_a_4307_ = lean_ctor_get(v___x_4305_, 1);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4305_, 2);
v___x_4308_ = lean_unsigned_to_nat(5u);
v___x_4309_ = l_Lean_Syntax_getArg(v_x_4274_, v___x_4308_);
lean_dec(v_x_4274_);
v___x_4310_ = l_Lean_Fmt_fmt(v___x_4309_, v_a_4275_, v_a_4307_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4325_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
v_a_4312_ = lean_ctor_get(v___x_4310_, 1);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4314_ = v___x_4310_;
v_isShared_4315_ = v_isSharedCheck_4325_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_inc(v_a_4311_);
lean_dec(v___x_4310_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4325_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4323_; 
v___x_4316_ = lean_mk_empty_array_with_capacity(v___x_4282_);
v___x_4317_ = lean_array_push(v___x_4316_, v_a_4294_);
v___x_4318_ = lean_array_push(v___x_4317_, v_a_4299_);
v___x_4319_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4318_, v___x_4304_);
v___x_4320_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4320_, 0, v___x_4303_);
lean_ctor_set_uint8(v___x_4320_, 1, v___x_4289_);
v___x_4321_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_4319_, v_a_4306_, v_a_4311_, v___x_4320_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 0, v___x_4321_);
v___x_4323_ = v___x_4314_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
lean_ctor_set(v_reuseFailAlloc_4324_, 1, v_a_4312_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
else
{
lean_dec(v_a_4306_);
lean_dec_ref_known(v___x_4304_, 0);
lean_dec(v_a_4299_);
lean_dec(v_a_4294_);
return v___x_4310_;
}
}
else
{
lean_dec_ref_known(v___x_4304_, 0);
lean_dec(v_a_4299_);
lean_dec(v_a_4294_);
lean_dec(v_x_4274_);
return v___x_4305_;
}
}
else
{
lean_dec(v_a_4294_);
lean_dec(v_x_4274_);
return v___x_4298_;
}
}
else
{
lean_dec(v_x_4274_);
return v___x_4293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoWhile___boxed(lean_object* v_x_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Lean_Fmt_fmtDoWhile(v_x_4326_, v_a_4327_, v_a_4328_);
lean_dec_ref(v_a_4327_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1(){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4336_ = l_Lean_Fmt_fmtAttribute;
v___x_4337_ = ((lean_object*)(l_Lean_Fmt_fmtDoWhile___closed__1));
v___x_4338_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___closed__1));
v___x_4339_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoWhile___boxed), 3, 0);
v___x_4340_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4336_, v___x_4337_, v___x_4338_, v___x_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1___boxed(lean_object* v_a_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1();
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoRepeatUntil(lean_object* v_x_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_){
_start:
{
lean_object* v___x_4352_; uint8_t v___x_4353_; 
v___x_4352_ = ((lean_object*)(l_Lean_Fmt_fmtDoRepeatUntil___closed__1));
lean_inc(v_x_4349_);
v___x_4353_ = l_Lean_Syntax_isOfKind(v_x_4349_, v___x_4352_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
lean_dec(v_x_4349_);
v___x_4354_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
lean_ctor_set(v___x_4355_, 1, v_a_4351_);
return v___x_4355_;
}
else
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4356_ = lean_unsigned_to_nat(0u);
v___x_4357_ = lean_unsigned_to_nat(1u);
v___x_4358_ = l_Lean_Syntax_getArg(v_x_4349_, v___x_4357_);
v___x_4359_ = l_Lean_Syntax_matchesNull(v___x_4358_, v___x_4356_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
lean_dec(v_x_4349_);
v___x_4360_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4360_);
lean_ctor_set(v___x_4361_, 1, v_a_4351_);
return v___x_4361_;
}
else
{
lean_object* v___x_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; 
v___x_4362_ = lean_unsigned_to_nat(2u);
v___x_4363_ = l_Lean_Syntax_getArg(v_x_4349_, v___x_4362_);
v___x_4364_ = l_Lean_Syntax_matchesNull(v___x_4363_, v___x_4356_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; lean_object* v___x_4366_; 
lean_dec(v_x_4349_);
v___x_4365_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4365_);
lean_ctor_set(v___x_4366_, 1, v_a_4351_);
return v___x_4366_;
}
else
{
lean_object* v_repeatTk_4367_; lean_object* v___x_4368_; 
v_repeatTk_4367_ = l_Lean_Syntax_getArg(v_x_4349_, v___x_4356_);
v___x_4368_ = l_Lean_Fmt_fmt(v_repeatTk_4367_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v_a_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
v_a_4370_ = lean_ctor_get(v___x_4368_, 1);
lean_inc(v_a_4370_);
lean_dec_ref_known(v___x_4368_, 2);
v___x_4371_ = lean_unsigned_to_nat(3u);
v___x_4372_ = l_Lean_Syntax_getArg(v_x_4349_, v___x_4371_);
v___x_4373_ = l_Lean_Fmt_fmt(v___x_4372_, v_a_4350_, v_a_4370_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; lean_object* v_a_4375_; lean_object* v___x_4376_; lean_object* v_untilTk_4377_; lean_object* v___x_4378_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_a_4374_);
v_a_4375_ = lean_ctor_get(v___x_4373_, 1);
lean_inc(v_a_4375_);
lean_dec_ref_known(v___x_4373_, 2);
v___x_4376_ = lean_unsigned_to_nat(4u);
v_untilTk_4377_ = l_Lean_Syntax_getArg(v_x_4349_, v___x_4376_);
v___x_4378_ = l_Lean_Fmt_fmt(v_untilTk_4377_, v_a_4350_, v_a_4375_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; lean_object* v_a_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
v_a_4380_ = lean_ctor_get(v___x_4378_, 1);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4378_, 2);
v___x_4381_ = lean_unsigned_to_nat(5u);
v___x_4382_ = l_Lean_Syntax_getArg(v_x_4349_, v___x_4381_);
lean_dec(v_x_4349_);
v___x_4383_ = l_Lean_Fmt_fmt(v___x_4382_, v_a_4350_, v_a_4380_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4405_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
v_a_4385_ = lean_ctor_get(v___x_4383_, 1);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4387_ = v___x_4383_;
v_isShared_4388_ = v_isSharedCheck_4405_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_inc(v_a_4384_);
lean_dec(v___x_4383_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4405_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4389_ = lean_mk_empty_array_with_capacity(v___x_4362_);
lean_inc_ref_n(v___x_4389_, 2);
v___x_4390_ = lean_array_push(v___x_4389_, v_a_4379_);
v___x_4391_ = lean_array_push(v___x_4390_, v_a_4384_);
v___x_4392_ = 0;
v___x_4393_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4393_, 0, v___x_4364_);
lean_ctor_set_uint8(v___x_4393_, 1, v___x_4392_);
lean_ctor_set_uint8(v___x_4393_, 2, v___x_4392_);
lean_ctor_set_uint8(v___x_4393_, 3, v___x_4392_);
v___x_4394_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4391_, v___x_4393_);
v___x_4395_ = lean_array_push(v___x_4389_, v_a_4369_);
v___x_4396_ = lean_array_push(v___x_4395_, v_a_4374_);
v___x_4397_ = l_Lean_Fmt_Layouts_lines(v___x_4396_);
lean_dec_ref(v___x_4396_);
v___x_4398_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4397_);
v___x_4399_ = lean_array_push(v___x_4389_, v___x_4398_);
v___x_4400_ = lean_array_push(v___x_4399_, v___x_4394_);
v___x_4401_ = l_Lean_Fmt_Layouts_lines(v___x_4400_);
lean_dec_ref(v___x_4400_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 0, v___x_4401_);
v___x_4403_ = v___x_4387_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4401_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_a_4385_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
else
{
lean_dec(v_a_4379_);
lean_dec(v_a_4374_);
lean_dec(v_a_4369_);
return v___x_4383_;
}
}
else
{
lean_dec(v_a_4374_);
lean_dec(v_a_4369_);
lean_dec(v_x_4349_);
return v___x_4378_;
}
}
else
{
lean_dec(v_a_4369_);
lean_dec(v_x_4349_);
return v___x_4373_;
}
}
else
{
lean_dec(v_x_4349_);
return v___x_4368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoRepeatUntil___boxed(lean_object* v_x_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Lean_Fmt_fmtDoRepeatUntil(v_x_4406_, v_a_4407_, v_a_4408_);
lean_dec_ref(v_a_4407_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1(){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4416_ = l_Lean_Fmt_fmtAttribute;
v___x_4417_ = ((lean_object*)(l_Lean_Fmt_fmtDoRepeatUntil___closed__1));
v___x_4418_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___closed__1));
v___x_4419_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoRepeatUntil___boxed), 3, 0);
v___x_4420_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4416_, v___x_4417_, v___x_4418_, v___x_4419_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1___boxed(lean_object* v_a_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1();
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoNested(lean_object* v_x_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v___x_4426_; uint8_t v___x_4427_; 
v___x_4426_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqItems___closed__2));
lean_inc(v_x_4423_);
v___x_4427_ = l_Lean_Syntax_isOfKind(v_x_4423_, v___x_4426_);
if (v___x_4427_ == 0)
{
lean_object* v___x_4428_; lean_object* v___x_4429_; 
lean_dec(v_x_4423_);
v___x_4428_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
lean_ctor_set(v___x_4429_, 1, v_a_4425_);
return v___x_4429_;
}
else
{
lean_object* v___x_4430_; lean_object* v_doTk_4431_; lean_object* v___x_4432_; 
v___x_4430_ = lean_unsigned_to_nat(0u);
v_doTk_4431_ = l_Lean_Syntax_getArg(v_x_4423_, v___x_4430_);
v___x_4432_ = l_Lean_Fmt_fmt(v_doTk_4431_, v_a_4424_, v_a_4425_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; lean_object* v_a_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4433_);
v_a_4434_ = lean_ctor_get(v___x_4432_, 1);
lean_inc(v_a_4434_);
lean_dec_ref_known(v___x_4432_, 2);
v___x_4435_ = lean_unsigned_to_nat(1u);
v___x_4436_ = l_Lean_Syntax_getArg(v_x_4423_, v___x_4435_);
lean_dec(v_x_4423_);
v___x_4437_ = l_Lean_Fmt_fmt(v___x_4436_, v_a_4424_, v_a_4434_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4438_; lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4448_; 
v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
v_a_4439_ = lean_ctor_get(v___x_4437_, 1);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4441_ = v___x_4437_;
v_isShared_4442_ = v_isSharedCheck_4448_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_inc(v_a_4438_);
lean_dec(v___x_4437_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4448_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
uint8_t v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4446_; 
v___x_4443_ = 0;
v___x_4444_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_4433_, v_a_4438_, v___x_4443_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 0, v___x_4444_);
v___x_4446_ = v___x_4441_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4444_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v_a_4439_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
else
{
lean_dec(v_a_4433_);
return v___x_4437_;
}
}
else
{
lean_dec(v_x_4423_);
return v___x_4432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoNested___boxed(lean_object* v_x_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Lean_Fmt_fmtDoNested(v_x_4449_, v_a_4450_, v_a_4451_);
lean_dec_ref(v_a_4450_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1(){
_start:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4459_ = l_Lean_Fmt_fmtAttribute;
v___x_4460_ = ((lean_object*)(l_Lean_Fmt_fmtDoSeqItems___closed__2));
v___x_4461_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___closed__1));
v___x_4462_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoNested___boxed), 3, 0);
v___x_4463_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4459_, v___x_4460_, v___x_4461_, v___x_4462_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1___boxed(lean_object* v_a_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1();
return v_res_4465_;
}
}
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Do(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtNestedAction___regBuiltin_Lean_Fmt_fmtNestedAction__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoExpr___regBuiltin_Lean_Fmt_fmtDoExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqIndent___regBuiltin_Lean_Fmt_fmtDoSeqIndent__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoSeqBracketed___regBuiltin_Lean_Fmt_fmtDoSeqBracketed__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDo___regBuiltin_Lean_Fmt_fmtDo__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermReturn___regBuiltin_Lean_Fmt_fmtTermReturn__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoBreak___regBuiltin_Lean_Fmt_fmtDoBreak__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoContinue___regBuiltin_Lean_Fmt_fmtDoContinue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReturn___regBuiltin_Lean_Fmt_fmtDoReturn__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDbgTrace___regBuiltin_Lean_Fmt_fmtDoDbgTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoAssert___regBuiltin_Lean_Fmt_fmtDoAssert__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoDebugAssert___regBuiltin_Lean_Fmt_fmtDoDebugAssert__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeat___regBuiltin_Lean_Fmt_fmtDoRepeat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLet___regBuiltin_Lean_Fmt_fmtDoLet__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoHave___regBuiltin_Lean_Fmt_fmtDoHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetArrow___regBuiltin_Lean_Fmt_fmtDoLetArrow__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetElse___regBuiltin_Lean_Fmt_fmtDoLetElse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetExpr___regBuiltin_Lean_Fmt_fmtDoLetExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetMetaExpr___regBuiltin_Lean_Fmt_fmtDoLetMetaExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoLetRec___regBuiltin_Lean_Fmt_fmtDoLetRec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtLetIdDeclNoBinders___regBuiltin_Lean_Fmt_fmtLetIdDeclNoBinders__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassign___regBuiltin_Lean_Fmt_fmtDoReassign__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoReassignArrow___regBuiltin_Lean_Fmt_fmtDoReassignArrow__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfProp___regBuiltin_Lean_Fmt_fmtDoIfProp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIfLet___regBuiltin_Lean_Fmt_fmtDoIfLet__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoIf___regBuiltin_Lean_Fmt_fmtDoIf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoUnless___regBuiltin_Lean_Fmt_fmtDoUnless__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermUnless___regBuiltin_Lean_Fmt_fmtTermUnless__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForDecl___regBuiltin_Lean_Fmt_fmtDoForDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoFor___regBuiltin_Lean_Fmt_fmtDoFor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermFor___regBuiltin_Lean_Fmt_fmtTermFor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDependentParam___regBuiltin_Lean_Fmt_fmtDependentParam__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatch___regBuiltin_Lean_Fmt_fmtDoMatch__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoMatchExpr___regBuiltin_Lean_Fmt_fmtDoMatchExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoTry___regBuiltin_Lean_Fmt_fmtDoTry__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtTermTry___regBuiltin_Lean_Fmt_fmtTermTry__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoForward___regBuiltin_Lean_Fmt_fmtDoForward__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoWhile___regBuiltin_Lean_Fmt_fmtDoWhile__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoRepeatUntil___regBuiltin_Lean_Fmt_fmtDoRepeatUntil__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Do_0__Lean_Fmt_fmtDoNested___regBuiltin_Lean_Fmt_fmtDoNested__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Do(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Do(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Parser_Do(builtin);
}
#ifdef __cplusplus
}
#endif
