// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Parser.Term.Basic
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.FmtM.CommonFormatters meta import Lean.Parser.Term.Basic import Init.Data
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_identComponents_x3f(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSeq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_break;
lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepBefore(lean_object*, lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtLocalSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_hardNl;
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_propagateMetaData(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_failure;
lean_object* l_Lean_Fmt_TaggedDoc_addMetaData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHole(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHole___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtAtomic___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__5_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fmtHole"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__7 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(246, 191, 29, 183, 12, 58, 16, 24)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__8 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntheticHole___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_Lean_Fmt_fmtSyntheticHole___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntheticHole___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntheticHole___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntheticHole___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntheticHole___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntheticHole___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntheticHole___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntheticHole___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntheticHole___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntheticHole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l_Lean_Fmt_fmtSyntheticHole___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntheticHole___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntheticHole(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntheticHole___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtSyntheticHole"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 103, 8, 58, 118, 45, 197, 36)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtOmission(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtOmission___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "omission"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 154, 52, 140, 5, 177, 16, 6)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtOmission"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(211, 210, 31, 8, 229, 167, 237, 121)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExplicitBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l_Lean_Fmt_fmtExplicitBinder___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExplicitBinder___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtExplicitBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtExplicitBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExplicitBinder___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtExplicitBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExplicitBinder___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtExplicitBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExplicitBinder___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtExplicitBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l_Lean_Fmt_fmtExplicitBinder___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExplicitBinder___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtExplicitBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtExplicitBinder___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtExplicitBinder___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtExplicitBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtExplicitBinder___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtExplicitBinder___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExplicitBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExplicitBinder___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtExplicitBinder"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 205, 34, 192, 92, 189, 176, 204)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtImplicitBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l_Lean_Fmt_fmtImplicitBinder___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtImplicitBinder___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtImplicitBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtImplicitBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtImplicitBinder___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtImplicitBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtImplicitBinder___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtImplicitBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtImplicitBinder___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtImplicitBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l_Lean_Fmt_fmtImplicitBinder___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtImplicitBinder___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtImplicitBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtImplicitBinder___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtImplicitBinder"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 68, 146, 31, 48, 227, 80, 239)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtStrictImplicitBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "strictImplicitBinder"};
static const lean_object* l_Lean_Fmt_fmtStrictImplicitBinder___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtStrictImplicitBinder___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtStrictImplicitBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtStrictImplicitBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStrictImplicitBinder___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtStrictImplicitBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStrictImplicitBinder___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtStrictImplicitBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStrictImplicitBinder___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtStrictImplicitBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 223, 215, 186, 222, 17, 242, 189)}};
static const lean_object* l_Lean_Fmt_fmtStrictImplicitBinder___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtStrictImplicitBinder___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtStrictImplicitBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Fmt_fmtStrictImplicitBinder___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtStrictImplicitBinder___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtStrictImplicitBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtStrictImplicitBinder___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Fmt_fmtStrictImplicitBinder___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtStrictImplicitBinder___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStrictImplicitBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStrictImplicitBinder___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtStrictImplicitBinder"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 19, 194, 41, 149, 212, 248, 167)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtInstBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l_Lean_Fmt_fmtInstBinder___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtInstBinder___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtInstBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtInstBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInstBinder___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtInstBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInstBinder___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtInstBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInstBinder___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtInstBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l_Lean_Fmt_fmtInstBinder___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtInstBinder___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtInstBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtInstBinder___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtInstBinder___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtInstBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtInstBinder___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtInstBinder___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtInstBinder___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInstBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInstBinder___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtInstBinder"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 197, 149, 13, 120, 112, 212, 163)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtStructInstArrayRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstArrayRef"};
static const lean_object* l_Lean_Fmt_fmtStructInstArrayRef___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtStructInstArrayRef___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtStructInstArrayRef___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtStructInstArrayRef___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStructInstArrayRef___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtStructInstArrayRef___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStructInstArrayRef___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtStructInstArrayRef___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStructInstArrayRef___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtStructInstArrayRef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 97, 16, 232, 167, 67, 90, 227)}};
static const lean_object* l_Lean_Fmt_fmtStructInstArrayRef___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtStructInstArrayRef___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstArrayRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstArrayRef___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtStructInstArrayRef"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 40, 38, 118, 96, 9, 61, 253)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_structInstLValKinds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldIdx"};
static const lean_object* l_Lean_Fmt_structInstLValKinds___closed__0 = (const lean_object*)&l_Lean_Fmt_structInstLValKinds___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_structInstLValKinds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_structInstLValKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 141, 165, 29, 238, 211, 61, 163)}};
static const lean_object* l_Lean_Fmt_structInstLValKinds___closed__1 = (const lean_object*)&l_Lean_Fmt_structInstLValKinds___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_structInstLValKinds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStructInstArrayRef___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_structInstLValKinds___closed__2 = (const lean_object*)&l_Lean_Fmt_structInstLValKinds___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_structInstLValKinds___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_structInstLValKinds___closed__1_value),((lean_object*)&l_Lean_Fmt_structInstLValKinds___closed__2_value)}};
static const lean_object* l_Lean_Fmt_structInstLValKinds___closed__3 = (const lean_object*)&l_Lean_Fmt_structInstLValKinds___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_structInstLValKinds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInstBinder___closed__3_value),((lean_object*)&l_Lean_Fmt_structInstLValKinds___closed__3_value)}};
static const lean_object* l_Lean_Fmt_structInstLValKinds___closed__4 = (const lean_object*)&l_Lean_Fmt_structInstLValKinds___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_structInstLValKinds = (const lean_object*)&l_Lean_Fmt_structInstLValKinds___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_splitStructInstLValIdent(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_splitStructInstLValRhs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_splitStructInstLValRhs___closed__0 = (const lean_object*)&l_Lean_Fmt_splitStructInstLValRhs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_splitStructInstLValRhs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_splitStructInstLValRhs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Fmt_fmtStructInstLVal_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Fmt_fmtStructInstLVal_spec__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_fmtStructInstLVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtStructInstLVal___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtStructInstLVal___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstLVal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstLVal___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtStructInstLVal"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(254, 229, 233, 175, 84, 215, 254, 209)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_convertStructInstFieldBinders_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_convertStructInstFieldBinders_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_convertStructInstFieldBinders(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedStructInstFieldDecl_default = (const lean_object*)&l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedStructInstFieldDecl = (const lean_object*)&l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___closed__0_value;
static const lean_string_object l_Lean_Fmt_instImpl___closed__0_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "StructInstFieldDecl"};
static const lean_object* l_Lean_Fmt_instImpl___closed__0_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15_ = (const lean_object*)&l_Lean_Fmt_instImpl___closed__0_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value;
static const lean_ctor_object l_Lean_Fmt_instImpl___closed__1_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_instImpl___closed__1_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_instImpl___closed__1_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_instImpl___closed__1_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_instImpl___closed__1_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value_aux_1),((lean_object*)&l_Lean_Fmt_instImpl___closed__0_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(105, 59, 58, 188, 119, 130, 141, 175)}};
static const lean_object* l_Lean_Fmt_instImpl___closed__1_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15_ = (const lean_object*)&l_Lean_Fmt_instImpl___closed__1_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instImpl_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15_ = (const lean_object*)&l_Lean_Fmt_instImpl___closed__1_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instTypeNameStructInstFieldDecl = (const lean_object*)&l_Lean_Fmt_instImpl___closed__1_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l_Lean_Fmt_mkStructInstFieldDecl___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_mkStructInstFieldDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_mkStructInstFieldDecl___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_mkStructInstFieldDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_mkStructInstFieldDecl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_mkStructInstFieldDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getStructInstFieldDecl_x3f(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtStructInstField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l_Lean_Fmt_fmtStructInstField___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtStructInstField___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtStructInstField___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtStructInstField___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtStructInstField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l_Lean_Fmt_fmtStructInstField___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtStructInstField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Fmt_fmtStructInstField___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtStructInstField___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtStructInstField___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtStructInstField___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtStructInstField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Fmt_fmtStructInstField___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtStructInstField___closed__3_value;
static lean_once_cell_t l_Lean_Fmt_fmtStructInstField___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtStructInstField___closed__4;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstField(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstField___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtStructInstField"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 20, 234, 28, 147, 18, 51, 26)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticSeq1Indented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtTacticSeq1Indented___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtTacticSeq1Indented___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Fmt_fmtTacticSeq1Indented___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeq1Indented___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeq1Indented___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeq1Indented___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeq1Indented___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Fmt_fmtTacticSeq1Indented___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtTacticSeq1Indented___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Fmt_fmtTacticSeq1Indented___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeq1Indented(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeq1Indented___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtTacticSeq1Indented"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 122, 210, 101, 43, 32, 77, 197)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticSeqBracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeqBracketed"};
static const lean_object* l_Lean_Fmt_fmtTacticSeqBracketed___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticSeqBracketed___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeqBracketed___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeqBracketed___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticSeqBracketed___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeqBracketed___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticSeqBracketed___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeqBracketed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticSeqBracketed___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_object* l_Lean_Fmt_fmtTacticSeqBracketed___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticSeqBracketed___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeqBracketed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeqBracketed___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtTacticSeqBracketed"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 254, 246, 119, 214, 151, 212, 47)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Fmt_fmtTacticSeq___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticSeq___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticSeq___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticSeq___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTacticSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticSeq___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticSeq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Fmt_fmtTacticSeq___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticSeq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeq___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtTacticSeq"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 4, 37, 161, 220, 49, 233, 28)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHole(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Lean_Fmt_fmtAtomic(v_a_1_, v_a_2_, v_a_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHole___boxed(lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Fmt_fmtHole(v_a_5_, v_a_6_, v_a_7_);
lean_dec_ref(v_a_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1(){
_start:
{
lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___f_26_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__0));
v___x_27_ = l_Lean_Fmt_fmtAttribute;
v___x_28_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__5));
v___x_29_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__8));
v___x_30_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_27_, v___x_28_, v___x_29_, v___f_26_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___boxed(lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1();
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntheticHole(lean_object* v_x_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_42_ = ((lean_object*)(l_Lean_Fmt_fmtSyntheticHole___closed__1));
lean_inc(v_x_39_);
v___x_43_ = l_Lean_Syntax_isOfKind(v_x_39_, v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v_x_39_);
v___x_44_ = l_Lean_Fmt_Error_partialFormatter;
v___x_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v_a_41_);
return v___x_45_;
}
else
{
lean_object* v___x_46_; lean_object* v_questionTk_47_; lean_object* v___x_48_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v_questionTk_47_ = l_Lean_Syntax_getArg(v_x_39_, v___x_46_);
v___x_48_ = l_Lean_Fmt_fmt(v_questionTk_47_, v_a_40_, v_a_41_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v_a_50_; lean_object* v___x_51_; lean_object* v_holeTk_52_; lean_object* v___x_53_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_a_49_);
v_a_50_ = lean_ctor_get(v___x_48_, 1);
lean_inc(v_a_50_);
lean_dec_ref_known(v___x_48_, 2);
v___x_51_ = lean_unsigned_to_nat(1u);
v_holeTk_52_ = l_Lean_Syntax_getArg(v_x_39_, v___x_51_);
lean_dec(v_x_39_);
v___x_53_ = l_Lean_Fmt_fmt(v_holeTk_52_, v_a_40_, v_a_50_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_67_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_a_55_ = lean_ctor_get(v___x_53_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_67_ == 0)
{
v___x_57_ = v___x_53_;
v_isShared_58_ = v_isSharedCheck_67_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_67_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_59_ = lean_unsigned_to_nat(2u);
v___x_60_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_61_ = lean_array_push(v___x_60_, v_a_49_);
v___x_62_ = lean_array_push(v___x_61_, v_a_54_);
v___x_63_ = l_Lean_Fmt_Layouts_atomic(v___x_62_);
lean_dec_ref(v___x_62_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_63_);
v___x_65_ = v___x_57_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_a_55_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
else
{
lean_dec(v_a_49_);
return v___x_53_;
}
}
else
{
lean_dec(v_x_39_);
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntheticHole___boxed(lean_object* v_x_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Fmt_fmtSyntheticHole(v_x_68_, v_a_69_, v_a_70_);
lean_dec_ref(v_a_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1(){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_78_ = l_Lean_Fmt_fmtAttribute;
v___x_79_ = ((lean_object*)(l_Lean_Fmt_fmtSyntheticHole___closed__1));
v___x_80_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___closed__1));
v___x_81_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntheticHole___boxed), 3, 0);
v___x_82_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_78_, v___x_79_, v___x_80_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1___boxed(lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1();
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtOmission(lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Fmt_fmtAtomic(v_a_85_, v_a_86_, v_a_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtOmission___boxed(lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Fmt_fmtOmission(v_a_89_, v_a_90_, v_a_91_);
lean_dec_ref(v_a_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1(){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___f_105_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1___closed__0));
v___x_106_ = l_Lean_Fmt_fmtAttribute;
v___x_107_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__1));
v___x_108_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___closed__3));
v___x_109_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_106_, v___x_107_, v___x_108_, v___f_105_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1___boxed(lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1();
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExplicitBinder(lean_object* v_x_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__1));
lean_inc(v_x_122_);
v___x_126_ = l_Lean_Syntax_isOfKind(v_x_122_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_x_122_);
v___x_127_ = l_Lean_Fmt_Error_partialFormatter;
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v_a_124_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; lean_object* v_lbTk_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v_tacticOrDefault_x3f_136_; lean_object* v___y_137_; lean_object* v___y_138_; lean_object* v_typeAscriptionTk_x3f_149_; lean_object* v_type_x3f_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v_lbTk_130_ = l_Lean_Syntax_getArg(v_x_122_, v___x_129_);
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = l_Lean_Syntax_getArg(v_x_122_, v___x_131_);
v___x_162_ = lean_unsigned_to_nat(2u);
v___x_163_ = l_Lean_Syntax_getArg(v_x_122_, v___x_162_);
v___x_164_ = l_Lean_Syntax_isNone(v___x_163_);
if (v___x_164_ == 0)
{
uint8_t v___x_165_; 
lean_inc(v___x_163_);
v___x_165_ = l_Lean_Syntax_matchesNull(v___x_163_, v___x_162_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v___x_163_);
lean_dec(v___x_132_);
lean_dec(v_lbTk_130_);
lean_dec(v_x_122_);
v___x_166_ = l_Lean_Fmt_Error_partialFormatter;
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_124_);
return v___x_167_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_168_; lean_object* v_type_x3f_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_typeAscriptionTk_x3f_168_ = l_Lean_Syntax_getArg(v___x_163_, v___x_129_);
v_type_x3f_169_ = l_Lean_Syntax_getArg(v___x_163_, v___x_131_);
lean_dec(v___x_163_);
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v_typeAscriptionTk_x3f_168_);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v_type_x3f_169_);
v_typeAscriptionTk_x3f_149_ = v___x_170_;
v_type_x3f_150_ = v___x_171_;
v___y_151_ = v_a_123_;
v___y_152_ = v_a_124_;
goto v___jp_148_;
}
}
else
{
lean_object* v___x_172_; 
lean_dec(v___x_163_);
v___x_172_ = lean_box(0);
v_typeAscriptionTk_x3f_149_ = v___x_172_;
v_type_x3f_150_ = v___x_172_;
v___y_151_ = v_a_123_;
v___y_152_ = v_a_124_;
goto v___jp_148_;
}
v___jp_133_:
{
lean_object* v___x_139_; lean_object* v_rbTk_140_; lean_object* v_ids_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_139_ = lean_unsigned_to_nat(4u);
v_rbTk_140_ = l_Lean_Syntax_getArg(v_x_122_, v___x_139_);
lean_dec(v_x_122_);
v_ids_141_ = l_Lean_Syntax_getArgs(v___x_132_);
lean_dec(v___x_132_);
v___x_142_ = lean_mk_empty_array_with_capacity(v___x_131_);
lean_inc_ref(v___x_142_);
v___x_143_ = lean_array_push(v___x_142_, v_lbTk_130_);
v___x_144_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__2));
v___x_145_ = lean_array_push(v___x_142_, v_rbTk_140_);
v___x_146_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__3));
v___x_147_ = l_Lean_Fmt_fmtBinder(v___x_143_, v_ids_141_, v___x_144_, v___y_135_, v___y_134_, v_tacticOrDefault_x3f_136_, v___x_145_, v___x_146_, v___y_137_, v___y_138_);
return v___x_147_;
}
v___jp_148_:
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = lean_unsigned_to_nat(3u);
v___x_154_ = l_Lean_Syntax_getArg(v_x_122_, v___x_153_);
v___x_155_ = l_Lean_Syntax_isNone(v___x_154_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
lean_inc(v___x_154_);
v___x_156_ = l_Lean_Syntax_matchesNull(v___x_154_, v___x_131_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v___x_154_);
lean_dec(v_type_x3f_150_);
lean_dec(v_typeAscriptionTk_x3f_149_);
lean_dec(v___x_132_);
lean_dec(v_lbTk_130_);
lean_dec(v_x_122_);
v___x_157_ = l_Lean_Fmt_Error_partialFormatter;
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___y_152_);
return v___x_158_;
}
else
{
lean_object* v_tacticOrDefault_x3f_159_; lean_object* v___x_160_; 
v_tacticOrDefault_x3f_159_ = l_Lean_Syntax_getArg(v___x_154_, v___x_129_);
lean_dec(v___x_154_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v_tacticOrDefault_x3f_159_);
v___y_134_ = v_type_x3f_150_;
v___y_135_ = v_typeAscriptionTk_x3f_149_;
v_tacticOrDefault_x3f_136_ = v___x_160_;
v___y_137_ = v___y_151_;
v___y_138_ = v___y_152_;
goto v___jp_133_;
}
}
else
{
lean_object* v___x_161_; 
lean_dec(v___x_154_);
v___x_161_ = lean_box(0);
v___y_134_ = v_type_x3f_150_;
v___y_135_ = v_typeAscriptionTk_x3f_149_;
v_tacticOrDefault_x3f_136_ = v___x_161_;
v___y_137_ = v___y_151_;
v___y_138_ = v___y_152_;
goto v___jp_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExplicitBinder___boxed(lean_object* v_x_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Fmt_fmtExplicitBinder(v_x_173_, v_a_174_, v_a_175_);
lean_dec_ref(v_a_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1(){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_183_ = l_Lean_Fmt_fmtAttribute;
v___x_184_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__1));
v___x_185_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___closed__1));
v___x_186_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExplicitBinder___boxed), 3, 0);
v___x_187_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_183_, v___x_184_, v___x_185_, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1___boxed(lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1();
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtImplicitBinder(lean_object* v_x_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_Fmt_fmtImplicitBinder___closed__1));
lean_inc(v_x_196_);
v___x_200_ = l_Lean_Syntax_isOfKind(v_x_196_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_x_196_);
v___x_201_ = l_Lean_Fmt_Error_partialFormatter;
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_a_198_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v_lbTk_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_typeAscriptionTk_x3f_208_; lean_object* v_type_x3f_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v_lbTk_204_ = l_Lean_Syntax_getArg(v_x_196_, v___x_203_);
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = l_Lean_Syntax_getArg(v_x_196_, v___x_205_);
v___x_222_ = lean_unsigned_to_nat(2u);
v___x_223_ = l_Lean_Syntax_getArg(v_x_196_, v___x_222_);
v___x_224_ = l_Lean_Syntax_isNone(v___x_223_);
if (v___x_224_ == 0)
{
uint8_t v___x_225_; 
lean_inc(v___x_223_);
v___x_225_ = l_Lean_Syntax_matchesNull(v___x_223_, v___x_222_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v___x_223_);
lean_dec(v___x_206_);
lean_dec(v_lbTk_204_);
lean_dec(v_x_196_);
v___x_226_ = l_Lean_Fmt_Error_partialFormatter;
v___x_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_198_);
return v___x_227_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_228_; lean_object* v_type_x3f_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_typeAscriptionTk_x3f_228_ = l_Lean_Syntax_getArg(v___x_223_, v___x_203_);
v_type_x3f_229_ = l_Lean_Syntax_getArg(v___x_223_, v___x_205_);
lean_dec(v___x_223_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v_typeAscriptionTk_x3f_228_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v_type_x3f_229_);
v_typeAscriptionTk_x3f_208_ = v___x_230_;
v_type_x3f_209_ = v___x_231_;
v___y_210_ = v_a_197_;
v___y_211_ = v_a_198_;
goto v___jp_207_;
}
}
else
{
lean_object* v___x_232_; 
lean_dec(v___x_223_);
v___x_232_ = lean_box(0);
v_typeAscriptionTk_x3f_208_ = v___x_232_;
v_type_x3f_209_ = v___x_232_;
v___y_210_ = v_a_197_;
v___y_211_ = v_a_198_;
goto v___jp_207_;
}
v___jp_207_:
{
lean_object* v___x_212_; lean_object* v_rbTk_213_; lean_object* v_ids_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_212_ = lean_unsigned_to_nat(3u);
v_rbTk_213_ = l_Lean_Syntax_getArg(v_x_196_, v___x_212_);
lean_dec(v_x_196_);
v_ids_214_ = l_Lean_Syntax_getArgs(v___x_206_);
lean_dec(v___x_206_);
v___x_215_ = lean_mk_empty_array_with_capacity(v___x_205_);
lean_inc_ref(v___x_215_);
v___x_216_ = lean_array_push(v___x_215_, v_lbTk_204_);
v___x_217_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__2));
v___x_218_ = lean_box(0);
v___x_219_ = lean_array_push(v___x_215_, v_rbTk_213_);
v___x_220_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__3));
v___x_221_ = l_Lean_Fmt_fmtBinder(v___x_216_, v_ids_214_, v___x_217_, v_typeAscriptionTk_x3f_208_, v_type_x3f_209_, v___x_218_, v___x_219_, v___x_220_, v___y_210_, v___y_211_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtImplicitBinder___boxed(lean_object* v_x_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Fmt_fmtImplicitBinder(v_x_233_, v_a_234_, v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1(){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_243_ = l_Lean_Fmt_fmtAttribute;
v___x_244_ = ((lean_object*)(l_Lean_Fmt_fmtImplicitBinder___closed__1));
v___x_245_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___closed__1));
v___x_246_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtImplicitBinder___boxed), 3, 0);
v___x_247_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_243_, v___x_244_, v___x_245_, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1___boxed(lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1();
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStrictImplicitBinder(lean_object* v_x_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = ((lean_object*)(l_Lean_Fmt_fmtStrictImplicitBinder___closed__1));
lean_inc(v_x_259_);
v___x_263_ = l_Lean_Syntax_isOfKind(v_x_259_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_x_259_);
v___x_264_ = l_Lean_Fmt_Error_partialFormatter;
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_a_261_);
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v_lbTk_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_266_ = lean_unsigned_to_nat(0u);
v_lbTk_267_ = l_Lean_Syntax_getArg(v_x_259_, v___x_266_);
v___x_268_ = ((lean_object*)(l_Lean_Fmt_fmtStrictImplicitBinder___closed__3));
lean_inc(v_lbTk_267_);
v___x_269_ = l_Lean_Syntax_isOfKind(v_lbTk_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v_typeAscriptionTk_x3f_273_; lean_object* v_type_x3f_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = l_Lean_Syntax_getArg(v_x_259_, v___x_270_);
v___x_301_ = lean_unsigned_to_nat(2u);
v___x_302_ = l_Lean_Syntax_getArg(v_x_259_, v___x_301_);
v___x_303_ = l_Lean_Syntax_isNone(v___x_302_);
if (v___x_303_ == 0)
{
uint8_t v___x_304_; 
lean_inc(v___x_302_);
v___x_304_ = l_Lean_Syntax_matchesNull(v___x_302_, v___x_301_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v___x_302_);
lean_dec(v___x_271_);
lean_dec(v_lbTk_267_);
lean_dec(v_x_259_);
v___x_305_ = l_Lean_Fmt_Error_partialFormatter;
v___x_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_a_261_);
return v___x_306_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_307_; lean_object* v_type_x3f_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_typeAscriptionTk_x3f_307_ = l_Lean_Syntax_getArg(v___x_302_, v___x_266_);
v_type_x3f_308_ = l_Lean_Syntax_getArg(v___x_302_, v___x_270_);
lean_dec(v___x_302_);
v___x_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_309_, 0, v_typeAscriptionTk_x3f_307_);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_type_x3f_308_);
v_typeAscriptionTk_x3f_273_ = v___x_309_;
v_type_x3f_274_ = v___x_310_;
v___y_275_ = v_a_260_;
v___y_276_ = v_a_261_;
goto v___jp_272_;
}
}
else
{
lean_object* v___x_311_; 
lean_dec(v___x_302_);
v___x_311_ = lean_box(0);
v_typeAscriptionTk_x3f_273_ = v___x_311_;
v_type_x3f_274_ = v___x_311_;
v___y_275_ = v_a_260_;
v___y_276_ = v_a_261_;
goto v___jp_272_;
}
v___jp_272_:
{
lean_object* v___x_277_; lean_object* v_rbTk_278_; uint8_t v___x_279_; 
v___x_277_ = lean_unsigned_to_nat(3u);
v_rbTk_278_ = l_Lean_Syntax_getArg(v_x_259_, v___x_277_);
lean_dec(v_x_259_);
lean_inc(v_rbTk_278_);
v___x_279_ = l_Lean_Syntax_isOfKind(v_rbTk_278_, v___x_268_);
if (v___x_279_ == 0)
{
lean_object* v_ids_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_ids_280_ = l_Lean_Syntax_getArgs(v___x_271_);
lean_dec(v___x_271_);
v___x_281_ = lean_mk_empty_array_with_capacity(v___x_270_);
lean_inc_ref(v___x_281_);
v___x_282_ = lean_array_push(v___x_281_, v_lbTk_267_);
v___x_283_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__2));
v___x_284_ = lean_box(0);
v___x_285_ = lean_array_push(v___x_281_, v_rbTk_278_);
v___x_286_ = lean_box(1);
v___x_287_ = l_Lean_Fmt_fmtBinder(v___x_282_, v_ids_280_, v___x_283_, v_typeAscriptionTk_x3f_273_, v_type_x3f_274_, v___x_284_, v___x_285_, v___x_286_, v___y_275_, v___y_276_);
return v___x_287_;
}
else
{
lean_object* v_rbTk1_288_; lean_object* v_rbTk2_289_; lean_object* v_ids_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_rbTk1_288_ = l_Lean_Syntax_getArg(v_rbTk_278_, v___x_266_);
v_rbTk2_289_ = l_Lean_Syntax_getArg(v_rbTk_278_, v___x_270_);
lean_dec(v_rbTk_278_);
v_ids_290_ = l_Lean_Syntax_getArgs(v___x_271_);
lean_dec(v___x_271_);
v___x_291_ = lean_mk_empty_array_with_capacity(v___x_270_);
v___x_292_ = lean_array_push(v___x_291_, v_lbTk_267_);
v___x_293_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__2));
v___x_294_ = lean_box(0);
v___x_295_ = lean_unsigned_to_nat(2u);
v___x_296_ = lean_mk_empty_array_with_capacity(v___x_295_);
v___x_297_ = lean_array_push(v___x_296_, v_rbTk1_288_);
v___x_298_ = lean_array_push(v___x_297_, v_rbTk2_289_);
v___x_299_ = lean_box(1);
v___x_300_ = l_Lean_Fmt_fmtBinder(v___x_292_, v_ids_290_, v___x_293_, v_typeAscriptionTk_x3f_273_, v_type_x3f_274_, v___x_294_, v___x_298_, v___x_299_, v___y_275_, v___y_276_);
return v___x_300_;
}
}
}
else
{
lean_object* v_lbTk1_312_; lean_object* v___x_313_; lean_object* v_lbTk2_314_; lean_object* v___x_315_; lean_object* v_typeAscriptionTk_x3f_317_; lean_object* v_type_x3f_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_lbTk1_312_ = l_Lean_Syntax_getArg(v_lbTk_267_, v___x_266_);
v___x_313_ = lean_unsigned_to_nat(1u);
v_lbTk2_314_ = l_Lean_Syntax_getArg(v_lbTk_267_, v___x_313_);
lean_dec(v_lbTk_267_);
v___x_315_ = l_Lean_Syntax_getArg(v_x_259_, v___x_313_);
v___x_348_ = lean_unsigned_to_nat(2u);
v___x_349_ = l_Lean_Syntax_getArg(v_x_259_, v___x_348_);
v___x_350_ = l_Lean_Syntax_isNone(v___x_349_);
if (v___x_350_ == 0)
{
uint8_t v___x_351_; 
lean_inc(v___x_349_);
v___x_351_ = l_Lean_Syntax_matchesNull(v___x_349_, v___x_348_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v___x_349_);
lean_dec(v___x_315_);
lean_dec(v_lbTk2_314_);
lean_dec(v_lbTk1_312_);
lean_dec(v_x_259_);
v___x_352_ = l_Lean_Fmt_Error_partialFormatter;
v___x_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_a_261_);
return v___x_353_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_354_; lean_object* v_type_x3f_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_typeAscriptionTk_x3f_354_ = l_Lean_Syntax_getArg(v___x_349_, v___x_266_);
v_type_x3f_355_ = l_Lean_Syntax_getArg(v___x_349_, v___x_313_);
lean_dec(v___x_349_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_typeAscriptionTk_x3f_354_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_type_x3f_355_);
v_typeAscriptionTk_x3f_317_ = v___x_356_;
v_type_x3f_318_ = v___x_357_;
v___y_319_ = v_a_260_;
v___y_320_ = v_a_261_;
goto v___jp_316_;
}
}
else
{
lean_object* v___x_358_; 
lean_dec(v___x_349_);
v___x_358_ = lean_box(0);
v_typeAscriptionTk_x3f_317_ = v___x_358_;
v_type_x3f_318_ = v___x_358_;
v___y_319_ = v_a_260_;
v___y_320_ = v_a_261_;
goto v___jp_316_;
}
v___jp_316_:
{
lean_object* v___x_321_; lean_object* v_rbTk_322_; uint8_t v___x_323_; 
v___x_321_ = lean_unsigned_to_nat(3u);
v_rbTk_322_ = l_Lean_Syntax_getArg(v_x_259_, v___x_321_);
lean_dec(v_x_259_);
lean_inc(v_rbTk_322_);
v___x_323_ = l_Lean_Syntax_isOfKind(v_rbTk_322_, v___x_268_);
if (v___x_323_ == 0)
{
lean_object* v_ids_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_ids_324_ = l_Lean_Syntax_getArgs(v___x_315_);
lean_dec(v___x_315_);
v___x_325_ = lean_unsigned_to_nat(2u);
v___x_326_ = lean_mk_empty_array_with_capacity(v___x_325_);
v___x_327_ = lean_array_push(v___x_326_, v_lbTk1_312_);
v___x_328_ = lean_array_push(v___x_327_, v_lbTk2_314_);
v___x_329_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__2));
v___x_330_ = lean_box(0);
v___x_331_ = lean_mk_empty_array_with_capacity(v___x_313_);
v___x_332_ = lean_array_push(v___x_331_, v_rbTk_322_);
v___x_333_ = lean_box(1);
v___x_334_ = l_Lean_Fmt_fmtBinder(v___x_328_, v_ids_324_, v___x_329_, v_typeAscriptionTk_x3f_317_, v_type_x3f_318_, v___x_330_, v___x_332_, v___x_333_, v___y_319_, v___y_320_);
return v___x_334_;
}
else
{
lean_object* v_rbTk1_335_; lean_object* v_rbTk2_336_; lean_object* v_ids_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_rbTk1_335_ = l_Lean_Syntax_getArg(v_rbTk_322_, v___x_266_);
v_rbTk2_336_ = l_Lean_Syntax_getArg(v_rbTk_322_, v___x_313_);
lean_dec(v_rbTk_322_);
v_ids_337_ = l_Lean_Syntax_getArgs(v___x_315_);
lean_dec(v___x_315_);
v___x_338_ = lean_unsigned_to_nat(2u);
v___x_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
lean_inc_ref(v___x_339_);
v___x_340_ = lean_array_push(v___x_339_, v_lbTk1_312_);
v___x_341_ = lean_array_push(v___x_340_, v_lbTk2_314_);
v___x_342_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__2));
v___x_343_ = lean_box(0);
v___x_344_ = lean_array_push(v___x_339_, v_rbTk1_335_);
v___x_345_ = lean_array_push(v___x_344_, v_rbTk2_336_);
v___x_346_ = lean_box(1);
v___x_347_ = l_Lean_Fmt_fmtBinder(v___x_341_, v_ids_337_, v___x_342_, v_typeAscriptionTk_x3f_317_, v_type_x3f_318_, v___x_343_, v___x_345_, v___x_346_, v___y_319_, v___y_320_);
return v___x_347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStrictImplicitBinder___boxed(lean_object* v_x_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Fmt_fmtStrictImplicitBinder(v_x_359_, v_a_360_, v_a_361_);
lean_dec_ref(v_a_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1(){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_369_ = l_Lean_Fmt_fmtAttribute;
v___x_370_ = ((lean_object*)(l_Lean_Fmt_fmtStrictImplicitBinder___closed__1));
v___x_371_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___closed__1));
v___x_372_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtStrictImplicitBinder___boxed), 3, 0);
v___x_373_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_369_, v___x_370_, v___x_371_, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1___boxed(lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1();
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInstBinder(lean_object* v_x_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_Fmt_fmtInstBinder___closed__1));
lean_inc(v_x_385_);
v___x_389_ = l_Lean_Syntax_isOfKind(v_x_385_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_x_385_);
v___x_390_ = l_Lean_Fmt_Error_partialFormatter;
v___x_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v_a_387_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v_lbTk_408_; lean_object* v_id_x3f_410_; lean_object* v_typeAscriptionTk_x3f_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_392_ = lean_unsigned_to_nat(0u);
v_lbTk_408_ = l_Lean_Syntax_getArg(v_x_385_, v___x_392_);
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = l_Lean_Syntax_getArg(v_x_385_, v___x_424_);
v___x_426_ = l_Lean_Syntax_isNone(v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_425_);
v___x_428_ = l_Lean_Syntax_matchesNull(v___x_425_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v___x_425_);
lean_dec(v_lbTk_408_);
lean_dec(v_x_385_);
v___x_429_ = l_Lean_Fmt_Error_partialFormatter;
v___x_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_a_387_);
return v___x_430_;
}
else
{
lean_object* v_id_x3f_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_id_x3f_431_ = l_Lean_Syntax_getArg(v___x_425_, v___x_392_);
v___x_432_ = ((lean_object*)(l_Lean_Fmt_fmtInstBinder___closed__3));
lean_inc(v_id_x3f_431_);
v___x_433_ = l_Lean_Syntax_isOfKind(v_id_x3f_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v_id_x3f_431_);
lean_dec(v___x_425_);
lean_dec(v_lbTk_408_);
lean_dec(v_x_385_);
v___x_434_ = l_Lean_Fmt_Error_partialFormatter;
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v_a_387_);
return v___x_435_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_typeAscriptionTk_x3f_436_ = l_Lean_Syntax_getArg(v___x_425_, v___x_424_);
lean_dec(v___x_425_);
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v_id_x3f_431_);
v___x_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_438_, 0, v_typeAscriptionTk_x3f_436_);
v_id_x3f_410_ = v___x_437_;
v_typeAscriptionTk_x3f_411_ = v___x_438_;
v___y_412_ = v_a_386_;
v___y_413_ = v_a_387_;
goto v___jp_409_;
}
}
}
else
{
lean_object* v___x_439_; 
lean_dec(v___x_425_);
v___x_439_ = lean_box(0);
v_id_x3f_410_ = v___x_439_;
v_typeAscriptionTk_x3f_411_ = v___x_439_;
v___y_412_ = v_a_386_;
v___y_413_ = v_a_387_;
goto v___jp_409_;
}
v___jp_393_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_402_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__2));
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v___y_398_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_array_push(v___y_397_, v___y_396_);
v___x_406_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__3));
v___x_407_ = l_Lean_Fmt_fmtBinder(v___y_400_, v___y_401_, v___x_402_, v___y_395_, v___x_403_, v___x_404_, v___x_405_, v___x_406_, v___y_394_, v___y_399_);
return v___x_407_;
}
v___jp_409_:
{
lean_object* v___x_414_; lean_object* v_classType_415_; lean_object* v___x_416_; lean_object* v_rbTk_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_414_ = lean_unsigned_to_nat(2u);
v_classType_415_ = l_Lean_Syntax_getArg(v_x_385_, v___x_414_);
v___x_416_ = lean_unsigned_to_nat(3u);
v_rbTk_417_ = l_Lean_Syntax_getArg(v_x_385_, v___x_416_);
lean_dec(v_x_385_);
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_mk_empty_array_with_capacity(v___x_418_);
lean_inc_ref(v___x_419_);
v___x_420_ = lean_array_push(v___x_419_, v_lbTk_408_);
if (lean_obj_tag(v_id_x3f_410_) == 0)
{
lean_object* v___x_421_; 
v___x_421_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__2));
v___y_394_ = v___y_412_;
v___y_395_ = v_typeAscriptionTk_x3f_411_;
v___y_396_ = v_rbTk_417_;
v___y_397_ = v___x_419_;
v___y_398_ = v_classType_415_;
v___y_399_ = v___y_413_;
v___y_400_ = v___x_420_;
v___y_401_ = v___x_421_;
goto v___jp_393_;
}
else
{
lean_object* v_val_422_; lean_object* v___x_423_; 
v_val_422_ = lean_ctor_get(v_id_x3f_410_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v_id_x3f_410_, 1);
lean_inc_ref(v___x_419_);
v___x_423_ = lean_array_push(v___x_419_, v_val_422_);
v___y_394_ = v___y_412_;
v___y_395_ = v_typeAscriptionTk_x3f_411_;
v___y_396_ = v_rbTk_417_;
v___y_397_ = v___x_419_;
v___y_398_ = v_classType_415_;
v___y_399_ = v___y_413_;
v___y_400_ = v___x_420_;
v___y_401_ = v___x_423_;
goto v___jp_393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInstBinder___boxed(lean_object* v_x_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Fmt_fmtInstBinder(v_x_440_, v_a_441_, v_a_442_);
lean_dec_ref(v_a_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1(){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_450_ = l_Lean_Fmt_fmtAttribute;
v___x_451_ = ((lean_object*)(l_Lean_Fmt_fmtInstBinder___closed__1));
v___x_452_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___closed__1));
v___x_453_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInstBinder___boxed), 3, 0);
v___x_454_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_450_, v___x_451_, v___x_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1___boxed(lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1();
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstArrayRef(lean_object* v_x_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Fmt_fmtStructInstArrayRef___closed__1));
lean_inc(v_x_463_);
v___x_467_ = l_Lean_Syntax_isOfKind(v_x_463_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_x_463_);
v___x_468_ = l_Lean_Fmt_Error_partialFormatter;
v___x_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v_a_465_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; lean_object* v_lbTk_471_; lean_object* v___x_472_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v_lbTk_471_ = l_Lean_Syntax_getArg(v_x_463_, v___x_470_);
v___x_472_ = l_Lean_Fmt_fmt(v_lbTk_471_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v_a_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
v_a_474_ = lean_ctor_get(v___x_472_, 1);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_472_, 2);
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = l_Lean_Syntax_getArg(v_x_463_, v___x_475_);
v___x_477_ = l_Lean_Fmt_fmt(v___x_476_, v_a_464_, v_a_474_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v_a_479_; lean_object* v___x_480_; lean_object* v_rbTk_481_; lean_object* v___x_482_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
v_a_479_ = lean_ctor_get(v___x_477_, 1);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_477_, 2);
v___x_480_ = lean_unsigned_to_nat(2u);
v_rbTk_481_ = l_Lean_Syntax_getArg(v_x_463_, v___x_480_);
lean_dec(v_x_463_);
v___x_482_ = l_Lean_Fmt_fmt(v_rbTk_481_, v_a_464_, v_a_479_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_494_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_a_484_ = lean_ctor_get(v___x_482_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_494_ == 0)
{
v___x_486_ = v___x_482_;
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_488_ = 0;
v___x_489_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_489_, 0, v___x_488_);
lean_ctor_set_uint8(v___x_489_, 1, v___x_467_);
v___x_490_ = l_Lean_Fmt_Layouts_bracketed(v_a_473_, v_a_478_, v_a_483_, v___x_489_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_490_);
v___x_492_ = v___x_486_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_a_484_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_dec(v_a_478_);
lean_dec(v_a_473_);
return v___x_482_;
}
}
else
{
lean_dec(v_a_473_);
lean_dec(v_x_463_);
return v___x_477_;
}
}
else
{
lean_dec(v_x_463_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstArrayRef___boxed(lean_object* v_x_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Fmt_fmtStructInstArrayRef(v_x_495_, v_a_496_, v_a_497_);
lean_dec_ref(v_a_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1(){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_505_ = l_Lean_Fmt_fmtAttribute;
v___x_506_ = ((lean_object*)(l_Lean_Fmt_fmtStructInstArrayRef___closed__1));
v___x_507_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___closed__1));
v___x_508_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtStructInstArrayRef___boxed), 3, 0);
v___x_509_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_505_, v___x_506_, v___x_507_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1___boxed(lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1();
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0___redArg(lean_object* v_upperBound_525_, lean_object* v_seps_526_, lean_object* v_comps_527_, lean_object* v_a_528_, lean_object* v_b_529_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = lean_nat_dec_lt(v_a_528_, v_upperBound_525_);
if (v___x_530_ == 0)
{
lean_dec(v_a_528_);
return v_b_529_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_box(0);
v___x_533_ = lean_nat_sub(v_a_528_, v___x_531_);
v___x_534_ = lean_array_get_borrowed(v___x_532_, v_seps_526_, v___x_533_);
lean_dec(v___x_533_);
lean_inc(v___x_534_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
v___x_536_ = lean_array_get_borrowed(v___x_532_, v_comps_527_, v_a_528_);
lean_inc(v___x_536_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_array_push(v_b_529_, v___x_537_);
v___x_539_ = lean_nat_add(v_a_528_, v___x_531_);
lean_dec(v_a_528_);
v_a_528_ = v___x_539_;
v_b_529_ = v___x_538_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0___redArg___boxed(lean_object* v_upperBound_541_, lean_object* v_seps_542_, lean_object* v_comps_543_, lean_object* v_a_544_, lean_object* v_b_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0___redArg(v_upperBound_541_, v_seps_542_, v_comps_543_, v_a_544_, v_b_545_);
lean_dec_ref(v_comps_543_);
lean_dec_ref(v_seps_542_);
lean_dec(v_upperBound_541_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_splitStructInstLValIdent(lean_object* v_id_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_box(0);
lean_inc(v_id_547_);
v___x_549_ = l_Lean_Syntax_identComponents_x3f(v_id_547_, v___x_548_);
if (lean_obj_tag(v___x_549_) == 1)
{
lean_object* v_val_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_id_547_);
v_val_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v___x_549_, 1);
v_fst_551_ = lean_ctor_get(v_val_550_, 0);
v_snd_552_ = lean_ctor_get(v_val_550_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_val_550_);
if (v_isSharedCheck_569_ == 0)
{
v___x_554_ = v_val_550_;
v_isShared_555_ = v_isSharedCheck_569_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_snd_552_);
lean_inc(v_fst_551_);
lean_dec(v_val_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_569_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v_comps_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_556_ = lean_box(0);
v_comps_557_ = lean_array_mk(v_fst_551_);
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_array_get_size(v_comps_557_);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_array_get_borrowed(v___x_556_, v_comps_557_, v___x_560_);
lean_inc(v___x_561_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_561_);
lean_ctor_set(v___x_554_, 0, v___x_548_);
v___x_563_ = v___x_554_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_561_);
v___x_563_ = v_reuseFailAlloc_568_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; lean_object* v_r_565_; lean_object* v_seps_566_; lean_object* v___x_567_; 
v___x_564_ = lean_mk_empty_array_with_capacity(v___x_558_);
v_r_565_ = lean_array_push(v___x_564_, v___x_563_);
v_seps_566_ = lean_array_mk(v_snd_552_);
v___x_567_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0___redArg(v___x_559_, v_seps_566_, v_comps_557_, v___x_558_, v_r_565_);
lean_dec_ref(v_comps_557_);
lean_dec_ref(v_seps_566_);
return v___x_567_;
}
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v___x_549_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_548_);
lean_ctor_set(v___x_570_, 1, v_id_547_);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_mk_empty_array_with_capacity(v___x_571_);
v___x_573_ = lean_array_push(v___x_572_, v___x_570_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0(lean_object* v_upperBound_574_, lean_object* v_seps_575_, lean_object* v_comps_576_, lean_object* v_inst_577_, lean_object* v_R_578_, lean_object* v_a_579_, lean_object* v_b_580_, lean_object* v_c_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0___redArg(v_upperBound_574_, v_seps_575_, v_comps_576_, v_a_579_, v_b_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0___boxed(lean_object* v_upperBound_583_, lean_object* v_seps_584_, lean_object* v_comps_585_, lean_object* v_inst_586_, lean_object* v_R_587_, lean_object* v_a_588_, lean_object* v_b_589_, lean_object* v_c_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_splitStructInstLValIdent_spec__0(v_upperBound_583_, v_seps_584_, v_comps_585_, v_inst_586_, v_R_587_, v_a_588_, v_b_589_, v_c_590_);
lean_dec_ref(v_comps_585_);
lean_dec_ref(v_seps_584_);
lean_dec(v_upperBound_583_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0___redArg(lean_object* v_as_592_, size_t v_i_593_, size_t v_stop_594_, lean_object* v_b_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_a_598_; lean_object* v_a_599_; uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_eq(v_i_593_, v_stop_594_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v_kind_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_605_ = lean_array_uget_borrowed(v_as_592_, v_i_593_);
lean_inc(v___x_605_);
v_kind_606_ = l_Lean_Syntax_getKind(v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_Fmt_fmtStrictImplicitBinder___closed__3));
v___x_608_ = lean_name_eq(v_kind_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = ((lean_object*)(l_Lean_Fmt_fmtStructInstArrayRef___closed__1));
v___x_610_ = lean_name_eq(v_kind_606_, v___x_609_);
lean_dec(v_kind_606_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec_ref(v_b_595_);
v___x_611_ = l_Lean_Fmt_Error_partialFormatter;
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___y_596_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_613_ = lean_box(0);
lean_inc(v___x_605_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_605_);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_mk_empty_array_with_capacity(v___x_615_);
v___x_617_ = lean_array_push(v___x_616_, v___x_614_);
v_a_598_ = v___x_617_;
v_a_599_ = v___y_596_;
goto v___jp_597_;
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_kind_606_);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = l_Lean_Fmt_getStxArg_x21___redArg(v___x_605_, v___x_618_, v___y_596_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
v_a_621_ = lean_ctor_get(v___x_619_, 1);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_619_, 2);
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = l_Lean_Fmt_getStxArg_x21___redArg(v___x_605_, v___x_622_, v_a_621_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_659_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_a_625_ = lean_ctor_get(v___x_623_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_659_ == 0)
{
v___x_627_ = v___x_623_;
v_isShared_628_ = v_isSharedCheck_659_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_659_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
lean_inc(v_a_624_);
v___x_629_ = l_Lean_Syntax_getKind(v_a_624_);
v___x_630_ = ((lean_object*)(l_Lean_Fmt_fmtInstBinder___closed__3));
v___x_631_ = lean_name_eq(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_Fmt_structInstLValKinds___closed__1));
v___x_633_ = lean_name_eq(v___x_629_, v___x_632_);
lean_dec(v___x_629_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec(v_a_624_);
lean_dec(v_a_620_);
lean_dec_ref(v_b_595_);
v___x_634_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 1);
lean_ctor_set(v___x_627_, 0, v___x_634_);
v___x_636_ = v___x_627_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_a_625_);
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
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_del_object(v___x_627_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_a_620_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_a_624_);
v___x_640_ = lean_mk_empty_array_with_capacity(v___x_622_);
v___x_641_ = lean_array_push(v___x_640_, v___x_639_);
v_a_598_ = v___x_641_;
v_a_599_ = v_a_625_;
goto v___jp_597_;
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
lean_dec(v___x_629_);
lean_del_object(v___x_627_);
v___x_642_ = l_Lean_Fmt_splitStructInstLValIdent(v_a_624_);
v___x_643_ = lean_array_get_size(v___x_642_);
v___x_644_ = lean_nat_dec_lt(v___x_618_, v___x_643_);
if (v___x_644_ == 0)
{
lean_dec(v_a_620_);
v_a_598_ = v___x_642_;
v_a_599_ = v_a_625_;
goto v___jp_597_;
}
else
{
lean_object* v_v_645_; lean_object* v_elem_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_657_; 
v_v_645_ = lean_array_fget(v___x_642_, v___x_618_);
v_elem_646_ = lean_ctor_get(v_v_645_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_v_645_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v_v_645_, 0);
lean_dec(v_unused_658_);
v___x_648_ = v_v_645_;
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_elem_646_);
lean_dec(v_v_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v_xs_x27_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_650_ = lean_box(0);
v_xs_x27_651_ = lean_array_fset(v___x_642_, v___x_618_, v___x_650_);
v___x_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_652_, 0, v_a_620_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_652_);
v___x_654_ = v___x_648_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_elem_646_);
v___x_654_ = v_reuseFailAlloc_656_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; 
v___x_655_ = lean_array_fset(v_xs_x27_651_, v___x_618_, v___x_654_);
v_a_598_ = v___x_655_;
v_a_599_ = v_a_625_;
goto v___jp_597_;
}
}
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_a_620_);
lean_dec_ref(v_b_595_);
v_a_660_ = lean_ctor_get(v___x_623_, 0);
v_a_661_ = lean_ctor_get(v___x_623_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_623_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_inc(v_a_660_);
lean_dec(v___x_623_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_660_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_a_669_; lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_b_595_);
v_a_669_ = lean_ctor_get(v___x_619_, 0);
v_a_670_ = lean_ctor_get(v___x_619_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_619_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_inc(v_a_669_);
lean_dec(v___x_619_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_669_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
lean_object* v___x_678_; 
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_b_595_);
lean_ctor_set(v___x_678_, 1, v___y_596_);
return v___x_678_;
}
v___jp_597_:
{
lean_object* v___x_600_; size_t v___x_601_; size_t v___x_602_; 
v___x_600_ = l_Array_append___redArg(v_b_595_, v_a_598_);
lean_dec_ref(v_a_598_);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_add(v_i_593_, v___x_601_);
v_i_593_ = v___x_602_;
v_b_595_ = v___x_600_;
v___y_596_ = v_a_599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0___redArg___boxed(lean_object* v_as_679_, lean_object* v_i_680_, lean_object* v_stop_681_, lean_object* v_b_682_, lean_object* v___y_683_){
_start:
{
size_t v_i_boxed_684_; size_t v_stop_boxed_685_; lean_object* v_res_686_; 
v_i_boxed_684_ = lean_unbox_usize(v_i_680_);
lean_dec(v_i_680_);
v_stop_boxed_685_ = lean_unbox_usize(v_stop_681_);
lean_dec(v_stop_681_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0___redArg(v_as_679_, v_i_boxed_684_, v_stop_boxed_685_, v_b_682_, v___y_683_);
lean_dec_ref(v_as_679_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_splitStructInstLValRhs(lean_object* v_rhs_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_692_ = l_Lean_Syntax_getArgs(v_rhs_689_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = ((lean_object*)(l_Lean_Fmt_splitStructInstLValRhs___closed__0));
v___x_695_ = lean_array_get_size(v___x_692_);
v___x_696_ = lean_nat_dec_lt(v___x_693_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
lean_dec_ref(v___x_692_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_694_);
lean_ctor_set(v___x_697_, 1, v_a_691_);
return v___x_697_;
}
else
{
size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v___x_698_ = ((size_t)0ULL);
v___x_699_ = lean_usize_of_nat(v___x_695_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0___redArg(v___x_692_, v___x_698_, v___x_699_, v___x_694_, v_a_691_);
lean_dec_ref(v___x_692_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_splitStructInstLValRhs___boxed(lean_object* v_rhs_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Fmt_splitStructInstLValRhs(v_rhs_701_, v_a_702_, v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_rhs_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0(lean_object* v_as_705_, size_t v_i_706_, size_t v_stop_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0___redArg(v_as_705_, v_i_706_, v_stop_707_, v_b_708_, v___y_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0___boxed(lean_object* v_as_712_, lean_object* v_i_713_, lean_object* v_stop_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
size_t v_i_boxed_718_; size_t v_stop_boxed_719_; lean_object* v_res_720_; 
v_i_boxed_718_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_stop_boxed_719_ = lean_unbox_usize(v_stop_714_);
lean_dec(v_stop_714_);
v_res_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_splitStructInstLValRhs_spec__0(v_as_712_, v_i_boxed_718_, v_stop_boxed_719_, v_b_715_, v___y_716_, v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_as_712_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___lam__0(lean_object* v___y_721_){
_start:
{
lean_inc_ref(v___y_721_);
return v___y_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___lam__0___boxed(lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___lam__0(v___y_722_);
lean_dec_ref(v___y_722_);
return v_res_723_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___closed__1(void){
_start:
{
lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___f_725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___closed__0));
v___x_726_ = l_Lean_Fmt_TaggedDoc_break;
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___f_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0(lean_object* v_as_728_, size_t v_i_729_, size_t v_stop_730_, lean_object* v_b_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = lean_usize_dec_eq(v_i_729_, v_stop_730_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v_dotTk_x3f_736_; lean_object* v_elem_737_; lean_object* v___x_738_; 
v___x_735_ = lean_array_uget_borrowed(v_as_728_, v_i_729_);
v_dotTk_x3f_736_ = lean_ctor_get(v___x_735_, 0);
v_elem_737_ = lean_ctor_get(v___x_735_, 1);
lean_inc(v_dotTk_x3f_736_);
v___x_738_ = l_Lean_Fmt_fmt_x3f(v_dotTk_x3f_736_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v_a_740_; lean_object* v___x_741_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
v_a_740_ = lean_ctor_get(v___x_738_, 1);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_738_, 2);
lean_inc(v_elem_737_);
v___x_741_ = l_Lean_Fmt_fmt(v_elem_737_, v___y_732_, v_a_740_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v_a_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; size_t v___x_755_; size_t v___x_756_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
v_a_743_ = lean_ctor_get(v___x_741_, 1);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_741_, 2);
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v_a_739_);
v___x_745_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___closed__1);
v___x_746_ = l_Lean_Fmt_TaggedDoc_Component_withSepBefore(v___x_744_, v___x_745_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v_a_742_);
v___x_749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
lean_ctor_set(v___x_749_, 2, v___x_747_);
v___x_750_ = lean_unsigned_to_nat(2u);
v___x_751_ = lean_mk_empty_array_with_capacity(v___x_750_);
v___x_752_ = lean_array_push(v___x_751_, v___x_746_);
v___x_753_ = lean_array_push(v___x_752_, v___x_749_);
v___x_754_ = l_Array_append___redArg(v_b_731_, v___x_753_);
lean_dec_ref(v___x_753_);
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_add(v_i_729_, v___x_755_);
v_i_729_ = v___x_756_;
v_b_731_ = v___x_754_;
v___y_733_ = v_a_743_;
goto _start;
}
else
{
lean_object* v_a_758_; lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_a_739_);
lean_dec_ref(v_b_731_);
v_a_758_ = lean_ctor_get(v___x_741_, 0);
v_a_759_ = lean_ctor_get(v___x_741_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_741_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_inc(v_a_758_);
lean_dec(v___x_741_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_758_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_b_731_);
v_a_767_ = lean_ctor_get(v___x_738_, 0);
v_a_768_ = lean_ctor_get(v___x_738_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_738_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_inc(v_a_767_);
lean_dec(v___x_738_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_767_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_b_731_);
lean_ctor_set(v___x_776_, 1, v___y_733_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0___boxed(lean_object* v_as_777_, lean_object* v_i_778_, lean_object* v_stop_779_, lean_object* v_b_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
size_t v_i_boxed_783_; size_t v_stop_boxed_784_; lean_object* v_res_785_; 
v_i_boxed_783_ = lean_unbox_usize(v_i_778_);
lean_dec(v_i_778_);
v_stop_boxed_784_ = lean_unbox_usize(v_stop_779_);
lean_dec(v_stop_779_);
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0(v_as_777_, v_i_boxed_783_, v_stop_boxed_784_, v_b_780_, v___y_781_, v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v_as_777_);
return v_res_785_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Fmt_fmtStructInstLVal_spec__1(lean_object* v_a_786_, lean_object* v_x_787_){
_start:
{
if (lean_obj_tag(v_x_787_) == 0)
{
uint8_t v___x_788_; 
v___x_788_ = 0;
return v___x_788_;
}
else
{
lean_object* v_head_789_; lean_object* v_tail_790_; uint8_t v___x_791_; 
v_head_789_ = lean_ctor_get(v_x_787_, 0);
v_tail_790_ = lean_ctor_get(v_x_787_, 1);
v___x_791_ = lean_name_eq(v_a_786_, v_head_789_);
if (v___x_791_ == 0)
{
v_x_787_ = v_tail_790_;
goto _start;
}
else
{
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Fmt_fmtStructInstLVal_spec__1___boxed(lean_object* v_a_793_, lean_object* v_x_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_List_elem___at___00Lean_Fmt_fmtStructInstLVal_spec__1(v_a_793_, v_x_794_);
lean_dec(v_x_794_);
lean_dec(v_a_793_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstLVal(lean_object* v_stx_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_a_803_; lean_object* v_a_804_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_799_, v___x_809_, v_a_801_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_876_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_a_812_ = lean_ctor_get(v___x_810_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_876_ == 0)
{
v___x_814_ = v___x_810_;
v_isShared_815_ = v_isSharedCheck_876_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_876_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___y_817_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = ((lean_object*)(l_Lean_Fmt_structInstLValKinds));
lean_inc(v_a_811_);
v___x_862_ = l_Lean_Syntax_getKind(v_a_811_);
v___x_863_ = l_List_elem___at___00Lean_Fmt_fmtStructInstLVal_spec__1(v___x_862_, v___x_861_);
lean_dec(v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_866_; 
lean_dec(v_a_811_);
v___x_864_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 1);
lean_ctor_set(v___x_814_, 0, v___x_864_);
v___x_866_ = v___x_814_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_a_812_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
else
{
lean_object* v___x_868_; uint8_t v___x_869_; 
lean_del_object(v___x_814_);
v___x_868_ = ((lean_object*)(l_Lean_Fmt_fmtInstBinder___closed__3));
lean_inc(v_a_811_);
v___x_869_ = l_Lean_Syntax_isOfKind(v_a_811_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_870_ = lean_box(0);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v_a_811_);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_mk_empty_array_with_capacity(v___x_872_);
v___x_874_ = lean_array_push(v___x_873_, v___x_871_);
v___y_817_ = v___x_874_;
goto v___jp_816_;
}
else
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Fmt_splitStructInstLValIdent(v_a_811_);
v___y_817_ = v___x_875_;
goto v___jp_816_;
}
}
v___jp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_799_, v___x_818_, v_a_812_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
v_a_821_ = lean_ctor_get(v___x_819_, 1);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_819_, 2);
v___x_822_ = l_Lean_Fmt_splitStructInstLValRhs(v_a_820_, v_a_800_, v_a_821_);
lean_dec(v_a_820_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
v_a_824_ = lean_ctor_get(v___x_822_, 1);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_822_, 2);
v___x_825_ = l_Array_append___redArg(v___y_817_, v_a_823_);
lean_dec(v_a_823_);
v___x_826_ = ((lean_object*)(l_Lean_Fmt_fmtStructInstLVal___closed__0));
v___x_827_ = lean_array_get_size(v___x_825_);
v___x_828_ = lean_nat_dec_lt(v___x_809_, v___x_827_);
if (v___x_828_ == 0)
{
lean_dec_ref(v___x_825_);
v_a_803_ = v___x_826_;
v_a_804_ = v_a_824_;
goto v___jp_802_;
}
else
{
size_t v___x_829_; size_t v___x_830_; lean_object* v___x_831_; 
v___x_829_ = ((size_t)0ULL);
v___x_830_ = lean_usize_of_nat(v___x_827_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtStructInstLVal_spec__0(v___x_825_, v___x_829_, v___x_830_, v___x_826_, v_a_800_, v_a_824_);
lean_dec_ref(v___x_825_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v_a_833_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
v_a_833_ = lean_ctor_get(v___x_831_, 1);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_831_, 2);
v_a_803_ = v_a_832_;
v_a_804_ = v_a_833_;
goto v___jp_802_;
}
else
{
lean_object* v_a_834_; lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_834_ = lean_ctor_get(v___x_831_, 0);
v_a_835_ = lean_ctor_get(v___x_831_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_831_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_inc(v_a_834_);
lean_dec(v___x_831_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_834_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v___y_817_);
v_a_843_ = lean_ctor_get(v___x_822_, 0);
v_a_844_ = lean_ctor_get(v___x_822_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_822_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_inc(v_a_843_);
lean_dec(v___x_822_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_843_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec_ref(v___y_817_);
v_a_852_ = lean_ctor_get(v___x_819_, 0);
v_a_853_ = lean_ctor_get(v___x_819_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_819_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_inc(v_a_852_);
lean_dec(v___x_819_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_852_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_a_877_ = lean_ctor_get(v___x_810_, 0);
v_a_878_ = lean_ctor_get(v___x_810_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_810_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_inc(v_a_877_);
lean_dec(v___x_810_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_877_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
v___jp_802_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_805_ = l_Lean_Fmt_TaggedDoc_combine(v_a_803_);
lean_dec_ref(v_a_803_);
v___x_806_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_805_);
v___x_807_ = l_Lean_Fmt_TaggedDoc_nested(v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v_a_804_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstLVal___boxed(lean_object* v_stx_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Fmt_fmtStructInstLVal(v_stx_886_, v_a_887_, v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_stx_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1(){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_902_ = l_Lean_Fmt_fmtAttribute;
v___x_903_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1));
v___x_904_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__3));
v___x_905_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtStructInstLVal___boxed), 3, 0);
v___x_906_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_902_, v___x_903_, v___x_904_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___boxed(lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1();
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_convertStructInstFieldBinders_spec__0(size_t v_sz_909_, size_t v_i_910_, lean_object* v_bs_911_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_convertStructInstFieldBinders_spec__0___boxed(lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_bs_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_924_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_convertStructInstFieldBinders_spec__0(v_sz_boxed_923_, v_i_boxed_924_, v_bs_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_convertStructInstFieldBinders(lean_object* v_binders_926_){
_start:
{
size_t v_sz_927_; size_t v___x_928_; lean_object* v___x_929_; 
v_sz_927_ = lean_array_size(v_binders_926_);
v___x_928_ = ((size_t)0ULL);
v___x_929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_convertStructInstFieldBinders_spec__0(v_sz_927_, v___x_928_, v_binders_926_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___lam__0(lean_object* v_x_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___lam__0___boxed(lean_object* v_x_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___lam__0(v_x_932_);
lean_dec_ref(v_x_932_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_mkStructInstFieldDecl___lam__0(lean_object* v_v_944_, lean_object* v_f_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_apply_1(v_v_944_, v___y_946_);
v___x_948_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v___x_947_, v_f_945_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_mkStructInstFieldDecl(lean_object* v_format_950_){
_start:
{
lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___f_951_ = ((lean_object*)(l_Lean_Fmt_mkStructInstFieldDecl___closed__0));
v___f_952_ = ((lean_object*)(l_Lean_Fmt_instInhabitedStructInstFieldDecl_default___closed__0));
v___x_953_ = ((lean_object*)(l_Lean_Fmt_instImpl_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15_));
v___x_954_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_955_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___f_952_, v___x_953_, v___x_954_, v_format_950_, v___f_951_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStructInstFieldDecl_x3f(lean_object* v_doc_956_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_Fmt_instImpl_00___x40_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_3182002522____hygCtx___hyg_15_));
v___x_958_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_957_, v_doc_956_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtStructInstField___closed__4(void){
_start:
{
lean_object* v___x_971_; lean_object* v_binders_972_; 
v___x_971_ = ((lean_object*)(l_Lean_Fmt_fmtExplicitBinder___closed__2));
v_binders_972_ = l_Lean_Fmt_convertStructInstFieldBinders(v___x_971_);
return v_binders_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstField(lean_object* v_x_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = ((lean_object*)(l_Lean_Fmt_fmtStructInstField___closed__1));
lean_inc(v_x_973_);
v___x_1003_ = l_Lean_Syntax_isOfKind(v_x_973_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec(v_x_973_);
v___x_1004_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_a_975_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = l_Lean_Syntax_getArg(v_x_973_, v___x_1006_);
v___x_1036_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1___closed__1));
lean_inc(v___x_1007_);
v___x_1037_ = l_Lean_Syntax_isOfKind(v___x_1007_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec(v___x_1007_);
lean_dec(v_x_973_);
v___x_1038_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v_a_975_);
return v___x_1039_;
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = l_Lean_Syntax_getArg(v_x_973_, v___x_1040_);
lean_dec(v_x_973_);
v___x_1042_ = l_Lean_Syntax_isNone(v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1041_);
v___x_1044_ = l_Lean_Syntax_matchesNull(v___x_1041_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec(v___x_1041_);
lean_dec(v___x_1007_);
v___x_1045_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v_a_975_);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; lean_object* v_typeAscriptionTk_x3f_1049_; lean_object* v_type_x3f_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1047_ = l_Lean_Syntax_getArg(v___x_1041_, v___x_1006_);
v___x_1066_ = l_Lean_Syntax_getArg(v___x_1041_, v___x_1040_);
v___x_1067_ = l_Lean_Syntax_isNone(v___x_1066_);
if (v___x_1067_ == 0)
{
uint8_t v___x_1068_; 
lean_inc(v___x_1066_);
v___x_1068_ = l_Lean_Syntax_matchesNull(v___x_1066_, v___x_1040_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec(v___x_1066_);
lean_dec(v___x_1047_);
lean_dec(v___x_1041_);
lean_dec(v___x_1007_);
v___x_1069_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_a_975_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = l_Lean_Syntax_getArg(v___x_1066_, v___x_1006_);
lean_dec(v___x_1066_);
v___x_1072_ = ((lean_object*)(l_Lean_Fmt_fmtStructInstField___closed__3));
lean_inc(v___x_1071_);
v___x_1073_ = l_Lean_Syntax_isOfKind(v___x_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec(v___x_1071_);
lean_dec(v___x_1047_);
lean_dec(v___x_1041_);
lean_dec(v___x_1007_);
v___x_1074_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v_a_975_);
return v___x_1075_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_1076_; lean_object* v_type_x3f_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_typeAscriptionTk_x3f_1076_ = l_Lean_Syntax_getArg(v___x_1071_, v___x_1006_);
v_type_x3f_1077_ = l_Lean_Syntax_getArg(v___x_1071_, v___x_1040_);
lean_dec(v___x_1071_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_typeAscriptionTk_x3f_1076_);
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_type_x3f_1077_);
v_typeAscriptionTk_x3f_1049_ = v___x_1078_;
v_type_x3f_1050_ = v___x_1079_;
v___y_1051_ = v_a_974_;
v___y_1052_ = v_a_975_;
goto v___jp_1048_;
}
}
}
else
{
lean_object* v___x_1080_; 
lean_dec(v___x_1066_);
v___x_1080_ = lean_box(0);
v_typeAscriptionTk_x3f_1049_ = v___x_1080_;
v_type_x3f_1050_ = v___x_1080_;
v___y_1051_ = v_a_974_;
v___y_1052_ = v_a_975_;
goto v___jp_1048_;
}
v___jp_1048_:
{
lean_object* v___x_1053_; lean_object* v_structInstFieldDecl_x3f_1054_; lean_object* v_binders_x3f_1055_; lean_object* v___x_1056_; lean_object* v_binders_1057_; 
v___x_1053_ = lean_unsigned_to_nat(2u);
v_structInstFieldDecl_x3f_1054_ = l_Lean_Syntax_getArg(v___x_1041_, v___x_1053_);
lean_dec(v___x_1041_);
v_binders_x3f_1055_ = l_Lean_Syntax_getArgs(v___x_1047_);
lean_dec(v___x_1047_);
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_structInstFieldDecl_x3f_1054_);
v_binders_1057_ = l_Lean_Fmt_convertStructInstFieldBinders(v_binders_x3f_1055_);
if (lean_obj_tag(v_type_x3f_1050_) == 0)
{
v___y_1030_ = v___y_1051_;
v___y_1031_ = v___x_1056_;
v___y_1032_ = v_typeAscriptionTk_x3f_1049_;
v___y_1033_ = v___y_1052_;
v___y_1034_ = v_binders_1057_;
goto v___jp_1029_;
}
else
{
lean_object* v_val_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_val_1058_ = lean_ctor_get(v_type_x3f_1050_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_type_x3f_1050_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v_type_x3f_1050_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_val_1058_);
lean_dec(v_type_x3f_1050_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_val_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
v___y_1009_ = v___y_1051_;
v___y_1010_ = v___x_1056_;
v___y_1011_ = v_typeAscriptionTk_x3f_1049_;
v___y_1012_ = v___y_1052_;
v___y_1013_ = v_binders_1057_;
v___y_1014_ = v___x_1063_;
goto v___jp_1008_;
}
}
}
}
}
}
else
{
lean_object* v___x_1081_; lean_object* v_binders_1082_; 
lean_dec(v___x_1041_);
v___x_1081_ = lean_box(0);
v_binders_1082_ = lean_obj_once(&l_Lean_Fmt_fmtStructInstField___closed__4, &l_Lean_Fmt_fmtStructInstField___closed__4_once, _init_l_Lean_Fmt_fmtStructInstField___closed__4);
v___y_1030_ = v_a_974_;
v___y_1031_ = v___x_1081_;
v___y_1032_ = v___x_1081_;
v___y_1033_ = v_a_975_;
v___y_1034_ = v_binders_1082_;
goto v___jp_1029_;
}
}
v___jp_1008_:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Fmt_fmtLocalSignature(v___x_1007_, v___y_1013_, v___y_1011_, v___y_1014_, v___y_1009_, v___y_1012_);
if (lean_obj_tag(v___x_1015_) == 0)
{
if (lean_obj_tag(v___y_1010_) == 0)
{
lean_object* v_a_1016_; lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
v_a_1017_ = lean_ctor_get(v___x_1015_, 1);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1015_, 2);
v___x_1018_ = lean_box(0);
v___y_977_ = v___y_1009_;
v___y_978_ = v_a_1017_;
v___y_979_ = v_a_1016_;
v___y_980_ = v___x_1018_;
goto v___jp_976_;
}
else
{
lean_object* v_a_1019_; lean_object* v_a_1020_; lean_object* v_val_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_a_1019_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1019_);
v_a_1020_ = lean_ctor_get(v___x_1015_, 1);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1015_, 2);
v_val_1021_ = lean_ctor_get(v___y_1010_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___y_1010_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___y_1010_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_val_1021_);
lean_dec(v___y_1010_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_val_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
v___y_977_ = v___y_1009_;
v___y_978_ = v_a_1020_;
v___y_979_ = v_a_1019_;
v___y_980_ = v___x_1026_;
goto v___jp_976_;
}
}
}
}
else
{
lean_dec(v___y_1010_);
return v___x_1015_;
}
}
v___jp_1029_:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_box(0);
v___y_1009_ = v___y_1030_;
v___y_1010_ = v___y_1031_;
v___y_1011_ = v___y_1032_;
v___y_1012_ = v___y_1033_;
v___y_1013_ = v___y_1034_;
v___y_1014_ = v___x_1035_;
goto v___jp_1008_;
}
}
v___jp_976_:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_Fmt_fmt_x3f(v___y_980_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1001_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_a_983_ = lean_ctor_get(v___x_981_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_985_ = v___x_981_;
v_isShared_986_ = v_isSharedCheck_1001_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1001_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
uint8_t v___x_987_; 
v___x_987_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_982_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_Fmt_getStructInstFieldDecl_x3f(v_a_982_);
if (lean_obj_tag(v___x_988_) == 1)
{
lean_object* v_val_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v_val_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_val_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = lean_apply_1(v_val_989_, v___y_979_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_990_);
v___x_992_ = v___x_985_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_a_983_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
else
{
lean_object* v___x_994_; lean_object* v___x_996_; 
lean_dec(v___x_988_);
lean_dec_ref(v___y_979_);
v___x_994_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 1);
lean_ctor_set(v___x_985_, 0, v___x_994_);
v___x_996_ = v___x_985_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_a_983_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v___x_999_; 
lean_dec(v_a_982_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___y_979_);
v___x_999_ = v___x_985_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___y_979_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_a_983_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_dec_ref(v___y_979_);
return v___x_981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStructInstField___boxed(lean_object* v_x_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Fmt_fmtStructInstField(v_x_1083_, v_a_1084_, v_a_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1(){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1093_ = l_Lean_Fmt_fmtAttribute;
v___x_1094_ = ((lean_object*)(l_Lean_Fmt_fmtStructInstField___closed__1));
v___x_1095_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___closed__1));
v___x_1096_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtStructInstField___boxed), 3, 0);
v___x_1097_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1093_, v___x_1094_, v___x_1095_, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1___boxed(lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1();
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeq1Indented(lean_object* v_x_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_Fmt_fmtTacticSeq1Indented___closed__2));
lean_inc(v_x_1108_);
v___x_1112_ = l_Lean_Syntax_isOfKind(v_x_1108_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v_x_1108_);
v___x_1113_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_a_1110_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v_tactics_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = l_Lean_Syntax_getArg(v_x_1108_, v___x_1115_);
lean_dec(v_x_1108_);
v___x_1117_ = ((lean_object*)(l_Lean_Fmt_fmtTacticSeq1Indented___closed__3));
v_tactics_1118_ = l_Lean_Syntax_getArgs(v___x_1116_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v___x_1120_ = l_Lean_Fmt_fmtSeq___redArg(v___x_1117_, v_tactics_1118_, v___x_1119_, v_a_1109_, v_a_1110_);
lean_dec_ref(v_tactics_1118_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeq1Indented___boxed(lean_object* v_x_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Fmt_fmtTacticSeq1Indented(v_x_1121_, v_a_1122_, v_a_1123_);
lean_dec_ref(v_a_1122_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1(){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1131_ = l_Lean_Fmt_fmtAttribute;
v___x_1132_ = ((lean_object*)(l_Lean_Fmt_fmtTacticSeq1Indented___closed__2));
v___x_1133_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___closed__1));
v___x_1134_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticSeq1Indented___boxed), 3, 0);
v___x_1135_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1131_, v___x_1132_, v___x_1133_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1___boxed(lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1();
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeqBracketed(lean_object* v_x_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_Lean_Fmt_fmtTacticSeqBracketed___closed__1));
lean_inc(v_x_1144_);
v___x_1148_ = l_Lean_Syntax_isOfKind(v_x_1144_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec(v_x_1144_);
v___x_1149_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v_a_1146_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; lean_object* v_lbTk_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_unsigned_to_nat(0u);
v_lbTk_1152_ = l_Lean_Syntax_getArg(v_x_1144_, v___x_1151_);
v___x_1153_ = l_Lean_Fmt_fmt(v_lbTk_1152_, v_a_1145_, v_a_1146_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v_a_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v_tactics_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
v_a_1155_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1153_, 2);
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = l_Lean_Syntax_getArg(v_x_1144_, v___x_1156_);
v___x_1158_ = ((lean_object*)(l_Lean_Fmt_fmtTacticSeq1Indented___closed__3));
v_tactics_1159_ = l_Lean_Syntax_getArgs(v___x_1157_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v___x_1161_ = l_Lean_Fmt_fmtSeq___redArg(v___x_1158_, v_tactics_1159_, v___x_1160_, v_a_1145_, v_a_1155_);
lean_dec_ref(v_tactics_1159_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v_rbTk_1165_; lean_object* v___x_1166_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
v_a_1163_ = lean_ctor_get(v___x_1161_, 1);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1161_, 2);
v___x_1164_ = lean_unsigned_to_nat(2u);
v_rbTk_1165_ = l_Lean_Syntax_getArg(v_x_1144_, v___x_1164_);
lean_dec(v_x_1144_);
v___x_1166_ = l_Lean_Fmt_fmt(v_rbTk_1165_, v_a_1145_, v_a_1163_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1179_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_a_1168_ = lean_ctor_get(v___x_1166_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1170_ = v___x_1166_;
v_isShared_1171_ = v_isSharedCheck_1179_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1179_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1172_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_1173_ = 1;
v___x_1174_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*1, v___x_1148_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*1 + 1, v___x_1173_);
v___x_1175_ = l_Lean_Fmt_Layouts_bracketed(v_a_1154_, v_a_1162_, v_a_1167_, v___x_1174_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1175_);
v___x_1177_ = v___x_1170_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_a_1168_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_dec(v_a_1162_);
lean_dec(v_a_1154_);
return v___x_1166_;
}
}
else
{
lean_dec(v_a_1154_);
lean_dec(v_x_1144_);
return v___x_1161_;
}
}
else
{
lean_dec(v_x_1144_);
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeqBracketed___boxed(lean_object* v_x_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Fmt_fmtTacticSeqBracketed(v_x_1180_, v_a_1181_, v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1(){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1190_ = l_Lean_Fmt_fmtAttribute;
v___x_1191_ = ((lean_object*)(l_Lean_Fmt_fmtTacticSeqBracketed___closed__1));
v___x_1192_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___closed__1));
v___x_1193_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticSeqBracketed___boxed), 3, 0);
v___x_1194_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1190_, v___x_1191_, v___x_1192_, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1___boxed(lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1();
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeq(lean_object* v_x_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_Lean_Fmt_fmtTacticSeq___closed__1));
lean_inc(v_x_1203_);
v___x_1207_ = l_Lean_Syntax_isOfKind(v_x_1203_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_x_1203_);
v___x_1208_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v_a_1205_);
return v___x_1209_;
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = l_Lean_Syntax_getArg(v_x_1203_, v___x_1210_);
lean_dec(v_x_1203_);
v___x_1212_ = ((lean_object*)(l_Lean_Fmt_fmtTacticSeq1Indented___closed__2));
lean_inc(v___x_1211_);
v___x_1213_ = l_Lean_Syntax_isOfKind(v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_Fmt_fmtTacticSeqBracketed___closed__1));
lean_inc(v___x_1211_);
v___x_1215_ = l_Lean_Syntax_isOfKind(v___x_1211_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec(v___x_1211_);
v___x_1216_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_a_1205_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Fmt_fmt(v___x_1211_, v_a_1204_, v_a_1205_);
return v___x_1218_;
}
}
else
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Fmt_fmt(v___x_1211_, v_a_1204_, v_a_1205_);
return v___x_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticSeq___boxed(lean_object* v_x_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_Fmt_fmtTacticSeq(v_x_1220_, v_a_1221_, v_a_1222_);
lean_dec_ref(v_a_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1(){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1230_ = l_Lean_Fmt_fmtAttribute;
v___x_1231_ = ((lean_object*)(l_Lean_Fmt_fmtTacticSeq___closed__1));
v___x_1232_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___closed__1));
v___x_1233_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticSeq___boxed), 3, 0);
v___x_1234_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1230_, v___x_1231_, v___x_1232_, v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1___boxed(lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1();
return v_res_1236_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtHole___regBuiltin_Lean_Fmt_fmtHole__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtSyntheticHole___regBuiltin_Lean_Fmt_fmtSyntheticHole__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtOmission___regBuiltin_Lean_Fmt_fmtOmission__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtExplicitBinder___regBuiltin_Lean_Fmt_fmtExplicitBinder__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtImplicitBinder___regBuiltin_Lean_Fmt_fmtImplicitBinder__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStrictImplicitBinder___regBuiltin_Lean_Fmt_fmtStrictImplicitBinder__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtInstBinder___regBuiltin_Lean_Fmt_fmtInstBinder__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstArrayRef___regBuiltin_Lean_Fmt_fmtStructInstArrayRef__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstLVal___regBuiltin_Lean_Fmt_fmtStructInstLVal__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtStructInstField___regBuiltin_Lean_Fmt_fmtStructInstField__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq1Indented___regBuiltin_Lean_Fmt_fmtTacticSeq1Indented__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeqBracketed___regBuiltin_Lean_Fmt_fmtTacticSeqBracketed__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Term_Basic_0__Lean_Fmt_fmtTacticSeq___regBuiltin_Lean_Fmt_fmtTacticSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
