// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Do.SPred.Notation
// Imports: public import Lean.Fmt.Formatters.Std.Do.SPred.Notation.Basic public import Lean.Fmt.FmtM.Basic meta import Std.Do.SPred.Notation import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Fmt_infixFmtAttribute;
static const lean_string_object l_Lean_Fmt_fmtSPredPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtSPredPure___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSPredPure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Fmt_fmtSPredPure___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSPredPure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term⌜_⌝"};
static const lean_object* l_Lean_Fmt_fmtSPredPure___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtSPredPure___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtSPredPure___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtSPredPure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__2_value),LEAN_SCALAR_PTR_LITERAL(190, 155, 137, 127, 35, 248, 173, 10)}};
static const lean_object* l_Lean_Fmt_fmtSPredPure___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredPure___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtSPredPure"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(236, 88, 194, 199, 242, 79, 11, 22)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSPredTautology___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term⊢ₛ_"};
static const lean_object* l_Lean_Fmt_fmtSPredTautology___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSPredTautology___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSPredTautology___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtSPredTautology___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSPredTautology___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtSPredTautology___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSPredTautology___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSPredTautology___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 33, 26, 243, 26, 184, 240, 184)}};
static const lean_object* l_Lean_Fmt_fmtSPredTautology___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSPredTautology___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredTautology(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredTautology___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtSPredTautology"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 22, 115, 243, 124, 94, 220, 181)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtSPredBientails___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtSPredBientails___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSPredBientails___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSPredBientails___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSPredBientails___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtSPredBientails___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSPredBientails___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtSPredBientails___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSPredBientails___closed__2;
static lean_once_cell_t l_Lean_Fmt_fmtSPredBientails___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSPredBientails___closed__3;
static lean_once_cell_t l_Lean_Fmt_fmtSPredBientails___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSPredBientails___closed__4;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredBientails;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 9, .m_data = "term_⊣⊢ₛ_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSPredPure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 122, 29, 216, 46, 173, 32, 216)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtSPredBientails"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(220, 95, 129, 139, 196, 62, 26, 119)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredPure(lean_object* v_x_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = ((lean_object*)(l_Lean_Fmt_fmtSPredPure___closed__3));
lean_inc(v_x_8_);
v___x_12_ = l_Lean_Syntax_isOfKind(v_x_8_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_x_8_);
v___x_13_ = l_Lean_Fmt_Error_partialFormatter;
v___x_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_a_10_);
return v___x_14_;
}
else
{
lean_object* v___x_15_; lean_object* v_lbTk_16_; lean_object* v___x_17_; 
v___x_15_ = lean_unsigned_to_nat(0u);
v_lbTk_16_ = l_Lean_Syntax_getArg(v_x_8_, v___x_15_);
v___x_17_ = l_Lean_Fmt_fmt(v_lbTk_16_, v_a_9_, v_a_10_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v_a_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
v_a_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_17_, 2);
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = l_Lean_Syntax_getArg(v_x_8_, v___x_20_);
v___x_22_ = l_Lean_Fmt_fmt(v___x_21_, v_a_9_, v_a_19_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v_a_24_; lean_object* v___x_25_; lean_object* v_rbTk_26_; lean_object* v___x_27_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc(v_a_23_);
v_a_24_ = lean_ctor_get(v___x_22_, 1);
lean_inc(v_a_24_);
lean_dec_ref_known(v___x_22_, 2);
v___x_25_ = lean_unsigned_to_nat(2u);
v_rbTk_26_ = l_Lean_Syntax_getArg(v_x_8_, v___x_25_);
lean_dec(v_x_8_);
v___x_27_ = l_Lean_Fmt_fmt(v_rbTk_26_, v_a_9_, v_a_24_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_37_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
v_a_29_ = lean_ctor_get(v___x_27_, 1);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_37_ == 0)
{
v___x_31_ = v___x_27_;
v_isShared_32_ = v_isSharedCheck_37_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_inc(v_a_28_);
lean_dec(v___x_27_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_37_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = l_Lean_Fmt_Layouts_parens(v_a_18_, v_a_23_, v_a_28_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 0, v___x_33_);
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_a_29_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_dec(v_a_23_);
lean_dec(v_a_18_);
return v___x_27_;
}
}
else
{
lean_dec(v_a_18_);
lean_dec(v_x_8_);
return v___x_22_;
}
}
else
{
lean_dec(v_x_8_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredPure___boxed(lean_object* v_x_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Fmt_fmtSPredPure(v_x_38_, v_a_39_, v_a_40_);
lean_dec_ref(v_a_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_50_ = l_Lean_Fmt_fmtAttribute;
v___x_51_ = ((lean_object*)(l_Lean_Fmt_fmtSPredPure___closed__3));
v___x_52_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___closed__3));
v___x_53_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSPredPure___boxed), 3, 0);
v___x_54_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_50_, v___x_51_, v___x_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1___boxed(lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1();
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredTautology(lean_object* v_x_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = ((lean_object*)(l_Lean_Fmt_fmtSPredTautology___closed__1));
lean_inc(v_x_62_);
v___x_66_ = l_Lean_Syntax_isOfKind(v_x_62_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_x_62_);
v___x_67_ = l_Lean_Fmt_Error_partialFormatter;
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_a_64_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v_entailsTk_70_; lean_object* v___x_71_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v_entailsTk_70_ = l_Lean_Syntax_getArg(v_x_62_, v___x_69_);
v___x_71_ = l_Lean_Fmt_fmt(v_entailsTk_70_, v_a_63_, v_a_64_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v_a_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
v_a_73_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_71_, 2);
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = l_Lean_Syntax_getArg(v_x_62_, v___x_74_);
lean_dec(v_x_62_);
v___x_76_ = l_Lean_Fmt_fmt(v___x_75_, v_a_63_, v_a_73_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_87_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_a_78_ = lean_ctor_get(v___x_76_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_87_ == 0)
{
v___x_80_ = v___x_76_;
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_82_ = 2;
v___x_83_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_72_, v_a_77_, v___x_82_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_a_78_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
else
{
lean_dec(v_a_72_);
return v___x_76_;
}
}
else
{
lean_dec(v_x_62_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSPredTautology___boxed(lean_object* v_x_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Fmt_fmtSPredTautology(v_x_88_, v_a_89_, v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1(){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_98_ = l_Lean_Fmt_fmtAttribute;
v___x_99_ = ((lean_object*)(l_Lean_Fmt_fmtSPredTautology___closed__1));
v___x_100_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___closed__1));
v___x_101_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSPredTautology___boxed), 3, 0);
v___x_102_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_98_, v___x_99_, v___x_100_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1___boxed(lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1();
return v_res_104_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSPredBientails___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_box(0);
v___x_110_ = lean_unsigned_to_nat(16u);
v___x_111_ = lean_mk_array(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSPredBientails___closed__3(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&l_Lean_Fmt_fmtSPredBientails___closed__2, &l_Lean_Fmt_fmtSPredBientails___closed__2_once, _init_l_Lean_Fmt_fmtSPredBientails___closed__2);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSPredBientails___closed__4(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; 
v___x_115_ = lean_obj_once(&l_Lean_Fmt_fmtSPredBientails___closed__3, &l_Lean_Fmt_fmtSPredBientails___closed__3_once, _init_l_Lean_Fmt_fmtSPredBientails___closed__3);
v___x_116_ = ((lean_object*)(l_Lean_Fmt_fmtSPredBientails___closed__1));
v___x_117_ = 0;
v___x_118_ = 1;
v___x_119_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_119_, 0, v___x_116_);
lean_ctor_set(v___x_119_, 1, v___x_115_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*2, v___x_118_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*2 + 1, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSPredBientails(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_obj_once(&l_Lean_Fmt_fmtSPredBientails___closed__4, &l_Lean_Fmt_fmtSPredBientails___closed__4_once, _init_l_Lean_Fmt_fmtSPredBientails___closed__4);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1(){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = l_Lean_Fmt_infixFmtAttribute;
v___x_133_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__1));
v___x_134_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___closed__3));
v___x_135_ = l_Lean_Fmt_fmtSPredBientails;
v___x_136_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_132_, v___x_133_, v___x_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1___boxed(lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1();
return v_res_138_;
}
}
lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredPure___regBuiltin_Lean_Fmt_fmtSPredPure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredTautology___regBuiltin_Lean_Fmt_fmtSPredTautology__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtSPredBientails = _init_l_Lean_Fmt_fmtSPredBientails();
lean_mark_persistent(l_Lean_Fmt_fmtSPredBientails);
res = l___private_Lean_Fmt_Formatters_Std_Do_SPred_Notation_0__Lean_Fmt_fmtSPredBientails___regBuiltin_Lean_Fmt_fmtSPredBientails__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Do_SPred_Notation(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Do_SPred_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Do_SPred_Notation(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_SPred_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Do_SPred_Notation(builtin);
}
#ifdef __cplusplus
}
#endif
