// Lean compiler output
// Module: Lean.Elab.Tactic.Congr
// Imports: public import Lean.Meta.Tactic.Congr public import Lean.Elab.Tactic.Basic
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
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_congrN(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 88, 242, 177, 210, 111, 166, 107)}};
static const lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalCongr"};
static const lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 154, 131, 65, 24, 251, 74, 112)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 193, 35, 15, 231, 100, 96, 114)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 86, 50, 6, 68, 248, 191, 209)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(128, 230, 234, 8, 188, 21, 38, 62)}};
static const lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(38) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0_value),((lean_object*)(((size_t)(38) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3_value),((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v___y_17_ = stack[7].m_obj;
lean_object* v___y_18_ = stack[8].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___boxed(lean_object* v_00_u03b1_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0(v_00_u03b1_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
return v_res_32_;
}
}
lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0(lean_object* v___y_33_, uint8_t v___x_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_36_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_46_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_45_);
lean_dec_ref_known(v___x_44_, 1);
v___x_46_ = l_Lean_MVarId_congrN(v_a_45_, v___y_33_, v___x_34_, v___x_34_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v___x_46_, 1);
v___x_48_ = lean_box(0);
v___x_49_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_47_, v___y_36_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_56_ == 0)
{
lean_object* v_unused_57_; 
v_unused_57_ = lean_ctor_get(v___x_49_, 0);
lean_dec(v_unused_57_);
v___x_51_ = v___x_49_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_dec(v___x_49_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_48_);
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_48_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
else
{
return v___x_49_;
}
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
v_a_58_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_46_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_46_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
else
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
v_a_66_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_73_ == 0)
{
v___x_68_ = v___x_44_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_44_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_a_66_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_33_ = stack[0].m_obj;
uint8_t v___x_34_ = stack[1].m_num;
lean_object* v___y_35_ = stack[2].m_obj;
lean_object* v___y_36_ = stack[3].m_obj;
lean_object* v___y_37_ = stack[4].m_obj;
lean_object* v___y_38_ = stack[5].m_obj;
lean_object* v___y_39_ = stack[6].m_obj;
lean_object* v___y_40_ = stack[7].m_obj;
lean_object* v___y_41_ = stack[8].m_obj;
lean_object* v___y_42_ = stack[9].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0(v___y_33_, v___x_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0___boxed(lean_object* v___y_75_, lean_object* v___x_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
uint8_t v___x_593__boxed_86_; lean_object* v_res_87_; 
v___x_593__boxed_86_ = lean_unbox(v___x_76_);
v_res_87_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0(v___y_75_, v___x_593__boxed_86_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_75_);
return v_res_87_;
}
}
lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr(lean_object* v_stx_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; lean_object* v___y_115_; lean_object* v___y_116_; lean_object* v___y_117_; lean_object* v___y_118_; 
v___x_107_ = ((lean_object*)(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4));
lean_inc(v_stx_97_);
v___x_108_ = l_Lean_Syntax_isOfKind(v_stx_97_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_122_; 
lean_dec(v_stx_97_);
v___x_122_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
return v___x_122_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = l_Lean_Syntax_getArg(v_stx_97_, v___x_123_);
lean_dec(v_stx_97_);
v___x_125_ = l_Lean_Syntax_isNone(v___x_124_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; 
lean_inc(v___x_124_);
v___x_126_ = l_Lean_Syntax_matchesNull(v___x_124_, v___x_123_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_dec(v___x_124_);
v___x_127_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
return v___x_127_;
}
else
{
lean_object* v___x_128_; lean_object* v_n_x3f_129_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v_n_x3f_129_ = l_Lean_Syntax_getArg(v___x_124_, v___x_128_);
lean_dec(v___x_124_);
v___x_130_ = l_Lean_TSyntax_getNat(v_n_x3f_129_);
lean_dec(v_n_x3f_129_);
v___y_110_ = v_a_102_;
v___y_111_ = v_a_101_;
v___y_112_ = v_a_103_;
v___y_113_ = v_a_100_;
v___y_114_ = v_a_99_;
v___y_115_ = v_a_104_;
v___y_116_ = v_a_105_;
v___y_117_ = v_a_98_;
v___y_118_ = v___x_130_;
goto v___jp_109_;
}
}
else
{
lean_object* v_hugeDepth_131_; 
lean_dec(v___x_124_);
v_hugeDepth_131_ = lean_unsigned_to_nat(1000000u);
v___y_110_ = v_a_102_;
v___y_111_ = v_a_101_;
v___y_112_ = v_a_103_;
v___y_113_ = v_a_100_;
v___y_114_ = v_a_99_;
v___y_115_ = v_a_104_;
v___y_116_ = v_a_105_;
v___y_117_ = v_a_98_;
v___y_118_ = v_hugeDepth_131_;
goto v___jp_109_;
}
}
v___jp_109_:
{
lean_object* v___x_119_; lean_object* v___f_120_; lean_object* v___x_121_; 
v___x_119_ = lean_box(v___x_108_);
v___f_120_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0___boxed), 11, 2);
lean_closure_set(v___f_120_, 0, v___y_118_);
lean_closure_set(v___f_120_, 1, v___x_119_);
v___x_121_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_120_, v___y_117_, v___y_114_, v___y_113_, v___y_111_, v___y_110_, v___y_112_, v___y_115_, v___y_116_);
return v___x_121_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_97_ = stack[0].m_obj;
lean_object* v_a_98_ = stack[1].m_obj;
lean_object* v_a_99_ = stack[2].m_obj;
lean_object* v_a_100_ = stack[3].m_obj;
lean_object* v_a_101_ = stack[4].m_obj;
lean_object* v_a_102_ = stack[5].m_obj;
lean_object* v_a_103_ = stack[6].m_obj;
lean_object* v_a_104_ = stack[7].m_obj;
lean_object* v_a_105_ = stack[8].m_obj;
lean_object* v_res_132_;
v_res_132_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr(v_stx_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___boxed(lean_object* v_stx_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr(v_stx_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
return v_res_143_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1(){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_152_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_153_ = ((lean_object*)(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4));
v___x_154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2));
v___x_155_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___boxed), 10, 0);
v___x_156_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_152_, v___x_153_, v___x_154_, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_157_;
v_res_157_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1();
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___boxed(lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1();
return v_res_159_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3(){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2));
v___x_187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6));
v___x_188_ = l_Lean_addBuiltinDeclarationRanges(v___x_186_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_189_;
v_res_189_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3();
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___boxed(lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3();
return v_res_191_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Congr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Congr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Congr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Congr(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Congr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Congr(builtin);
}
#ifdef __cplusplus
}
#endif
