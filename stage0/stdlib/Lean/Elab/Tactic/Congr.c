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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0(lean_object* v___y_31_, uint8_t v___x_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_34_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v___x_44_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
lean_dec_ref(v___x_42_);
v___x_44_ = l_Lean_MVarId_congrN(v_a_43_, v___y_31_, v___x_32_, v___x_32_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_46_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_45_);
lean_dec_ref(v___x_44_);
v___x_46_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_45_, v___y_34_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_54_; 
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_54_ == 0)
{
lean_object* v_unused_55_; 
v_unused_55_ = lean_ctor_get(v___x_46_, 0);
lean_dec(v_unused_55_);
v___x_48_ = v___x_46_;
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
else
{
lean_dec(v___x_46_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_50_ = lean_box(0);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
else
{
return v___x_46_;
}
}
else
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
v_a_56_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_44_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_44_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
else
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
v_a_64_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___x_42_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_42_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0___boxed(lean_object* v___y_72_, lean_object* v___x_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
uint8_t v___x_876__boxed_83_; lean_object* v_res_84_; 
v___x_876__boxed_83_ = lean_unbox(v___x_73_);
v_res_84_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0(v___y_72_, v___x_876__boxed_83_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_72_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr(lean_object* v_stx_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_104_; uint8_t v___x_105_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; lean_object* v___y_115_; 
v___x_104_ = ((lean_object*)(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4));
lean_inc(v_stx_94_);
v___x_105_ = l_Lean_Syntax_isOfKind(v_stx_94_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_119_; 
lean_dec(v_stx_94_);
v___x_119_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = l_Lean_Syntax_getArg(v_stx_94_, v___x_120_);
lean_dec(v_stx_94_);
v___x_122_ = l_Lean_Syntax_isNone(v___x_121_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
lean_inc(v___x_121_);
v___x_123_ = l_Lean_Syntax_matchesNull(v___x_121_, v___x_120_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
lean_dec(v___x_121_);
v___x_124_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
return v___x_124_;
}
else
{
lean_object* v___x_125_; lean_object* v_n_x3f_126_; lean_object* v___x_127_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v_n_x3f_126_ = l_Lean_Syntax_getArg(v___x_121_, v___x_125_);
lean_dec(v___x_121_);
v___x_127_ = l_Lean_TSyntax_getNat(v_n_x3f_126_);
lean_dec(v_n_x3f_126_);
v___y_107_ = v_a_96_;
v___y_108_ = v_a_101_;
v___y_109_ = v_a_100_;
v___y_110_ = v_a_99_;
v___y_111_ = v_a_102_;
v___y_112_ = v_a_97_;
v___y_113_ = v_a_95_;
v___y_114_ = v_a_98_;
v___y_115_ = v___x_127_;
goto v___jp_106_;
}
}
else
{
lean_object* v_hugeDepth_128_; 
lean_dec(v___x_121_);
v_hugeDepth_128_ = lean_unsigned_to_nat(1000000u);
v___y_107_ = v_a_96_;
v___y_108_ = v_a_101_;
v___y_109_ = v_a_100_;
v___y_110_ = v_a_99_;
v___y_111_ = v_a_102_;
v___y_112_ = v_a_97_;
v___y_113_ = v_a_95_;
v___y_114_ = v_a_98_;
v___y_115_ = v_hugeDepth_128_;
goto v___jp_106_;
}
}
v___jp_106_:
{
lean_object* v___x_116_; lean_object* v___f_117_; lean_object* v___x_118_; 
v___x_116_ = lean_box(v___x_105_);
v___f_117_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0___boxed), 11, 2);
lean_closure_set(v___f_117_, 0, v___y_115_);
lean_closure_set(v___f_117_, 1, v___x_116_);
v___x_118_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_117_, v___y_113_, v___y_107_, v___y_112_, v___y_114_, v___y_110_, v___y_109_, v___y_108_, v___y_111_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___boxed(lean_object* v_stx_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr(v_stx_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1(){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_148_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_149_ = ((lean_object*)(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4));
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2));
v___x_151_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___boxed), 10, 0);
v___x_152_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_148_, v___x_149_, v___x_150_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___boxed(lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1();
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2));
v___x_182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6));
v___x_183_ = l_Lean_addBuiltinDeclarationRanges(v___x_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___boxed(lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3();
return v_res_185_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Congr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Congr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
