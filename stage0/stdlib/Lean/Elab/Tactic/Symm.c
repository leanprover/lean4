// Lean compiler output
// Module: Lean.Elab.Tactic.Symm
// Imports: public import Lean.Meta.Tactic.Symm public import Lean.Elab.Tactic.Location
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_symmSaturate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applySymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applySymmAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSymm___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "`symm` made no progress"};
static const lean_object* l_Lean_Elab_Tactic_evalSymm___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSymm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalSymm___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSymm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalSymm___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSymm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalSymm___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalSymm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l_Lean_Elab_Tactic_evalSymm___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSymm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 245, 98, 203, 35, 2, 43, 106)}};
static const lean_object* l_Lean_Elab_Tactic_evalSymm___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalSymm___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalSymm___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalSymm___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalSymm___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalSymm___lam__1___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__5_value)} };
static const lean_object* l_Lean_Elab_Tactic_evalSymm___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__6_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalSymm___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalSymm___lam__2___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalSymm___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__7_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalSymm___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalSymm___lam__4___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalSymm___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__8_value;
static const lean_array_object l_Lean_Elab_Tactic_evalSymm___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_evalSymm___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalSymm"};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 3, 217, 210, 255, 45, 48, 213)}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__4_value),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymmSaturate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymmSaturate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSymmSaturate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "symmSaturate"};
static const lean_object* l_Lean_Elab_Tactic_evalSymmSaturate___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymmSaturate___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSymmSaturate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 186, 236, 63, 7, 254, 154, 190)}};
static const lean_object* l_Lean_Elab_Tactic_evalSymmSaturate___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymmSaturate___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalSymmSaturate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalSymmSaturate___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalSymmSaturate___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalSymmSaturate___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymmSaturate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymmSaturate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalSymmSaturate"};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalSymm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 38, 32, 117, 193, 67, 14, 170)}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__4_value),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0(void){
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg();
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1_0interp(lean_interpreter_value* stack)
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
v_res_21_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___boxed(lean_object* v_00_u03b1_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1(v_00_u03b1_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
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
lean_object* l_Lean_Elab_Tactic_evalSymm___lam__0(lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_34_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v___x_44_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_42_, 1);
v___x_44_ = l_Lean_MVarId_applySymm(v_a_43_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_45_);
lean_dec_ref_known(v___x_44_, 1);
v___x_46_ = lean_box(0);
v___x_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_47_, 0, v_a_45_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_47_, v___y_34_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
return v___x_48_;
}
else
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
v_a_49_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v___x_44_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_44_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
else
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_64_; 
v_a_57_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_64_ == 0)
{
v___x_59_ = v___x_42_;
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_42_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_a_57_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSymm___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_33_ = stack[0].m_obj;
lean_object* v___y_34_ = stack[1].m_obj;
lean_object* v___y_35_ = stack[2].m_obj;
lean_object* v___y_36_ = stack[3].m_obj;
lean_object* v___y_37_ = stack[4].m_obj;
lean_object* v___y_38_ = stack[5].m_obj;
lean_object* v___y_39_ = stack[6].m_obj;
lean_object* v___y_40_ = stack[7].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_Elab_Tactic_evalSymm___lam__0(v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__0___boxed(lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Elab_Tactic_evalSymm___lam__0(v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
return v_res_75_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSymm___lam__1(lean_object* v___f_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
return v___x_86_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSymm___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_76_ = stack[0].m_obj;
lean_object* v___y_77_ = stack[1].m_obj;
lean_object* v___y_78_ = stack[2].m_obj;
lean_object* v___y_79_ = stack[3].m_obj;
lean_object* v___y_80_ = stack[4].m_obj;
lean_object* v___y_81_ = stack[5].m_obj;
lean_object* v___y_82_ = stack[6].m_obj;
lean_object* v___y_83_ = stack[7].m_obj;
lean_object* v___y_84_ = stack[8].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_Elab_Tactic_evalSymm___lam__1(v___f_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__1___boxed(lean_object* v___f_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Elab_Tactic_evalSymm___lam__1(v___f_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
return v_res_98_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0(lean_object* v_msgData_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; lean_object* v_env_106_; uint8_t v___x_107_; lean_object* v_env_108_; lean_object* v___x_109_; lean_object* v_toCold_110_; lean_object* v_mctx_111_; lean_object* v_lctx_112_; lean_object* v_options_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_105_ = lean_st_ref_get(v___y_103_);
v_env_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_env_106_);
lean_dec(v___x_105_);
v___x_107_ = 0;
v_env_108_ = l_Lean_Environment_setRecordingDeps(v_env_106_, v___x_107_);
v___x_109_ = lean_st_ref_get(v___y_101_);
v_toCold_110_ = lean_ctor_get(v___y_102_, 0);
v_mctx_111_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_mctx_111_);
lean_dec(v___x_109_);
v_lctx_112_ = lean_ctor_get(v___y_100_, 2);
v_options_113_ = lean_ctor_get(v_toCold_110_, 2);
lean_inc_ref(v_options_113_);
lean_inc_ref(v_lctx_112_);
v___x_114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_114_, 0, v_env_108_);
lean_ctor_set(v___x_114_, 1, v_mctx_111_);
lean_ctor_set(v___x_114_, 2, v_lctx_112_);
lean_ctor_set(v___x_114_, 3, v_options_113_);
v___x_115_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_msgData_99_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_99_ = stack[0].m_obj;
lean_object* v___y_100_ = stack[1].m_obj;
lean_object* v___y_101_ = stack[2].m_obj;
lean_object* v___y_102_ = stack[3].m_obj;
lean_object* v___y_103_ = stack[4].m_obj;
lean_object* v_res_117_;
v_res_117_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0(v_msgData_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0___boxed(lean_object* v_msgData_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0(v_msgData_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_124_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg(lean_object* v_msg_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_ref_131_; lean_object* v___x_132_; lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_141_; 
v_ref_131_ = lean_ctor_get(v___y_128_, 2);
v___x_132_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_spec__0(v_msg_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_141_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
lean_inc(v_ref_131_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_ref_131_);
lean_ctor_set(v___x_137_, 1, v_a_133_);
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 1);
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_125_ = stack[0].m_obj;
lean_object* v___y_126_ = stack[1].m_obj;
lean_object* v___y_127_ = stack[2].m_obj;
lean_object* v___y_128_ = stack[3].m_obj;
lean_object* v___y_129_ = stack[4].m_obj;
lean_object* v_res_142_;
v_res_142_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg(v_msg_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg___boxed(lean_object* v_msg_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg(v_msg_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
return v_res_149_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSymm___lam__2___closed__0));
v___x_152_ = l_Lean_stringToMessageData(v___x_151_);
return v___x_152_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSymm___lam__2(lean_object* v_x_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1, &l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_evalSymm___lam__2___closed__1);
v___x_164_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg(v___x_163_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
return v___x_164_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSymm___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_153_ = stack[0].m_obj;
lean_object* v___y_154_ = stack[1].m_obj;
lean_object* v___y_155_ = stack[2].m_obj;
lean_object* v___y_156_ = stack[3].m_obj;
lean_object* v___y_157_ = stack[4].m_obj;
lean_object* v___y_158_ = stack[5].m_obj;
lean_object* v___y_159_ = stack[6].m_obj;
lean_object* v___y_160_ = stack[7].m_obj;
lean_object* v___y_161_ = stack[8].m_obj;
lean_object* v_res_165_;
v_res_165_ = l_Lean_Elab_Tactic_evalSymm___lam__2(v_x_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__2___boxed(lean_object* v_x_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Elab_Tactic_evalSymm___lam__2(v_x_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v_x_166_);
return v_res_176_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSymm___lam__3(lean_object* v_h_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_179_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_187_, 1);
v___x_189_ = l_Lean_MVarId_applySymmAt(v_h_177_, v_a_188_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_189_, 1);
v___x_191_ = lean_box(0);
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v_a_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_192_, v___y_179_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_193_;
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
v_a_194_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_189_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_189_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_h_177_);
v_a_202_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_187_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_187_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSymm___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_177_ = stack[0].m_obj;
lean_object* v___y_178_ = stack[1].m_obj;
lean_object* v___y_179_ = stack[2].m_obj;
lean_object* v___y_180_ = stack[3].m_obj;
lean_object* v___y_181_ = stack[4].m_obj;
lean_object* v___y_182_ = stack[5].m_obj;
lean_object* v___y_183_ = stack[6].m_obj;
lean_object* v___y_184_ = stack[7].m_obj;
lean_object* v___y_185_ = stack[8].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_Elab_Tactic_evalSymm___lam__3(v_h_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__3___boxed(lean_object* v_h_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_Tactic_evalSymm___lam__3(v_h_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_221_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSymm___lam__4(lean_object* v_h_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v___f_232_; lean_object* v___x_233_; 
v___f_232_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSymm___lam__3___boxed), 10, 1);
lean_closure_set(v___f_232_, 0, v_h_222_);
v___x_233_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_232_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
return v___x_233_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSymm___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_222_ = stack[0].m_obj;
lean_object* v___y_223_ = stack[1].m_obj;
lean_object* v___y_224_ = stack[2].m_obj;
lean_object* v___y_225_ = stack[3].m_obj;
lean_object* v___y_226_ = stack[4].m_obj;
lean_object* v___y_227_ = stack[5].m_obj;
lean_object* v___y_228_ = stack[6].m_obj;
lean_object* v___y_229_ = stack[7].m_obj;
lean_object* v___y_230_ = stack[8].m_obj;
lean_object* v_res_234_;
v_res_234_ = l_Lean_Elab_Tactic_evalSymm___lam__4(v_h_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___lam__4___boxed(lean_object* v_h_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Elab_Tactic_evalSymm___lam__4(v_h_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_245_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSymm(lean_object* v_stx_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSymm___closed__4));
lean_inc(v_stx_262_);
v___x_273_ = l_Lean_Syntax_isOfKind(v_stx_262_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec(v_stx_262_);
v___x_274_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg();
return v___x_274_;
}
else
{
lean_object* v_atTarget_275_; lean_object* v___f_276_; lean_object* v_atHyp_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_atTarget_275_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSymm___closed__6));
v___f_276_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSymm___closed__7));
v_atHyp_277_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSymm___closed__8));
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = l_Lean_Syntax_getArg(v_stx_262_, v___x_278_);
lean_dec(v_stx_262_);
v___x_280_ = l_Lean_Syntax_getOptional_x3f(v___x_279_);
lean_dec(v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSymm___closed__9));
v___x_282_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*1, v___x_273_);
v___x_283_ = l_Lean_Elab_Tactic_withLocation(v___x_282_, v_atHyp_277_, v_atTarget_275_, v___f_276_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
lean_dec_ref_known(v___x_282_, 1);
return v___x_283_;
}
else
{
lean_object* v_val_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_val_284_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_284_);
lean_dec_ref_known(v___x_280_, 1);
v___x_285_ = l_Lean_Elab_Tactic_expandLocation(v_val_284_);
lean_dec(v_val_284_);
v___x_286_ = l_Lean_Elab_Tactic_withLocation(v___x_285_, v_atHyp_277_, v_atTarget_275_, v___f_276_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
lean_dec(v___x_285_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSymm_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_262_ = stack[0].m_obj;
lean_object* v_a_263_ = stack[1].m_obj;
lean_object* v_a_264_ = stack[2].m_obj;
lean_object* v_a_265_ = stack[3].m_obj;
lean_object* v_a_266_ = stack[4].m_obj;
lean_object* v_a_267_ = stack[5].m_obj;
lean_object* v_a_268_ = stack[6].m_obj;
lean_object* v_a_269_ = stack[7].m_obj;
lean_object* v_a_270_ = stack[8].m_obj;
lean_object* v_res_287_;
v_res_287_ = l_Lean_Elab_Tactic_evalSymm(v_stx_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymm___boxed(lean_object* v_stx_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Elab_Tactic_evalSymm(v_stx_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_298_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0(lean_object* v_00_u03b1_299_, lean_object* v_msg_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___redArg(v_msg_300_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
return v___x_310_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_300_ = stack[1].m_obj;
lean_object* v___y_301_ = stack[2].m_obj;
lean_object* v___y_302_ = stack[3].m_obj;
lean_object* v___y_303_ = stack[4].m_obj;
lean_object* v___y_304_ = stack[5].m_obj;
lean_object* v___y_305_ = stack[6].m_obj;
lean_object* v___y_306_ = stack[7].m_obj;
lean_object* v___y_307_ = stack[8].m_obj;
lean_object* v___y_308_ = stack[9].m_obj;
lean_object* v_res_311_;
v_res_311_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0(lean_box(0), v_msg_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0___boxed(lean_object* v_00_u03b1_312_, lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSymm_spec__0(v_00_u03b1_312_, v_msg_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_323_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1(){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_332_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_333_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSymm___closed__4));
v___x_334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2));
v___x_335_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSymm___boxed), 10, 0);
v___x_336_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_332_, v___x_333_, v___x_334_, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_337_;
v_res_337_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1();
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___boxed(lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1();
return v_res_339_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3(){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1___closed__2));
v___x_367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___closed__6));
v___x_368_ = l_Lean_addBuiltinDeclarationRanges(v___x_366_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_369_;
v_res_369_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3();
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3___boxed(lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3();
return v_res_371_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSymmSaturate___lam__0(lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_373_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_383_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_381_, 1);
v___x_383_ = l_Lean_MVarId_symmSaturate(v_a_382_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v___x_385_ = lean_box(0);
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v_a_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_386_, v___y_373_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
return v___x_387_;
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v_a_388_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_383_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_383_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_a_396_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_381_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_381_);
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
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSymmSaturate___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_372_ = stack[0].m_obj;
lean_object* v___y_373_ = stack[1].m_obj;
lean_object* v___y_374_ = stack[2].m_obj;
lean_object* v___y_375_ = stack[3].m_obj;
lean_object* v___y_376_ = stack[4].m_obj;
lean_object* v___y_377_ = stack[5].m_obj;
lean_object* v___y_378_ = stack[6].m_obj;
lean_object* v___y_379_ = stack[7].m_obj;
lean_object* v_res_404_;
v_res_404_ = l_Lean_Elab_Tactic_evalSymmSaturate___lam__0(v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
stack->m_obj
 = v_res_404_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymmSaturate___lam__0___boxed(lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Elab_Tactic_evalSymmSaturate___lam__0(v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_414_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSymmSaturate(lean_object* v_stx_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSymmSaturate___closed__1));
v___x_433_ = l_Lean_Syntax_isOfKind(v_stx_422_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalSymm_spec__1___redArg();
return v___x_434_;
}
else
{
lean_object* v___f_435_; lean_object* v___x_436_; 
v___f_435_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSymmSaturate___closed__2));
v___x_436_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_435_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
return v___x_436_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSymmSaturate_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_422_ = stack[0].m_obj;
lean_object* v_a_423_ = stack[1].m_obj;
lean_object* v_a_424_ = stack[2].m_obj;
lean_object* v_a_425_ = stack[3].m_obj;
lean_object* v_a_426_ = stack[4].m_obj;
lean_object* v_a_427_ = stack[5].m_obj;
lean_object* v_a_428_ = stack[6].m_obj;
lean_object* v_a_429_ = stack[7].m_obj;
lean_object* v_a_430_ = stack[8].m_obj;
lean_object* v_res_437_;
v_res_437_ = l_Lean_Elab_Tactic_evalSymmSaturate(v_stx_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSymmSaturate___boxed(lean_object* v_stx_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Elab_Tactic_evalSymmSaturate(v_stx_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
return v_res_448_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1(){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_456_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_457_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSymmSaturate___closed__1));
v___x_458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1));
v___x_459_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSymmSaturate___boxed), 10, 0);
v___x_460_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_456_, v___x_457_, v___x_458_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_461_;
v_res_461_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1();
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___boxed(lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1();
return v_res_463_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3(){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1___closed__1));
v___x_491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___closed__6));
v___x_492_ = l_Lean_addBuiltinDeclarationRanges(v___x_490_, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_493_;
v_res_493_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3();
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3___boxed(lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3();
return v_res_495_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Symm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Symm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymm___regBuiltin_Lean_Elab_Tactic_evalSymm_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Symm_0__Lean_Elab_Tactic_evalSymmSaturate___regBuiltin_Lean_Elab_Tactic_evalSymmSaturate_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Symm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Symm(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Symm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Symm(builtin);
}
#ifdef __cplusplus
}
#endif
