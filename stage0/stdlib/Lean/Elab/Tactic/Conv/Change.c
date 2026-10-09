// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Change
// Imports: public import Lean.Elab.Tactic.Change public import Lean.Elab.Tactic.Conv.Basic
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabChangeDefaultError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_elabChangeDefaultError___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalChange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalChange___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "change"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__4_value),LEAN_SCALAR_PTR_LITERAL(85, 48, 251, 99, 118, 217, 178, 16)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalChange"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 227, 251, 40, 6, 142, 99, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0_value),((lean_object*)(((size_t)(49) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0(void){
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0_0interp(lean_interpreter_value* stack)
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
v_res_21_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___boxed(lean_object* v_00_u03b1_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0(v_00_u03b1_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
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
lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lam__0(lean_object* v_e_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_36_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_46_; lean_object* v_mctx_47_; lean_object* v_mvarCounter_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_45_);
lean_dec_ref_known(v___x_44_, 1);
v___x_46_ = lean_st_ref_get(v___y_40_);
v_mctx_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc_ref(v_mctx_47_);
lean_dec(v___x_46_);
v_mvarCounter_48_ = lean_ctor_get(v_mctx_47_, 3);
lean_inc(v_mvarCounter_48_);
lean_dec_ref(v_mctx_47_);
v___x_49_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0));
v___x_50_ = l_Lean_Elab_Tactic_elabChange(v_a_45_, v_e_34_, v___x_49_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v_a_51_; lean_object* v___x_52_; 
v_a_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc_n(v_a_51_, 2);
lean_dec_ref_known(v___x_50_, 1);
v___x_52_ = l_Lean_Meta_getMVars(v_a_51_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_54_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
lean_dec_ref_known(v___x_52_, 1);
v___x_54_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_53_, v_mvarCounter_48_, v___y_40_);
lean_dec(v_mvarCounter_48_);
lean_dec(v_a_53_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_56_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_a_55_);
lean_dec_ref_known(v___x_54_, 1);
v___x_56_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_55_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v_a_55_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v___x_57_; 
lean_dec_ref_known(v___x_56_, 1);
v___x_57_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_51_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
return v___x_57_;
}
else
{
lean_dec(v_a_51_);
return v___x_56_;
}
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
lean_dec(v_a_51_);
v_a_58_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_54_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_54_);
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
lean_dec(v_a_51_);
lean_dec(v_mvarCounter_48_);
v_a_66_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_73_ == 0)
{
v___x_68_ = v___x_52_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_52_);
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
else
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
lean_dec(v_mvarCounter_48_);
v_a_74_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_81_ == 0)
{
v___x_76_ = v___x_50_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_50_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_a_74_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
lean_dec(v_e_34_);
v_a_82_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_44_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_44_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalChange___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_34_ = stack[0].m_obj;
lean_object* v___y_35_ = stack[1].m_obj;
lean_object* v___y_36_ = stack[2].m_obj;
lean_object* v___y_37_ = stack[3].m_obj;
lean_object* v___y_38_ = stack[4].m_obj;
lean_object* v___y_39_ = stack[5].m_obj;
lean_object* v___y_40_ = stack[6].m_obj;
lean_object* v___y_41_ = stack[7].m_obj;
lean_object* v___y_42_ = stack[8].m_obj;
lean_object* v_res_90_;
v_res_90_ = l_Lean_Elab_Tactic_Conv_evalChange___lam__0(v_e_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lam__0___boxed(lean_object* v_e_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Elab_Tactic_Conv_evalChange___lam__0(v_e_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_101_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalChange(lean_object* v_stx_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalChange___closed__5));
lean_inc(v_stx_113_);
v___x_124_ = l_Lean_Syntax_isOfKind(v_stx_113_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
lean_dec(v_stx_113_);
v___x_125_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v_e_127_; lean_object* v___f_128_; lean_object* v___x_129_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v_e_127_ = l_Lean_Syntax_getArg(v_stx_113_, v___x_126_);
lean_dec(v_stx_113_);
v___f_128_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalChange___lam__0___boxed), 10, 1);
lean_closure_set(v___f_128_, 0, v_e_127_);
v___x_129_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_128_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
return v___x_129_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_113_ = stack[0].m_obj;
lean_object* v_a_114_ = stack[1].m_obj;
lean_object* v_a_115_ = stack[2].m_obj;
lean_object* v_a_116_ = stack[3].m_obj;
lean_object* v_a_117_ = stack[4].m_obj;
lean_object* v_a_118_ = stack[5].m_obj;
lean_object* v_a_119_ = stack[6].m_obj;
lean_object* v_a_120_ = stack[7].m_obj;
lean_object* v_a_121_ = stack[8].m_obj;
lean_object* v_res_130_;
v_res_130_ = l_Lean_Elab_Tactic_Conv_evalChange(v_stx_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___boxed(lean_object* v_stx_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Elab_Tactic_Conv_evalChange(v_stx_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
return v_res_141_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1(){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_151_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_152_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalChange___closed__5));
v___x_153_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2));
v___x_154_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalChange___boxed), 10, 0);
v___x_155_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_151_, v___x_152_, v___x_153_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_156_;
v_res_156_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1();
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___boxed(lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1();
return v_res_158_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3(){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2));
v___x_186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6));
v___x_187_ = l_Lean_addBuiltinDeclarationRanges(v___x_185_, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_188_;
v_res_188_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3();
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___boxed(lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3();
return v_res_190_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Change(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Change(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Change(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Change(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Change(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Change(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Change(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Change(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Change(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Change(builtin);
}
#ifdef __cplusplus
}
#endif
