// Lean compiler output
// Module: Lean.Elab.Tactic.FalseOrByContra
// Imports: public import Lean.Elab.Tactic.Basic public import Lean.Meta.Tactic.Apply public import Lean.Meta.Tactic.Intro
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
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__0 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__0_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__1 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__1_value;
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__2_value_aux_0),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 114, 54, 50, 40, 156, 62, 47)}};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__2 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__3 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__3_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Elab.Tactic.FalseOrByContra"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__4 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__4_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.MVarId.falseOrByContra"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__5 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__5_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected at most one sugoal"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__6 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__6_value;
static lean_once_cell_t l_Lean_MVarId_falseOrByContra___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_falseOrByContra___closed__7;
static lean_once_cell_t l_Lean_MVarId_falseOrByContra___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_falseOrByContra___closed__8;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__9 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__9_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__10 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__10_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "byContradiction"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__11 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__11_value;
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__10_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__12_value_aux_0),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__11_value),LEAN_SCALAR_PTR_LITERAL(92, 114, 13, 107, 214, 89, 53, 175)}};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__12 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__12_value;
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__9_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__13_value_aux_0),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__11_value),LEAN_SCALAR_PTR_LITERAL(143, 54, 188, 55, 95, 58, 91, 50)}};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__13 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__13_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__14 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__0 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__0_value;
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__1 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__1_value;
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__2 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__2_value;
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "falseOrByContra"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__3 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__3_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_0),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_1),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_2),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 186, 236, 85, 98, 241, 184, 126)}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__4 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value;
static const lean_closure_object l_Lean_MVarId_elabFalseOrByContra___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__5 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "MVarId"};
static const lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabFalseOrByContra"};
static const lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 186, 234, 138, 172, 166, 87, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(16, 121, 168, 236, 1, 165, 84, 207)}};
static const lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(62) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(62) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(62) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_5638__overap_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0));
v___x_5638__overap_9_ = lean_panic_fn_borrowed(v___f_8_, v_msg_2_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_10_ = lean_apply_5(v___x_5638__overap_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___boxed(lean_object* v_msg_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v_msg_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_17_;
}
}
static lean_object* _init_l_Lean_MVarId_falseOrByContra___closed__7(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_30_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__6));
v___x_31_ = lean_unsigned_to_nat(13u);
v___x_32_ = lean_unsigned_to_nat(66u);
v___x_33_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__5));
v___x_34_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__4));
v___x_35_ = l_mkPanicMessageWithDecl(v___x_34_, v___x_33_, v___x_32_, v___x_31_, v___x_30_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_MVarId_falseOrByContra___closed__8(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_36_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__6));
v___x_37_ = lean_unsigned_to_nat(16u);
v___x_38_ = lean_unsigned_to_nat(61u);
v___x_39_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__5));
v___x_40_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__4));
v___x_41_ = l_mkPanicMessageWithDecl(v___x_40_, v___x_39_, v___x_38_, v___x_37_, v___x_36_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra(lean_object* v_g_52_, lean_object* v_useClassical_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___y_63_; lean_object* v___y_64_; lean_object* v___y_65_; lean_object* v___y_66_; lean_object* v___y_92_; lean_object* v___y_93_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; uint8_t v___y_97_; lean_object* v_val_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v___y_132_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___y_136_; uint8_t v___y_137_; lean_object* v___x_151_; 
lean_inc(v_g_52_);
v___x_151_ = l_Lean_MVarId_getType(v_g_52_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_153_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v___x_153_ = l_Lean_Meta_whnfR(v_a_152_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_283_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_283_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_283_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_283_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; 
switch(lean_obj_tag(v_a_154_))
{
case 4:
{
lean_object* v_declName_215_; 
v_declName_215_ = lean_ctor_get(v_a_154_, 0);
if (lean_obj_tag(v_declName_215_) == 1)
{
lean_object* v_pre_216_; 
v_pre_216_ = lean_ctor_get(v_declName_215_, 0);
if (lean_obj_tag(v_pre_216_) == 0)
{
lean_object* v_str_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_str_217_ = lean_ctor_get(v_declName_215_, 1);
v___x_218_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__0));
v___x_219_ = lean_string_dec_eq(v_str_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_del_object(v___x_156_);
v___y_159_ = v_a_54_;
v___y_160_ = v_a_55_;
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
goto v___jp_158_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_222_; 
lean_dec_ref_known(v_a_154_, 2);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v_g_52_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_220_);
v___x_222_ = v___x_156_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
else
{
lean_del_object(v___x_156_);
v___y_159_ = v_a_54_;
v___y_160_ = v_a_55_;
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
goto v___jp_158_;
}
}
else
{
lean_del_object(v___x_156_);
v___y_159_ = v_a_54_;
v___y_160_ = v_a_55_;
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
goto v___jp_158_;
}
}
case 7:
{
lean_object* v_keyedConfig_224_; uint8_t v_trackZetaDelta_225_; lean_object* v_zetaDeltaSet_226_; lean_object* v_lctx_227_; lean_object* v_localInstances_228_; lean_object* v_defEqCtx_x3f_229_; lean_object* v_synthPendingDepth_230_; lean_object* v_customCanUnfoldPredicate_x3f_231_; uint8_t v_univApprox_232_; uint8_t v_inTypeClassResolution_233_; uint8_t v_cacheInferType_234_; uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; 
lean_dec_ref_known(v_a_154_, 3);
lean_del_object(v___x_156_);
v_keyedConfig_224_ = lean_ctor_get(v_a_54_, 0);
v_trackZetaDelta_225_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7);
v_zetaDeltaSet_226_ = lean_ctor_get(v_a_54_, 1);
v_lctx_227_ = lean_ctor_get(v_a_54_, 2);
v_localInstances_228_ = lean_ctor_get(v_a_54_, 3);
v_defEqCtx_x3f_229_ = lean_ctor_get(v_a_54_, 4);
v_synthPendingDepth_230_ = lean_ctor_get(v_a_54_, 5);
v_customCanUnfoldPredicate_x3f_231_ = lean_ctor_get(v_a_54_, 6);
v_univApprox_232_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_233_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 2);
v_cacheInferType_234_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 3);
v___x_235_ = 0;
lean_inc_ref(v_keyedConfig_224_);
v___x_236_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_235_, v_keyedConfig_224_);
lean_inc(v_customCanUnfoldPredicate_x3f_231_);
lean_inc(v_synthPendingDepth_230_);
lean_inc(v_defEqCtx_x3f_229_);
lean_inc_ref(v_localInstances_228_);
lean_inc_ref(v_lctx_227_);
lean_inc(v_zetaDeltaSet_226_);
v___x_237_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v_zetaDeltaSet_226_);
lean_ctor_set(v___x_237_, 2, v_lctx_227_);
lean_ctor_set(v___x_237_, 3, v_localInstances_228_);
lean_ctor_set(v___x_237_, 4, v_defEqCtx_x3f_229_);
lean_ctor_set(v___x_237_, 5, v_synthPendingDepth_230_);
lean_ctor_set(v___x_237_, 6, v_customCanUnfoldPredicate_x3f_231_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*7, v_trackZetaDelta_225_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*7 + 1, v_univApprox_232_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*7 + 2, v_inTypeClassResolution_233_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*7 + 3, v_cacheInferType_234_);
v___x_238_ = 1;
v___x_239_ = l_Lean_Meta_intro1Core(v_g_52_, v___x_238_, v___x_237_, v_a_55_, v_a_56_, v_a_57_);
lean_dec_ref_known(v___x_237_, 7);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v_snd_241_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v___x_239_, 1);
v_snd_241_ = lean_ctor_get(v_a_240_, 1);
lean_inc(v_snd_241_);
lean_dec(v_a_240_);
v_g_52_ = v_snd_241_;
goto _start;
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
v_a_243_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_239_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_239_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
case 5:
{
lean_object* v_fn_251_; 
lean_del_object(v___x_156_);
v_fn_251_ = lean_ctor_get(v_a_154_, 0);
if (lean_obj_tag(v_fn_251_) == 4)
{
lean_object* v_declName_252_; 
v_declName_252_ = lean_ctor_get(v_fn_251_, 0);
if (lean_obj_tag(v_declName_252_) == 1)
{
lean_object* v_pre_253_; 
v_pre_253_ = lean_ctor_get(v_declName_252_, 0);
if (lean_obj_tag(v_pre_253_) == 0)
{
lean_object* v_str_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_str_254_ = lean_ctor_get(v_declName_252_, 1);
v___x_255_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__14));
v___x_256_ = lean_string_dec_eq(v_str_254_, v___x_255_);
if (v___x_256_ == 0)
{
v___y_159_ = v_a_54_;
v___y_160_ = v_a_55_;
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
goto v___jp_158_;
}
else
{
lean_object* v_keyedConfig_257_; uint8_t v_trackZetaDelta_258_; lean_object* v_zetaDeltaSet_259_; lean_object* v_lctx_260_; lean_object* v_localInstances_261_; lean_object* v_defEqCtx_x3f_262_; lean_object* v_synthPendingDepth_263_; lean_object* v_customCanUnfoldPredicate_x3f_264_; uint8_t v_univApprox_265_; uint8_t v_inTypeClassResolution_266_; uint8_t v_cacheInferType_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref_known(v_a_154_, 2);
v_keyedConfig_257_ = lean_ctor_get(v_a_54_, 0);
v_trackZetaDelta_258_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7);
v_zetaDeltaSet_259_ = lean_ctor_get(v_a_54_, 1);
v_lctx_260_ = lean_ctor_get(v_a_54_, 2);
v_localInstances_261_ = lean_ctor_get(v_a_54_, 3);
v_defEqCtx_x3f_262_ = lean_ctor_get(v_a_54_, 4);
v_synthPendingDepth_263_ = lean_ctor_get(v_a_54_, 5);
v_customCanUnfoldPredicate_x3f_264_ = lean_ctor_get(v_a_54_, 6);
v_univApprox_265_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_266_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 2);
v_cacheInferType_267_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 3);
v___x_268_ = 0;
lean_inc_ref(v_keyedConfig_257_);
v___x_269_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_268_, v_keyedConfig_257_);
lean_inc(v_customCanUnfoldPredicate_x3f_264_);
lean_inc(v_synthPendingDepth_263_);
lean_inc(v_defEqCtx_x3f_262_);
lean_inc_ref(v_localInstances_261_);
lean_inc_ref(v_lctx_260_);
lean_inc(v_zetaDeltaSet_259_);
v___x_270_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_zetaDeltaSet_259_);
lean_ctor_set(v___x_270_, 2, v_lctx_260_);
lean_ctor_set(v___x_270_, 3, v_localInstances_261_);
lean_ctor_set(v___x_270_, 4, v_defEqCtx_x3f_262_);
lean_ctor_set(v___x_270_, 5, v_synthPendingDepth_263_);
lean_ctor_set(v___x_270_, 6, v_customCanUnfoldPredicate_x3f_264_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*7, v_trackZetaDelta_258_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*7 + 1, v_univApprox_265_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*7 + 2, v_inTypeClassResolution_266_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*7 + 3, v_cacheInferType_267_);
v___x_271_ = l_Lean_Meta_intro1Core(v_g_52_, v___x_256_, v___x_270_, v_a_55_, v_a_56_, v_a_57_);
lean_dec_ref_known(v___x_270_, 7);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_snd_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v_snd_273_ = lean_ctor_get(v_a_272_, 1);
lean_inc(v_snd_273_);
lean_dec(v_a_272_);
v_g_52_ = v_snd_273_;
goto _start;
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_271_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_271_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
else
{
v___y_159_ = v_a_54_;
v___y_160_ = v_a_55_;
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
goto v___jp_158_;
}
}
else
{
v___y_159_ = v_a_54_;
v___y_160_ = v_a_55_;
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
goto v___jp_158_;
}
}
else
{
v___y_159_ = v_a_54_;
v___y_160_ = v_a_55_;
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
goto v___jp_158_;
}
}
default: 
{
lean_del_object(v___x_156_);
v___y_159_ = v_a_54_;
v___y_160_ = v_a_55_;
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
goto v___jp_158_;
}
}
v___jp_158_:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Meta_isProp(v_a_154_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; uint8_t v___x_165_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v___x_163_, 1);
v___x_165_ = lean_unbox(v_a_164_);
if (v___x_165_ == 0)
{
lean_dec(v_a_164_);
v___y_63_ = v___y_159_;
v___y_64_ = v___y_160_;
v___y_65_ = v___y_161_;
v___y_66_ = v___y_162_;
goto v___jp_62_;
}
else
{
if (lean_obj_tag(v_useClassical_53_) == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; 
v___x_166_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__11));
v___x_167_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
v___x_168_ = 0;
v___x_169_ = 0;
v___x_170_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_170_, 0, v___x_168_);
v___x_171_ = lean_unbox(v_a_164_);
lean_ctor_set_uint8(v___x_170_, 1, v___x_171_);
lean_ctor_set_uint8(v___x_170_, 2, v___x_169_);
v___x_172_ = lean_unbox(v_a_164_);
lean_dec(v_a_164_);
lean_ctor_set_uint8(v___x_170_, 3, v___x_172_);
lean_inc_ref(v___x_170_);
lean_inc(v_g_52_);
v___x_173_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_167_, v___x_170_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; 
lean_dec_ref_known(v___x_170_, 0);
lean_dec(v_g_52_);
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_173_, 1);
v_val_100_ = v_a_174_;
v___y_101_ = v___y_159_;
v___y_102_ = v___y_160_;
v___y_103_ = v___y_161_;
v___y_104_ = v___y_162_;
goto v___jp_99_;
}
else
{
lean_object* v_a_175_; uint8_t v___x_176_; 
v_a_175_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_173_, 1);
v___x_176_ = l_Lean_Exception_isInterrupt(v_a_175_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; 
lean_inc(v_a_175_);
v___x_177_ = l_Lean_Exception_isRuntime(v_a_175_);
v___y_130_ = v___y_160_;
v___y_131_ = v___x_170_;
v___y_132_ = v_a_175_;
v___y_133_ = v___y_159_;
v___y_134_ = v___y_161_;
v___y_135_ = v___y_162_;
v___y_136_ = v___x_166_;
v___y_137_ = v___x_177_;
goto v___jp_129_;
}
else
{
v___y_130_ = v___y_160_;
v___y_131_ = v___x_170_;
v___y_132_ = v_a_175_;
v___y_133_ = v___y_159_;
v___y_134_ = v___y_161_;
v___y_135_ = v___y_162_;
v___y_136_ = v___x_166_;
v___y_137_ = v___x_176_;
goto v___jp_129_;
}
}
}
else
{
lean_object* v_val_178_; uint8_t v___x_179_; 
v_val_178_ = lean_ctor_get(v_useClassical_53_, 0);
v___x_179_ = lean_unbox(v_val_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; uint8_t v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; 
v___x_180_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
v___x_181_ = 0;
v___x_182_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_182_, 0, v___x_181_);
v___x_183_ = lean_unbox(v_a_164_);
lean_ctor_set_uint8(v___x_182_, 1, v___x_183_);
v___x_184_ = lean_unbox(v_val_178_);
lean_ctor_set_uint8(v___x_182_, 2, v___x_184_);
v___x_185_ = lean_unbox(v_a_164_);
lean_dec(v_a_164_);
lean_ctor_set_uint8(v___x_182_, 3, v___x_185_);
lean_inc(v_g_52_);
v___x_186_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_180_, v___x_182_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; 
lean_dec(v_g_52_);
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref_known(v___x_186_, 1);
v_val_100_ = v_a_187_;
v___y_101_ = v___y_159_;
v___y_102_ = v___y_160_;
v___y_103_ = v___y_161_;
v___y_104_ = v___y_162_;
goto v___jp_99_;
}
else
{
lean_object* v_a_188_; uint8_t v___x_189_; 
v_a_188_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_186_, 1);
v___x_189_ = l_Lean_Exception_isInterrupt(v_a_188_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; 
lean_inc(v_a_188_);
v___x_190_ = l_Lean_Exception_isRuntime(v_a_188_);
v___y_92_ = v_a_188_;
v___y_93_ = v___y_160_;
v___y_94_ = v___y_159_;
v___y_95_ = v___y_161_;
v___y_96_ = v___y_162_;
v___y_97_ = v___x_190_;
goto v___jp_91_;
}
else
{
v___y_92_ = v_a_188_;
v___y_93_ = v___y_160_;
v___y_94_ = v___y_159_;
v___y_95_ = v___y_161_;
v___y_96_ = v___y_162_;
v___y_97_ = v___x_189_;
goto v___jp_91_;
}
}
}
else
{
lean_object* v___x_191_; uint8_t v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; 
v___x_191_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__13));
v___x_192_ = 0;
v___x_193_ = 0;
v___x_194_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_194_, 0, v___x_192_);
v___x_195_ = lean_unbox(v_a_164_);
lean_ctor_set_uint8(v___x_194_, 1, v___x_195_);
lean_ctor_set_uint8(v___x_194_, 2, v___x_193_);
v___x_196_ = lean_unbox(v_a_164_);
lean_dec(v_a_164_);
lean_ctor_set_uint8(v___x_194_, 3, v___x_196_);
v___x_197_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_191_, v___x_194_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref_known(v___x_197_, 1);
v_val_100_ = v_a_198_;
v___y_101_ = v___y_159_;
v___y_102_ = v___y_160_;
v___y_103_ = v___y_161_;
v___y_104_ = v___y_162_;
goto v___jp_99_;
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_a_199_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_197_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_197_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_g_52_);
v_a_207_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_163_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_163_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v_g_52_);
v_a_284_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_153_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_153_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec(v_g_52_);
v_a_292_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_151_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_151_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
v___jp_59_:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_box(0);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
v___jp_62_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__2));
v___x_68_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__3));
v___x_69_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_67_, v___x_68_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_82_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_82_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_82_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_82_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
if (lean_obj_tag(v_a_70_) == 0)
{
lean_del_object(v___x_72_);
goto v___jp_59_;
}
else
{
lean_object* v_tail_74_; 
v_tail_74_ = lean_ctor_get(v_a_70_, 1);
if (lean_obj_tag(v_tail_74_) == 0)
{
lean_object* v_head_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v_head_75_ = lean_ctor_get(v_a_70_, 0);
lean_inc(v_head_75_);
lean_dec_ref_known(v_a_70_, 2);
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v_head_75_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_76_);
v___x_78_ = v___x_72_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec_ref_known(v_a_70_, 2);
lean_del_object(v___x_72_);
v___x_80_ = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__7, &l_Lean_MVarId_falseOrByContra___closed__7_once, _init_l_Lean_MVarId_falseOrByContra___closed__7);
v___x_81_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v___x_80_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_81_;
}
}
}
}
else
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
v_a_83_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_69_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_69_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
v___jp_91_:
{
if (v___y_97_ == 0)
{
lean_dec_ref(v___y_92_);
v___y_63_ = v___y_94_;
v___y_64_ = v___y_93_;
v___y_65_ = v___y_95_;
v___y_66_ = v___y_96_;
goto v___jp_62_;
}
else
{
lean_object* v___x_98_; 
lean_dec(v_g_52_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v___y_92_);
return v___x_98_;
}
}
v___jp_99_:
{
if (lean_obj_tag(v_val_100_) == 0)
{
goto v___jp_59_;
}
else
{
lean_object* v_tail_105_; 
v_tail_105_ = lean_ctor_get(v_val_100_, 1);
if (lean_obj_tag(v_tail_105_) == 0)
{
lean_object* v_head_106_; uint8_t v___x_107_; lean_object* v___x_108_; 
v_head_106_ = lean_ctor_get(v_val_100_, 0);
lean_inc(v_head_106_);
lean_dec_ref_known(v_val_100_, 2);
v___x_107_ = 0;
v___x_108_ = l_Lean_Meta_intro1Core(v_head_106_, v___x_107_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_118_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_118_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_snd_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v_snd_113_ = lean_ctor_get(v_a_109_, 1);
lean_inc(v_snd_113_);
lean_dec(v_a_109_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v_snd_113_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_114_);
v___x_116_ = v___x_111_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
v_a_119_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_108_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_108_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec_ref_known(v_val_100_, 2);
v___x_127_ = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__8, &l_Lean_MVarId_falseOrByContra___closed__8_once, _init_l_Lean_MVarId_falseOrByContra___closed__8);
v___x_128_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v___x_127_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
return v___x_128_;
}
}
}
v___jp_129_:
{
if (v___y_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec_ref(v___y_132_);
v___x_138_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__9));
lean_inc_ref(v___y_136_);
v___x_139_ = l_Lean_Name_mkStr2(v___x_138_, v___y_136_);
v___x_140_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_139_, v___y_131_, v___y_133_, v___y_130_, v___y_134_, v___y_135_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_140_, 1);
v_val_100_ = v_a_141_;
v___y_101_ = v___y_133_;
v___y_102_ = v___y_130_;
v___y_103_ = v___y_134_;
v___y_104_ = v___y_135_;
goto v___jp_99_;
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_140_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_140_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
else
{
lean_object* v___x_150_; 
lean_dec_ref(v___y_131_);
lean_dec(v_g_52_);
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v___y_132_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra___boxed(lean_object* v_g_300_, lean_object* v_useClassical_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_MVarId_falseOrByContra(v_g_300_, v_useClassical_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_useClassical_301_);
return v_res_307_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_box(0);
v___x_309_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg(){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___boxed(lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(lean_object* v_00_u03b1_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___boxed(lean_object* v_00_u03b1_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(v_00_u03b1_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0(lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_339_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = lean_box(0);
v___x_350_ = l_Lean_MVarId_falseOrByContra(v_a_348_, v___x_349_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 1);
if (lean_obj_tag(v_a_351_) == 1)
{
lean_object* v_val_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_val_352_ = lean_ctor_get(v_a_351_, 0);
lean_inc(v_val_352_);
lean_dec_ref_known(v_a_351_, 1);
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v_val_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_354_, v___y_339_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec(v_a_351_);
v___x_356_ = lean_box(0);
v___x_357_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_356_, v___y_339_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
return v___x_357_;
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_a_358_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_350_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_350_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_a_366_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_347_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_347_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed(lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_MVarId_elabFalseOrByContra___lam__0(v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra(lean_object* v_x_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
v___x_405_ = l_Lean_Syntax_isOfKind(v_x_394_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v___x_406_;
}
else
{
lean_object* v___f_407_; lean_object* v___x_408_; 
v___f_407_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__5));
v___x_408_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_407_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___boxed(lean_object* v_x_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_MVarId_elabFalseOrByContra(v_x_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1(){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_427_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_428_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
v___x_429_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
v___x_430_ = lean_alloc_closure((void*)(l_Lean_MVarId_elabFalseOrByContra___boxed), 10, 0);
v___x_431_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_427_, v___x_428_, v___x_429_, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___boxed(lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3(){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
v___x_461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6));
v___x_462_ = l_Lean_addBuiltinDeclarationRanges(v___x_460_, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___boxed(lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
return v_res_464_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
}
#ifdef __cplusplus
}
#endif
