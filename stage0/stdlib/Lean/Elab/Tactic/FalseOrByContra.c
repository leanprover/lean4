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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "expected at most one subgoal"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__6 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__6_value;
static lean_once_cell_t l_Lean_MVarId_falseOrByContra___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_falseOrByContra___closed__7;
static lean_once_cell_t l_Lean_MVarId_falseOrByContra___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_falseOrByContra___closed__8;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__9 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__9_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "byContradiction"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__10 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__10_value;
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__9_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__11_value_aux_0),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__10_value),LEAN_SCALAR_PTR_LITERAL(92, 114, 13, 107, 214, 89, 53, 175)}};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__11 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__11_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__12 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__12_value;
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__12_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Lean_MVarId_falseOrByContra___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__13_value_aux_0),((lean_object*)&l_Lean_MVarId_falseOrByContra___closed__10_value),LEAN_SCALAR_PTR_LITERAL(143, 54, 188, 55, 95, 58, 91, 50)}};
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
lean_object* v___f_8_; lean_object* v___x_5559__overap_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0));
v___x_5559__overap_9_ = lean_panic_fn_borrowed(v___f_8_, v_msg_2_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_10_ = lean_apply_5(v___x_5559__overap_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
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
lean_object* v___y_63_; lean_object* v___y_64_; lean_object* v___y_65_; lean_object* v___y_66_; lean_object* v_val_92_; lean_object* v___y_93_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_122_; lean_object* v___y_135_; lean_object* v___x_147_; 
lean_inc(v_g_52_);
v___x_147_ = l_Lean_MVarId_getType(v_g_52_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_149_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_147_, 1);
v___x_149_ = l_Lean_Meta_whnfR(v_a_148_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_295_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_295_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_295_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_295_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; 
switch(lean_obj_tag(v_a_150_))
{
case 4:
{
lean_object* v_declName_241_; 
v_declName_241_ = lean_ctor_get(v_a_150_, 0);
if (lean_obj_tag(v_declName_241_) == 1)
{
lean_object* v_pre_242_; 
v_pre_242_ = lean_ctor_get(v_declName_241_, 0);
if (lean_obj_tag(v_pre_242_) == 0)
{
lean_object* v_str_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_str_243_ = lean_ctor_get(v_declName_241_, 1);
v___x_244_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__0));
v___x_245_ = lean_string_dec_eq(v_str_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_del_object(v___x_152_);
v___y_155_ = v_a_54_;
v___y_156_ = v_a_55_;
v___y_157_ = v_a_56_;
v___y_158_ = v_a_57_;
goto v___jp_154_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_248_; 
lean_dec_ref_known(v_a_150_, 2);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_g_52_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_246_);
v___x_248_ = v___x_152_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
else
{
lean_del_object(v___x_152_);
v___y_155_ = v_a_54_;
v___y_156_ = v_a_55_;
v___y_157_ = v_a_56_;
v___y_158_ = v_a_57_;
goto v___jp_154_;
}
}
else
{
lean_del_object(v___x_152_);
v___y_155_ = v_a_54_;
v___y_156_ = v_a_55_;
v___y_157_ = v_a_56_;
v___y_158_ = v_a_57_;
goto v___jp_154_;
}
}
case 7:
{
lean_object* v___x_250_; uint8_t v_transparency_251_; uint8_t v___x_252_; uint8_t v___x_253_; 
lean_dec_ref_known(v_a_150_, 3);
lean_del_object(v___x_152_);
v___x_250_ = l_Lean_Meta_Context_config(v_a_54_);
v_transparency_251_ = lean_ctor_get_uint8(v___x_250_, 9);
lean_dec_ref(v___x_250_);
v___x_252_ = 0;
v___x_253_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v_keyedConfig_254_; uint8_t v_trackZetaDelta_255_; lean_object* v_zetaDeltaSet_256_; lean_object* v_lctx_257_; lean_object* v_localInstances_258_; lean_object* v_defEqCtx_x3f_259_; lean_object* v_synthPendingDepth_260_; lean_object* v_customCanUnfoldPredicate_x3f_261_; uint8_t v_univApprox_262_; uint8_t v_inTypeClassResolution_263_; uint8_t v_cacheInferType_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; 
v_keyedConfig_254_ = lean_ctor_get(v_a_54_, 0);
v_trackZetaDelta_255_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7);
v_zetaDeltaSet_256_ = lean_ctor_get(v_a_54_, 1);
v_lctx_257_ = lean_ctor_get(v_a_54_, 2);
v_localInstances_258_ = lean_ctor_get(v_a_54_, 3);
v_defEqCtx_x3f_259_ = lean_ctor_get(v_a_54_, 4);
v_synthPendingDepth_260_ = lean_ctor_get(v_a_54_, 5);
v_customCanUnfoldPredicate_x3f_261_ = lean_ctor_get(v_a_54_, 6);
v_univApprox_262_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_263_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 2);
v_cacheInferType_264_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_254_);
v___x_265_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_252_, v_keyedConfig_254_);
lean_inc(v_customCanUnfoldPredicate_x3f_261_);
lean_inc(v_synthPendingDepth_260_);
lean_inc(v_defEqCtx_x3f_259_);
lean_inc_ref(v_localInstances_258_);
lean_inc_ref(v_lctx_257_);
lean_inc(v_zetaDeltaSet_256_);
v___x_266_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_zetaDeltaSet_256_);
lean_ctor_set(v___x_266_, 2, v_lctx_257_);
lean_ctor_set(v___x_266_, 3, v_localInstances_258_);
lean_ctor_set(v___x_266_, 4, v_defEqCtx_x3f_259_);
lean_ctor_set(v___x_266_, 5, v_synthPendingDepth_260_);
lean_ctor_set(v___x_266_, 6, v_customCanUnfoldPredicate_x3f_261_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*7, v_trackZetaDelta_255_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*7 + 1, v_univApprox_262_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*7 + 2, v_inTypeClassResolution_263_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*7 + 3, v_cacheInferType_264_);
v___x_267_ = 1;
v___x_268_ = l_Lean_Meta_intro1Core(v_g_52_, v___x_267_, v___x_266_, v_a_55_, v_a_56_, v_a_57_);
lean_dec_ref_known(v___x_266_, 7);
v___y_122_ = v___x_268_;
goto v___jp_121_;
}
else
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_intro1Core(v_g_52_, v___x_253_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
v___y_122_ = v___x_269_;
goto v___jp_121_;
}
}
case 5:
{
lean_object* v_fn_270_; 
lean_del_object(v___x_152_);
v_fn_270_ = lean_ctor_get(v_a_150_, 0);
if (lean_obj_tag(v_fn_270_) == 4)
{
lean_object* v_declName_271_; 
v_declName_271_ = lean_ctor_get(v_fn_270_, 0);
if (lean_obj_tag(v_declName_271_) == 1)
{
lean_object* v_pre_272_; 
v_pre_272_ = lean_ctor_get(v_declName_271_, 0);
if (lean_obj_tag(v_pre_272_) == 0)
{
lean_object* v_str_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_str_273_ = lean_ctor_get(v_declName_271_, 1);
v___x_274_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__14));
v___x_275_ = lean_string_dec_eq(v_str_273_, v___x_274_);
if (v___x_275_ == 0)
{
v___y_155_ = v_a_54_;
v___y_156_ = v_a_55_;
v___y_157_ = v_a_56_;
v___y_158_ = v_a_57_;
goto v___jp_154_;
}
else
{
lean_object* v___x_276_; uint8_t v_transparency_277_; uint8_t v___x_278_; uint8_t v___x_279_; 
lean_dec_ref_known(v_a_150_, 2);
v___x_276_ = l_Lean_Meta_Context_config(v_a_54_);
v_transparency_277_ = lean_ctor_get_uint8(v___x_276_, 9);
lean_dec_ref(v___x_276_);
v___x_278_ = 0;
v___x_279_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v_keyedConfig_280_; uint8_t v_trackZetaDelta_281_; lean_object* v_zetaDeltaSet_282_; lean_object* v_lctx_283_; lean_object* v_localInstances_284_; lean_object* v_defEqCtx_x3f_285_; lean_object* v_synthPendingDepth_286_; lean_object* v_customCanUnfoldPredicate_x3f_287_; uint8_t v_univApprox_288_; uint8_t v_inTypeClassResolution_289_; uint8_t v_cacheInferType_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_keyedConfig_280_ = lean_ctor_get(v_a_54_, 0);
v_trackZetaDelta_281_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7);
v_zetaDeltaSet_282_ = lean_ctor_get(v_a_54_, 1);
v_lctx_283_ = lean_ctor_get(v_a_54_, 2);
v_localInstances_284_ = lean_ctor_get(v_a_54_, 3);
v_defEqCtx_x3f_285_ = lean_ctor_get(v_a_54_, 4);
v_synthPendingDepth_286_ = lean_ctor_get(v_a_54_, 5);
v_customCanUnfoldPredicate_x3f_287_ = lean_ctor_get(v_a_54_, 6);
v_univApprox_288_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_289_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 2);
v_cacheInferType_290_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_280_);
v___x_291_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_278_, v_keyedConfig_280_);
lean_inc(v_customCanUnfoldPredicate_x3f_287_);
lean_inc(v_synthPendingDepth_286_);
lean_inc(v_defEqCtx_x3f_285_);
lean_inc_ref(v_localInstances_284_);
lean_inc_ref(v_lctx_283_);
lean_inc(v_zetaDeltaSet_282_);
v___x_292_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_zetaDeltaSet_282_);
lean_ctor_set(v___x_292_, 2, v_lctx_283_);
lean_ctor_set(v___x_292_, 3, v_localInstances_284_);
lean_ctor_set(v___x_292_, 4, v_defEqCtx_x3f_285_);
lean_ctor_set(v___x_292_, 5, v_synthPendingDepth_286_);
lean_ctor_set(v___x_292_, 6, v_customCanUnfoldPredicate_x3f_287_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*7, v_trackZetaDelta_281_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*7 + 1, v_univApprox_288_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*7 + 2, v_inTypeClassResolution_289_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*7 + 3, v_cacheInferType_290_);
v___x_293_ = l_Lean_Meta_intro1Core(v_g_52_, v___x_275_, v___x_292_, v_a_55_, v_a_56_, v_a_57_);
lean_dec_ref_known(v___x_292_, 7);
v___y_135_ = v___x_293_;
goto v___jp_134_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_intro1Core(v_g_52_, v___x_279_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
v___y_135_ = v___x_294_;
goto v___jp_134_;
}
}
}
else
{
v___y_155_ = v_a_54_;
v___y_156_ = v_a_55_;
v___y_157_ = v_a_56_;
v___y_158_ = v_a_57_;
goto v___jp_154_;
}
}
else
{
v___y_155_ = v_a_54_;
v___y_156_ = v_a_55_;
v___y_157_ = v_a_56_;
v___y_158_ = v_a_57_;
goto v___jp_154_;
}
}
else
{
v___y_155_ = v_a_54_;
v___y_156_ = v_a_55_;
v___y_157_ = v_a_56_;
v___y_158_ = v_a_57_;
goto v___jp_154_;
}
}
default: 
{
lean_del_object(v___x_152_);
v___y_155_ = v_a_54_;
v___y_156_ = v_a_55_;
v___y_157_ = v_a_56_;
v___y_158_ = v_a_57_;
goto v___jp_154_;
}
}
v___jp_154_:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_isProp(v_a_150_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; uint8_t v___x_161_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v___x_159_, 1);
v___x_161_ = lean_unbox(v_a_160_);
if (v___x_161_ == 0)
{
lean_dec(v_a_160_);
v___y_63_ = v___y_155_;
v___y_64_ = v___y_156_;
v___y_65_ = v___y_157_;
v___y_66_ = v___y_158_;
goto v___jp_62_;
}
else
{
if (lean_obj_tag(v_useClassical_53_) == 0)
{
lean_object* v___x_162_; uint8_t v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; 
v___x_162_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__11));
v___x_163_ = 0;
v___x_164_ = 0;
v___x_165_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_165_, 0, v___x_163_);
v___x_166_ = lean_unbox(v_a_160_);
lean_ctor_set_uint8(v___x_165_, 1, v___x_166_);
lean_ctor_set_uint8(v___x_165_, 2, v___x_164_);
v___x_167_ = lean_unbox(v_a_160_);
lean_dec(v_a_160_);
lean_ctor_set_uint8(v___x_165_, 3, v___x_167_);
lean_inc_ref(v___x_165_);
lean_inc(v_g_52_);
v___x_168_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_162_, v___x_165_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; 
lean_dec_ref_known(v___x_165_, 0);
lean_dec(v_g_52_);
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref_known(v___x_168_, 1);
v_val_92_ = v_a_169_;
v___y_93_ = v___y_155_;
v___y_94_ = v___y_156_;
v___y_95_ = v___y_157_;
v___y_96_ = v___y_158_;
goto v___jp_91_;
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_193_; 
v_a_170_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_193_ == 0)
{
v___x_172_ = v___x_168_;
v_isShared_173_ = v_isSharedCheck_193_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_193_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint8_t v___x_174_; 
v___x_174_ = l_Lean_Exception_isInterrupt(v_a_170_);
if (v___x_174_ == 0)
{
uint8_t v___x_175_; 
lean_inc(v_a_170_);
v___x_175_ = l_Lean_Exception_isRuntime(v_a_170_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_del_object(v___x_172_);
lean_dec(v_a_170_);
v___x_176_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__13));
v___x_177_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_176_, v___x_165_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v_val_92_ = v_a_178_;
v___y_93_ = v___y_155_;
v___y_94_ = v___y_156_;
v___y_95_ = v___y_157_;
v___y_96_ = v___y_158_;
goto v___jp_91_;
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_177_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_177_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v___x_188_; 
lean_dec_ref_known(v___x_165_, 0);
lean_dec(v_g_52_);
if (v_isShared_173_ == 0)
{
v___x_188_ = v___x_172_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_170_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
lean_object* v___x_191_; 
lean_dec_ref_known(v___x_165_, 0);
lean_dec(v_g_52_);
if (v_isShared_173_ == 0)
{
v___x_191_ = v___x_172_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_170_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
else
{
lean_object* v_val_194_; uint8_t v___x_195_; 
v_val_194_ = lean_ctor_get(v_useClassical_53_, 0);
v___x_195_ = lean_unbox(v_val_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; 
v___x_196_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__11));
v___x_197_ = 0;
v___x_198_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_198_, 0, v___x_197_);
v___x_199_ = lean_unbox(v_a_160_);
lean_ctor_set_uint8(v___x_198_, 1, v___x_199_);
v___x_200_ = lean_unbox(v_val_194_);
lean_ctor_set_uint8(v___x_198_, 2, v___x_200_);
v___x_201_ = lean_unbox(v_a_160_);
lean_dec(v_a_160_);
lean_ctor_set_uint8(v___x_198_, 3, v___x_201_);
lean_inc(v_g_52_);
v___x_202_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_196_, v___x_198_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; 
lean_dec(v_g_52_);
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v_val_92_ = v_a_203_;
v___y_93_ = v___y_155_;
v___y_94_ = v___y_156_;
v___y_95_ = v___y_157_;
v___y_96_ = v___y_158_;
goto v___jp_91_;
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_216_; 
v_a_204_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_216_ == 0)
{
v___x_206_ = v___x_202_;
v_isShared_207_ = v_isSharedCheck_216_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_202_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_216_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
uint8_t v___x_208_; 
v___x_208_ = l_Lean_Exception_isInterrupt(v_a_204_);
if (v___x_208_ == 0)
{
uint8_t v___x_209_; 
lean_inc(v_a_204_);
v___x_209_ = l_Lean_Exception_isRuntime(v_a_204_);
if (v___x_209_ == 0)
{
lean_del_object(v___x_206_);
lean_dec(v_a_204_);
v___y_63_ = v___y_155_;
v___y_64_ = v___y_156_;
v___y_65_ = v___y_157_;
v___y_66_ = v___y_158_;
goto v___jp_62_;
}
else
{
lean_object* v___x_211_; 
lean_dec(v_g_52_);
if (v_isShared_207_ == 0)
{
v___x_211_ = v___x_206_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_204_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
else
{
lean_object* v___x_214_; 
lean_dec(v_g_52_);
if (v_isShared_207_ == 0)
{
v___x_214_ = v___x_206_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_204_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
else
{
lean_object* v___x_217_; uint8_t v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; 
v___x_217_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__13));
v___x_218_ = 0;
v___x_219_ = 0;
v___x_220_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_220_, 0, v___x_218_);
v___x_221_ = lean_unbox(v_a_160_);
lean_ctor_set_uint8(v___x_220_, 1, v___x_221_);
lean_ctor_set_uint8(v___x_220_, 2, v___x_219_);
v___x_222_ = lean_unbox(v_a_160_);
lean_dec(v_a_160_);
lean_ctor_set_uint8(v___x_220_, 3, v___x_222_);
v___x_223_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_217_, v___x_220_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v_val_92_ = v_a_224_;
v___y_93_ = v___y_155_;
v___y_94_ = v___y_156_;
v___y_95_ = v___y_157_;
v___y_96_ = v___y_158_;
goto v___jp_91_;
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
v_a_225_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_223_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_223_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec(v_g_52_);
v_a_233_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_159_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_159_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v_g_52_);
v_a_296_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_149_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_149_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec(v_g_52_);
v_a_304_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_147_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_147_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
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
if (lean_obj_tag(v_val_92_) == 0)
{
goto v___jp_59_;
}
else
{
lean_object* v_tail_97_; 
v_tail_97_ = lean_ctor_get(v_val_92_, 1);
if (lean_obj_tag(v_tail_97_) == 0)
{
lean_object* v_head_98_; uint8_t v___x_99_; lean_object* v___x_100_; 
v_head_98_ = lean_ctor_get(v_val_92_, 0);
lean_inc(v_head_98_);
lean_dec_ref_known(v_val_92_, 2);
v___x_99_ = 0;
v___x_100_ = l_Lean_Meta_intro1Core(v_head_98_, v___x_99_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_110_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_110_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v_snd_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
v_snd_105_ = lean_ctor_get(v_a_101_, 1);
lean_inc(v_snd_105_);
lean_dec(v_a_101_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v_snd_105_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_106_);
v___x_108_ = v___x_103_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_a_111_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v___x_100_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_100_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec_ref_known(v_val_92_, 2);
v___x_119_ = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__8, &l_Lean_MVarId_falseOrByContra___closed__8_once, _init_l_Lean_MVarId_falseOrByContra___closed__8);
v___x_120_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v___x_119_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
return v___x_120_;
}
}
}
v___jp_121_:
{
if (lean_obj_tag(v___y_122_) == 0)
{
lean_object* v_a_123_; lean_object* v_snd_124_; 
v_a_123_ = lean_ctor_get(v___y_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___y_122_, 1);
v_snd_124_ = lean_ctor_get(v_a_123_, 1);
lean_inc(v_snd_124_);
lean_dec(v_a_123_);
v_g_52_ = v_snd_124_;
goto _start;
}
else
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
v_a_126_ = lean_ctor_get(v___y_122_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___y_122_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___y_122_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___y_122_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
v___jp_134_:
{
if (lean_obj_tag(v___y_135_) == 0)
{
lean_object* v_a_136_; lean_object* v_snd_137_; 
v_a_136_ = lean_ctor_get(v___y_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___y_135_, 1);
v_snd_137_ = lean_ctor_get(v_a_136_, 1);
lean_inc(v_snd_137_);
lean_dec(v_a_136_);
v_g_52_ = v_snd_137_;
goto _start;
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___y_135_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___y_135_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___y_135_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___y_135_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra___boxed(lean_object* v_g_312_, lean_object* v_useClassical_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_MVarId_falseOrByContra(v_g_312_, v_useClassical_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_useClassical_313_);
return v_res_319_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_box(0);
v___x_321_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg(){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___boxed(lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(lean_object* v_00_u03b1_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___boxed(lean_object* v_00_u03b1_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(v_00_u03b1_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0(lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_351_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
v___x_361_ = lean_box(0);
v___x_362_ = l_Lean_MVarId_falseOrByContra(v_a_360_, v___x_361_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
if (lean_obj_tag(v_a_363_) == 1)
{
lean_object* v_val_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_val_364_ = lean_ctor_get(v_a_363_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v_a_363_, 1);
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_366_, 0, v_val_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_366_, v___y_351_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v_a_363_);
v___x_368_ = lean_box(0);
v___x_369_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_368_, v___y_351_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
return v___x_369_;
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
v_a_370_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_362_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_362_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
v_a_378_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_359_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_359_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed(lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_MVarId_elabFalseOrByContra___lam__0(v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra(lean_object* v_x_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
v___x_417_ = l_Lean_Syntax_isOfKind(v_x_406_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v___x_418_;
}
else
{
lean_object* v___f_419_; lean_object* v___x_420_; 
v___f_419_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__5));
v___x_420_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_419_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___boxed(lean_object* v_x_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_MVarId_elabFalseOrByContra(v_x_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1(){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_439_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_440_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
v___x_441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
v___x_442_ = lean_alloc_closure((void*)(l_Lean_MVarId_elabFalseOrByContra___boxed), 10, 0);
v___x_443_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_439_, v___x_440_, v___x_441_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___boxed(lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3(){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
v___x_473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6));
v___x_474_ = l_Lean_addBuiltinDeclarationRanges(v___x_472_, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___boxed(lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
return v_res_476_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
