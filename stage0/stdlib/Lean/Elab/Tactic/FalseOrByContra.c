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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_5615__overap_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0));
v___x_5615__overap_9_ = lean_panic_fn_borrowed(v___f_8_, v_msg_2_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_10_ = lean_apply_5(v___x_5615__overap_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_10_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_MVarId_falseOrByContra_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2_ = stack[0].m_obj;
lean_object* v___y_3_ = stack[1].m_obj;
lean_object* v___y_4_ = stack[2].m_obj;
lean_object* v___y_5_ = stack[3].m_obj;
lean_object* v___y_6_ = stack[4].m_obj;
lean_object* v_res_11_;
v_res_11_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v_msg_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___boxed(lean_object* v_msg_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v_msg_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
static lean_object* _init_l_Lean_MVarId_falseOrByContra___closed__7(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_31_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__6));
v___x_32_ = lean_unsigned_to_nat(13u);
v___x_33_ = lean_unsigned_to_nat(66u);
v___x_34_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__5));
v___x_35_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__4));
v___x_36_ = l_mkPanicMessageWithDecl(v___x_35_, v___x_34_, v___x_33_, v___x_32_, v___x_31_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_MVarId_falseOrByContra___closed__8(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_37_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__6));
v___x_38_ = lean_unsigned_to_nat(16u);
v___x_39_ = lean_unsigned_to_nat(61u);
v___x_40_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__5));
v___x_41_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__4));
v___x_42_ = l_mkPanicMessageWithDecl(v___x_41_, v___x_40_, v___x_39_, v___x_38_, v___x_37_);
return v___x_42_;
}
}
lean_object* l_Lean_MVarId_falseOrByContra(lean_object* v_g_53_, lean_object* v_useClassical_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___y_64_; lean_object* v___y_65_; lean_object* v___y_66_; lean_object* v___y_67_; lean_object* v___y_93_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_97_; uint8_t v___y_98_; lean_object* v_val_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_131_; lean_object* v___y_132_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; uint8_t v___y_138_; lean_object* v___y_153_; lean_object* v___y_166_; lean_object* v___x_178_; 
lean_inc(v_g_53_);
v___x_178_ = l_Lean_MVarId_getType(v_g_53_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = l_Lean_Meta_whnfR(v_a_179_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_296_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_296_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_296_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_296_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; 
switch(lean_obj_tag(v_a_181_))
{
case 4:
{
lean_object* v_declName_242_; 
v_declName_242_ = lean_ctor_get(v_a_181_, 0);
if (lean_obj_tag(v_declName_242_) == 1)
{
lean_object* v_pre_243_; 
v_pre_243_ = lean_ctor_get(v_declName_242_, 0);
if (lean_obj_tag(v_pre_243_) == 0)
{
lean_object* v_str_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_str_244_ = lean_ctor_get(v_declName_242_, 1);
v___x_245_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__0));
v___x_246_ = lean_string_dec_eq(v_str_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_del_object(v___x_183_);
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
v___y_189_ = v_a_58_;
goto v___jp_185_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_249_; 
lean_dec_ref_known(v_a_181_, 2);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v_g_53_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_247_);
v___x_249_ = v___x_183_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_del_object(v___x_183_);
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
v___y_189_ = v_a_58_;
goto v___jp_185_;
}
}
else
{
lean_del_object(v___x_183_);
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
v___y_189_ = v_a_58_;
goto v___jp_185_;
}
}
case 7:
{
lean_object* v___x_251_; uint8_t v_transparency_252_; uint8_t v___x_253_; uint8_t v___x_254_; 
lean_dec_ref_known(v_a_181_, 3);
lean_del_object(v___x_183_);
v___x_251_ = l_Lean_Meta_Context_config(v_a_55_);
v_transparency_252_ = lean_ctor_get_uint8(v___x_251_, 9);
lean_dec_ref(v___x_251_);
v___x_253_ = 0;
v___x_254_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_252_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v_keyedConfig_255_; uint8_t v_trackZetaDelta_256_; lean_object* v_zetaDeltaSet_257_; lean_object* v_lctx_258_; lean_object* v_localInstances_259_; lean_object* v_defEqCtx_x3f_260_; lean_object* v_synthPendingDepth_261_; lean_object* v_customCanUnfoldPredicate_x3f_262_; uint8_t v_univApprox_263_; uint8_t v_inTypeClassResolution_264_; uint8_t v_cacheInferType_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; 
v_keyedConfig_255_ = lean_ctor_get(v_a_55_, 0);
v_trackZetaDelta_256_ = lean_ctor_get_uint8(v_a_55_, sizeof(void*)*7);
v_zetaDeltaSet_257_ = lean_ctor_get(v_a_55_, 1);
v_lctx_258_ = lean_ctor_get(v_a_55_, 2);
v_localInstances_259_ = lean_ctor_get(v_a_55_, 3);
v_defEqCtx_x3f_260_ = lean_ctor_get(v_a_55_, 4);
v_synthPendingDepth_261_ = lean_ctor_get(v_a_55_, 5);
v_customCanUnfoldPredicate_x3f_262_ = lean_ctor_get(v_a_55_, 6);
v_univApprox_263_ = lean_ctor_get_uint8(v_a_55_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_264_ = lean_ctor_get_uint8(v_a_55_, sizeof(void*)*7 + 2);
v_cacheInferType_265_ = lean_ctor_get_uint8(v_a_55_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_255_);
v___x_266_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_253_, v_keyedConfig_255_);
lean_inc(v_customCanUnfoldPredicate_x3f_262_);
lean_inc(v_synthPendingDepth_261_);
lean_inc(v_defEqCtx_x3f_260_);
lean_inc_ref(v_localInstances_259_);
lean_inc_ref(v_lctx_258_);
lean_inc(v_zetaDeltaSet_257_);
v___x_267_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_zetaDeltaSet_257_);
lean_ctor_set(v___x_267_, 2, v_lctx_258_);
lean_ctor_set(v___x_267_, 3, v_localInstances_259_);
lean_ctor_set(v___x_267_, 4, v_defEqCtx_x3f_260_);
lean_ctor_set(v___x_267_, 5, v_synthPendingDepth_261_);
lean_ctor_set(v___x_267_, 6, v_customCanUnfoldPredicate_x3f_262_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*7, v_trackZetaDelta_256_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*7 + 1, v_univApprox_263_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*7 + 2, v_inTypeClassResolution_264_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*7 + 3, v_cacheInferType_265_);
v___x_268_ = 1;
v___x_269_ = l_Lean_Meta_intro1Core(v_g_53_, v___x_268_, v___x_267_, v_a_56_, v_a_57_, v_a_58_);
lean_dec_ref_known(v___x_267_, 7);
v___y_153_ = v___x_269_;
goto v___jp_152_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Meta_intro1Core(v_g_53_, v___x_254_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
v___y_153_ = v___x_270_;
goto v___jp_152_;
}
}
case 5:
{
lean_object* v_fn_271_; 
lean_del_object(v___x_183_);
v_fn_271_ = lean_ctor_get(v_a_181_, 0);
if (lean_obj_tag(v_fn_271_) == 4)
{
lean_object* v_declName_272_; 
v_declName_272_ = lean_ctor_get(v_fn_271_, 0);
if (lean_obj_tag(v_declName_272_) == 1)
{
lean_object* v_pre_273_; 
v_pre_273_ = lean_ctor_get(v_declName_272_, 0);
if (lean_obj_tag(v_pre_273_) == 0)
{
lean_object* v_str_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_str_274_ = lean_ctor_get(v_declName_272_, 1);
v___x_275_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__14));
v___x_276_ = lean_string_dec_eq(v_str_274_, v___x_275_);
if (v___x_276_ == 0)
{
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
v___y_189_ = v_a_58_;
goto v___jp_185_;
}
else
{
lean_object* v___x_277_; uint8_t v_transparency_278_; uint8_t v___x_279_; uint8_t v___x_280_; 
lean_dec_ref_known(v_a_181_, 2);
v___x_277_ = l_Lean_Meta_Context_config(v_a_55_);
v_transparency_278_ = lean_ctor_get_uint8(v___x_277_, 9);
lean_dec_ref(v___x_277_);
v___x_279_ = 0;
v___x_280_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v_keyedConfig_281_; uint8_t v_trackZetaDelta_282_; lean_object* v_zetaDeltaSet_283_; lean_object* v_lctx_284_; lean_object* v_localInstances_285_; lean_object* v_defEqCtx_x3f_286_; lean_object* v_synthPendingDepth_287_; lean_object* v_customCanUnfoldPredicate_x3f_288_; uint8_t v_univApprox_289_; uint8_t v_inTypeClassResolution_290_; uint8_t v_cacheInferType_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_keyedConfig_281_ = lean_ctor_get(v_a_55_, 0);
v_trackZetaDelta_282_ = lean_ctor_get_uint8(v_a_55_, sizeof(void*)*7);
v_zetaDeltaSet_283_ = lean_ctor_get(v_a_55_, 1);
v_lctx_284_ = lean_ctor_get(v_a_55_, 2);
v_localInstances_285_ = lean_ctor_get(v_a_55_, 3);
v_defEqCtx_x3f_286_ = lean_ctor_get(v_a_55_, 4);
v_synthPendingDepth_287_ = lean_ctor_get(v_a_55_, 5);
v_customCanUnfoldPredicate_x3f_288_ = lean_ctor_get(v_a_55_, 6);
v_univApprox_289_ = lean_ctor_get_uint8(v_a_55_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_290_ = lean_ctor_get_uint8(v_a_55_, sizeof(void*)*7 + 2);
v_cacheInferType_291_ = lean_ctor_get_uint8(v_a_55_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_281_);
v___x_292_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_279_, v_keyedConfig_281_);
lean_inc(v_customCanUnfoldPredicate_x3f_288_);
lean_inc(v_synthPendingDepth_287_);
lean_inc(v_defEqCtx_x3f_286_);
lean_inc_ref(v_localInstances_285_);
lean_inc_ref(v_lctx_284_);
lean_inc(v_zetaDeltaSet_283_);
v___x_293_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_zetaDeltaSet_283_);
lean_ctor_set(v___x_293_, 2, v_lctx_284_);
lean_ctor_set(v___x_293_, 3, v_localInstances_285_);
lean_ctor_set(v___x_293_, 4, v_defEqCtx_x3f_286_);
lean_ctor_set(v___x_293_, 5, v_synthPendingDepth_287_);
lean_ctor_set(v___x_293_, 6, v_customCanUnfoldPredicate_x3f_288_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*7, v_trackZetaDelta_282_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*7 + 1, v_univApprox_289_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*7 + 2, v_inTypeClassResolution_290_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*7 + 3, v_cacheInferType_291_);
v___x_294_ = l_Lean_Meta_intro1Core(v_g_53_, v___x_276_, v___x_293_, v_a_56_, v_a_57_, v_a_58_);
lean_dec_ref_known(v___x_293_, 7);
v___y_166_ = v___x_294_;
goto v___jp_165_;
}
else
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_intro1Core(v_g_53_, v___x_280_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
v___y_166_ = v___x_295_;
goto v___jp_165_;
}
}
}
else
{
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
v___y_189_ = v_a_58_;
goto v___jp_185_;
}
}
else
{
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
v___y_189_ = v_a_58_;
goto v___jp_185_;
}
}
else
{
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
v___y_189_ = v_a_58_;
goto v___jp_185_;
}
}
default: 
{
lean_del_object(v___x_183_);
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
v___y_189_ = v_a_58_;
goto v___jp_185_;
}
}
v___jp_185_:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Meta_isProp(v_a_181_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; uint8_t v___x_192_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_190_, 1);
v___x_192_ = lean_unbox(v_a_191_);
if (v___x_192_ == 0)
{
lean_dec(v_a_191_);
v___y_64_ = v___y_186_;
v___y_65_ = v___y_187_;
v___y_66_ = v___y_188_;
v___y_67_ = v___y_189_;
goto v___jp_63_;
}
else
{
if (lean_obj_tag(v_useClassical_54_) == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; 
v___x_193_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__11));
v___x_194_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
v___x_195_ = 0;
v___x_196_ = 0;
v___x_197_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_197_, 0, v___x_195_);
v___x_198_ = lean_unbox(v_a_191_);
lean_ctor_set_uint8(v___x_197_, 1, v___x_198_);
lean_ctor_set_uint8(v___x_197_, 2, v___x_196_);
v___x_199_ = lean_unbox(v_a_191_);
lean_dec(v_a_191_);
lean_ctor_set_uint8(v___x_197_, 3, v___x_199_);
lean_inc_ref(v___x_197_);
lean_inc(v_g_53_);
v___x_200_ = l_Lean_MVarId_applyConst(v_g_53_, v___x_194_, v___x_197_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; 
lean_dec_ref_known(v___x_197_, 0);
lean_dec(v_g_53_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
v_val_101_ = v_a_201_;
v___y_102_ = v___y_186_;
v___y_103_ = v___y_187_;
v___y_104_ = v___y_188_;
v___y_105_ = v___y_189_;
goto v___jp_100_;
}
else
{
lean_object* v_a_202_; uint8_t v___x_203_; 
v_a_202_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_200_, 1);
v___x_203_ = l_Lean_Exception_isInterrupt(v_a_202_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; 
lean_inc(v_a_202_);
v___x_204_ = l_Lean_Exception_isRuntime(v_a_202_);
v___y_131_ = v___y_186_;
v___y_132_ = v_a_202_;
v___y_133_ = v___y_189_;
v___y_134_ = v___x_193_;
v___y_135_ = v___y_187_;
v___y_136_ = v___y_188_;
v___y_137_ = v___x_197_;
v___y_138_ = v___x_204_;
goto v___jp_130_;
}
else
{
v___y_131_ = v___y_186_;
v___y_132_ = v_a_202_;
v___y_133_ = v___y_189_;
v___y_134_ = v___x_193_;
v___y_135_ = v___y_187_;
v___y_136_ = v___y_188_;
v___y_137_ = v___x_197_;
v___y_138_ = v___x_203_;
goto v___jp_130_;
}
}
}
else
{
lean_object* v_val_205_; uint8_t v___x_206_; 
v_val_205_ = lean_ctor_get(v_useClassical_54_, 0);
v___x_206_ = lean_unbox(v_val_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; uint8_t v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; 
v___x_207_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
v___x_208_ = 0;
v___x_209_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_209_, 0, v___x_208_);
v___x_210_ = lean_unbox(v_a_191_);
lean_ctor_set_uint8(v___x_209_, 1, v___x_210_);
v___x_211_ = lean_unbox(v_val_205_);
lean_ctor_set_uint8(v___x_209_, 2, v___x_211_);
v___x_212_ = lean_unbox(v_a_191_);
lean_dec(v_a_191_);
lean_ctor_set_uint8(v___x_209_, 3, v___x_212_);
lean_inc(v_g_53_);
v___x_213_ = l_Lean_MVarId_applyConst(v_g_53_, v___x_207_, v___x_209_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; 
lean_dec(v_g_53_);
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v_val_101_ = v_a_214_;
v___y_102_ = v___y_186_;
v___y_103_ = v___y_187_;
v___y_104_ = v___y_188_;
v___y_105_ = v___y_189_;
goto v___jp_100_;
}
else
{
lean_object* v_a_215_; uint8_t v___x_216_; 
v_a_215_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_213_, 1);
v___x_216_ = l_Lean_Exception_isInterrupt(v_a_215_);
if (v___x_216_ == 0)
{
uint8_t v___x_217_; 
lean_inc(v_a_215_);
v___x_217_ = l_Lean_Exception_isRuntime(v_a_215_);
v___y_93_ = v___y_186_;
v___y_94_ = v___y_189_;
v___y_95_ = v___y_187_;
v___y_96_ = v_a_215_;
v___y_97_ = v___y_188_;
v___y_98_ = v___x_217_;
goto v___jp_92_;
}
else
{
v___y_93_ = v___y_186_;
v___y_94_ = v___y_189_;
v___y_95_ = v___y_187_;
v___y_96_ = v_a_215_;
v___y_97_ = v___y_188_;
v___y_98_ = v___x_216_;
goto v___jp_92_;
}
}
}
else
{
lean_object* v___x_218_; uint8_t v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; uint8_t v___x_223_; lean_object* v___x_224_; 
v___x_218_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__13));
v___x_219_ = 0;
v___x_220_ = 0;
v___x_221_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_221_, 0, v___x_219_);
v___x_222_ = lean_unbox(v_a_191_);
lean_ctor_set_uint8(v___x_221_, 1, v___x_222_);
lean_ctor_set_uint8(v___x_221_, 2, v___x_220_);
v___x_223_ = lean_unbox(v_a_191_);
lean_dec(v_a_191_);
lean_ctor_set_uint8(v___x_221_, 3, v___x_223_);
v___x_224_ = l_Lean_MVarId_applyConst(v_g_53_, v___x_218_, v___x_221_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
v_val_101_ = v_a_225_;
v___y_102_ = v___y_186_;
v___y_103_ = v___y_187_;
v___y_104_ = v___y_188_;
v___y_105_ = v___y_189_;
goto v___jp_100_;
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
v_a_226_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_224_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec(v_g_53_);
v_a_234_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_190_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_190_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec(v_g_53_);
v_a_297_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_180_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_180_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_g_53_);
v_a_305_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_178_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_178_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
v___jp_60_:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_box(0);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
v___jp_63_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__2));
v___x_69_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__3));
v___x_70_ = l_Lean_MVarId_applyConst(v_g_53_, v___x_68_, v___x_69_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_83_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_83_ == 0)
{
v___x_73_ = v___x_70_;
v_isShared_74_ = v_isSharedCheck_83_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_83_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
if (lean_obj_tag(v_a_71_) == 0)
{
lean_del_object(v___x_73_);
goto v___jp_60_;
}
else
{
lean_object* v_tail_75_; 
v_tail_75_ = lean_ctor_get(v_a_71_, 1);
if (lean_obj_tag(v_tail_75_) == 0)
{
lean_object* v_head_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
v_head_76_ = lean_ctor_get(v_a_71_, 0);
lean_inc(v_head_76_);
lean_dec_ref_known(v_a_71_, 2);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v_head_76_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_77_);
v___x_79_ = v___x_73_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec_ref_known(v_a_71_, 2);
lean_del_object(v___x_73_);
v___x_81_ = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__7, &l_Lean_MVarId_falseOrByContra___closed__7_once, _init_l_Lean_MVarId_falseOrByContra___closed__7);
v___x_82_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v___x_81_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
return v___x_82_;
}
}
}
}
else
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
v_a_84_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___x_70_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_70_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
v___jp_92_:
{
if (v___y_98_ == 0)
{
lean_dec_ref(v___y_96_);
v___y_64_ = v___y_93_;
v___y_65_ = v___y_95_;
v___y_66_ = v___y_97_;
v___y_67_ = v___y_94_;
goto v___jp_63_;
}
else
{
lean_object* v___x_99_; 
lean_dec(v_g_53_);
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v___y_96_);
return v___x_99_;
}
}
v___jp_100_:
{
if (lean_obj_tag(v_val_101_) == 0)
{
goto v___jp_60_;
}
else
{
lean_object* v_tail_106_; 
v_tail_106_ = lean_ctor_get(v_val_101_, 1);
if (lean_obj_tag(v_tail_106_) == 0)
{
lean_object* v_head_107_; uint8_t v___x_108_; lean_object* v___x_109_; 
v_head_107_ = lean_ctor_get(v_val_101_, 0);
lean_inc(v_head_107_);
lean_dec_ref_known(v_val_101_, 2);
v___x_108_ = 0;
v___x_109_ = l_Lean_Meta_intro1Core(v_head_107_, v___x_108_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_119_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_119_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_119_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_119_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_snd_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v_snd_114_ = lean_ctor_get(v_a_110_, 1);
lean_inc(v_snd_114_);
lean_dec(v_a_110_);
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v_snd_114_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_115_);
v___x_117_ = v___x_112_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_109_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_109_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec_ref_known(v_val_101_, 2);
v___x_128_ = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__8, &l_Lean_MVarId_falseOrByContra___closed__8_once, _init_l_Lean_MVarId_falseOrByContra___closed__8);
v___x_129_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v___x_128_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
return v___x_129_;
}
}
}
v___jp_130_:
{
if (v___y_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec_ref(v___y_132_);
v___x_139_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__9));
lean_inc_ref(v___y_134_);
v___x_140_ = l_Lean_Name_mkStr2(v___x_139_, v___y_134_);
v___x_141_ = l_Lean_MVarId_applyConst(v_g_53_, v___x_140_, v___y_137_, v___y_131_, v___y_135_, v___y_136_, v___y_133_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
lean_dec_ref_known(v___x_141_, 1);
v_val_101_ = v_a_142_;
v___y_102_ = v___y_131_;
v___y_103_ = v___y_135_;
v___y_104_ = v___y_136_;
v___y_105_ = v___y_133_;
goto v___jp_100_;
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_141_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_141_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_object* v___x_151_; 
lean_dec_ref(v___y_137_);
lean_dec(v_g_53_);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v___y_132_);
return v___x_151_;
}
}
v___jp_152_:
{
if (lean_obj_tag(v___y_153_) == 0)
{
lean_object* v_a_154_; lean_object* v_snd_155_; 
v_a_154_ = lean_ctor_get(v___y_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___y_153_, 1);
v_snd_155_ = lean_ctor_get(v_a_154_, 1);
lean_inc(v_snd_155_);
lean_dec(v_a_154_);
v_g_53_ = v_snd_155_;
goto _start;
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_a_157_ = lean_ctor_get(v___y_153_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___y_153_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___y_153_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___y_153_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
v___jp_165_:
{
if (lean_obj_tag(v___y_166_) == 0)
{
lean_object* v_a_167_; lean_object* v_snd_168_; 
v_a_167_ = lean_ctor_get(v___y_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v___y_166_, 1);
v_snd_168_ = lean_ctor_get(v_a_167_, 1);
lean_inc(v_snd_168_);
lean_dec(v_a_167_);
v_g_53_ = v_snd_168_;
goto _start;
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___y_166_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___y_166_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___y_166_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___y_166_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_falseOrByContra_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_53_ = stack[0].m_obj;
lean_object* v_useClassical_54_ = stack[1].m_obj;
lean_object* v_a_55_ = stack[2].m_obj;
lean_object* v_a_56_ = stack[3].m_obj;
lean_object* v_a_57_ = stack[4].m_obj;
lean_object* v_a_58_ = stack[5].m_obj;
lean_object* v_res_313_;
v_res_313_ = l_Lean_MVarId_falseOrByContra(v_g_53_, v_useClassical_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra___boxed(lean_object* v_g_314_, lean_object* v_useClassical_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_MVarId_falseOrByContra(v_g_314_, v_useClassical_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_useClassical_315_);
return v_res_321_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_box(0);
v___x_323_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
return v___x_324_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg(){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_328_;
v_res_328_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
stack->m_obj
 = v_res_328_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___boxed(lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v_res_330_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(lean_object* v_00_u03b1_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v___x_341_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_332_ = stack[1].m_obj;
lean_object* v___y_333_ = stack[2].m_obj;
lean_object* v___y_334_ = stack[3].m_obj;
lean_object* v___y_335_ = stack[4].m_obj;
lean_object* v___y_336_ = stack[5].m_obj;
lean_object* v___y_337_ = stack[6].m_obj;
lean_object* v___y_338_ = stack[7].m_obj;
lean_object* v___y_339_ = stack[8].m_obj;
lean_object* v_res_342_;
v_res_342_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(lean_box(0), v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
stack->m_obj
 = v_res_342_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___boxed(lean_object* v_00_u03b1_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(v_00_u03b1_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_353_;
}
}
lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0(lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_355_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v___x_365_ = lean_box(0);
v___x_366_ = l_Lean_MVarId_falseOrByContra(v_a_364_, v___x_365_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 1);
if (lean_obj_tag(v_a_367_) == 1)
{
lean_object* v_val_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_val_368_ = lean_ctor_get(v_a_367_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v_a_367_, 1);
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_370_, 0, v_val_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_370_, v___y_355_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec(v_a_367_);
v___x_372_ = lean_box(0);
v___x_373_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_372_, v___y_355_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_373_;
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_366_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_366_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_a_382_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_363_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_363_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_elabFalseOrByContra___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_354_ = stack[0].m_obj;
lean_object* v___y_355_ = stack[1].m_obj;
lean_object* v___y_356_ = stack[2].m_obj;
lean_object* v___y_357_ = stack[3].m_obj;
lean_object* v___y_358_ = stack[4].m_obj;
lean_object* v___y_359_ = stack[5].m_obj;
lean_object* v___y_360_ = stack[6].m_obj;
lean_object* v___y_361_ = stack[7].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_MVarId_elabFalseOrByContra___lam__0(v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed(lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_MVarId_elabFalseOrByContra___lam__0(v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_400_;
}
}
lean_object* l_Lean_MVarId_elabFalseOrByContra(lean_object* v_x_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
v___x_422_ = l_Lean_Syntax_isOfKind(v_x_411_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v___x_423_;
}
else
{
lean_object* v___f_424_; lean_object* v___x_425_; 
v___f_424_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__5));
v___x_425_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_424_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
return v___x_425_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_elabFalseOrByContra_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_411_ = stack[0].m_obj;
lean_object* v_a_412_ = stack[1].m_obj;
lean_object* v_a_413_ = stack[2].m_obj;
lean_object* v_a_414_ = stack[3].m_obj;
lean_object* v_a_415_ = stack[4].m_obj;
lean_object* v_a_416_ = stack[5].m_obj;
lean_object* v_a_417_ = stack[6].m_obj;
lean_object* v_a_418_ = stack[7].m_obj;
lean_object* v_a_419_ = stack[8].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_Lean_MVarId_elabFalseOrByContra(v_x_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___boxed(lean_object* v_x_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_MVarId_elabFalseOrByContra(v_x_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
return v_res_437_;
}
}
lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1(){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_445_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_446_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
v___x_447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
v___x_448_ = lean_alloc_closure((void*)(l_Lean_MVarId_elabFalseOrByContra___boxed), 10, 0);
v___x_449_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_445_, v___x_446_, v___x_447_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_450_;
v_res_450_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___boxed(lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
return v_res_452_;
}
}
lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3(){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
v___x_480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6));
v___x_481_ = l_Lean_addBuiltinDeclarationRanges(v___x_479_, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_482_;
v_res_482_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___boxed(lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
return v_res_484_;
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
