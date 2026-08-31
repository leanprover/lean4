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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
lean_object* v___y_60_; lean_object* v___y_73_; lean_object* v___y_89_; lean_object* v___y_90_; lean_object* v___y_91_; lean_object* v___y_92_; lean_object* v___y_118_; lean_object* v___y_119_; lean_object* v___y_120_; lean_object* v___y_121_; lean_object* v___y_122_; uint8_t v___y_123_; lean_object* v_val_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; uint8_t v___y_163_; lean_object* v___x_177_; 
lean_inc(v_g_52_);
v___x_177_ = l_Lean_MVarId_getType(v_g_52_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v___x_179_ = l_Lean_Meta_whnfR(v_a_178_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_295_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_295_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_295_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_295_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; 
switch(lean_obj_tag(v_a_180_))
{
case 4:
{
lean_object* v_declName_241_; 
v_declName_241_ = lean_ctor_get(v_a_180_, 0);
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
lean_del_object(v___x_182_);
v___y_185_ = v_a_54_;
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
goto v___jp_184_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_248_; 
lean_dec_ref_known(v_a_180_, 2);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_g_52_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_246_);
v___x_248_ = v___x_182_;
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
lean_del_object(v___x_182_);
v___y_185_ = v_a_54_;
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
goto v___jp_184_;
}
}
else
{
lean_del_object(v___x_182_);
v___y_185_ = v_a_54_;
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
goto v___jp_184_;
}
}
case 7:
{
lean_object* v___x_250_; uint8_t v_transparency_251_; uint8_t v___x_252_; uint8_t v___x_253_; 
lean_dec_ref_known(v_a_180_, 3);
lean_del_object(v___x_182_);
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
v___y_73_ = v___x_268_;
goto v___jp_72_;
}
else
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_intro1Core(v_g_52_, v___x_253_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
v___y_73_ = v___x_269_;
goto v___jp_72_;
}
}
case 5:
{
lean_object* v_fn_270_; 
lean_del_object(v___x_182_);
v_fn_270_ = lean_ctor_get(v_a_180_, 0);
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
v___y_185_ = v_a_54_;
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
goto v___jp_184_;
}
else
{
lean_object* v___x_276_; uint8_t v_transparency_277_; uint8_t v___x_278_; uint8_t v___x_279_; 
lean_dec_ref_known(v_a_180_, 2);
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
v___y_60_ = v___x_293_;
goto v___jp_59_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_intro1Core(v_g_52_, v___x_279_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
v___y_60_ = v___x_294_;
goto v___jp_59_;
}
}
}
else
{
v___y_185_ = v_a_54_;
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
goto v___jp_184_;
}
}
else
{
v___y_185_ = v_a_54_;
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
goto v___jp_184_;
}
}
else
{
v___y_185_ = v_a_54_;
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
goto v___jp_184_;
}
}
default: 
{
lean_del_object(v___x_182_);
v___y_185_ = v_a_54_;
v___y_186_ = v_a_55_;
v___y_187_ = v_a_56_;
v___y_188_ = v_a_57_;
goto v___jp_184_;
}
}
v___jp_184_:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Meta_isProp(v_a_180_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; uint8_t v___x_191_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_189_, 1);
v___x_191_ = lean_unbox(v_a_190_);
if (v___x_191_ == 0)
{
lean_dec(v_a_190_);
v___y_89_ = v___y_185_;
v___y_90_ = v___y_186_;
v___y_91_ = v___y_187_;
v___y_92_ = v___y_188_;
goto v___jp_88_;
}
else
{
if (lean_obj_tag(v_useClassical_53_) == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; 
v___x_192_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__11));
v___x_193_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
v___x_194_ = 0;
v___x_195_ = 0;
v___x_196_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_196_, 0, v___x_194_);
v___x_197_ = lean_unbox(v_a_190_);
lean_ctor_set_uint8(v___x_196_, 1, v___x_197_);
lean_ctor_set_uint8(v___x_196_, 2, v___x_195_);
v___x_198_ = lean_unbox(v_a_190_);
lean_dec(v_a_190_);
lean_ctor_set_uint8(v___x_196_, 3, v___x_198_);
lean_inc_ref(v___x_196_);
lean_inc(v_g_52_);
v___x_199_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_193_, v___x_196_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; 
lean_dec_ref_known(v___x_196_, 0);
lean_dec(v_g_52_);
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_199_, 1);
v_val_126_ = v_a_200_;
v___y_127_ = v___y_185_;
v___y_128_ = v___y_186_;
v___y_129_ = v___y_187_;
v___y_130_ = v___y_188_;
goto v___jp_125_;
}
else
{
lean_object* v_a_201_; uint8_t v___x_202_; 
v_a_201_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_199_, 1);
v___x_202_ = l_Lean_Exception_isInterrupt(v_a_201_);
if (v___x_202_ == 0)
{
uint8_t v___x_203_; 
lean_inc(v_a_201_);
v___x_203_ = l_Lean_Exception_isRuntime(v_a_201_);
v___y_156_ = v___x_196_;
v___y_157_ = v_a_201_;
v___y_158_ = v___x_192_;
v___y_159_ = v___y_188_;
v___y_160_ = v___y_185_;
v___y_161_ = v___y_187_;
v___y_162_ = v___y_186_;
v___y_163_ = v___x_203_;
goto v___jp_155_;
}
else
{
v___y_156_ = v___x_196_;
v___y_157_ = v_a_201_;
v___y_158_ = v___x_192_;
v___y_159_ = v___y_188_;
v___y_160_ = v___y_185_;
v___y_161_ = v___y_187_;
v___y_162_ = v___y_186_;
v___y_163_ = v___x_202_;
goto v___jp_155_;
}
}
}
else
{
lean_object* v_val_204_; uint8_t v___x_205_; 
v_val_204_ = lean_ctor_get(v_useClassical_53_, 0);
v___x_205_ = lean_unbox(v_val_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; uint8_t v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; 
v___x_206_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
v___x_207_ = 0;
v___x_208_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_208_, 0, v___x_207_);
v___x_209_ = lean_unbox(v_a_190_);
lean_ctor_set_uint8(v___x_208_, 1, v___x_209_);
v___x_210_ = lean_unbox(v_val_204_);
lean_ctor_set_uint8(v___x_208_, 2, v___x_210_);
v___x_211_ = lean_unbox(v_a_190_);
lean_dec(v_a_190_);
lean_ctor_set_uint8(v___x_208_, 3, v___x_211_);
lean_inc(v_g_52_);
v___x_212_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_206_, v___x_208_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; 
lean_dec(v_g_52_);
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_212_, 1);
v_val_126_ = v_a_213_;
v___y_127_ = v___y_185_;
v___y_128_ = v___y_186_;
v___y_129_ = v___y_187_;
v___y_130_ = v___y_188_;
goto v___jp_125_;
}
else
{
lean_object* v_a_214_; uint8_t v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_212_, 1);
v___x_215_ = l_Lean_Exception_isInterrupt(v_a_214_);
if (v___x_215_ == 0)
{
uint8_t v___x_216_; 
lean_inc(v_a_214_);
v___x_216_ = l_Lean_Exception_isRuntime(v_a_214_);
v___y_118_ = v___y_188_;
v___y_119_ = v___y_185_;
v___y_120_ = v___y_187_;
v___y_121_ = v_a_214_;
v___y_122_ = v___y_186_;
v___y_123_ = v___x_216_;
goto v___jp_117_;
}
else
{
v___y_118_ = v___y_188_;
v___y_119_ = v___y_185_;
v___y_120_ = v___y_187_;
v___y_121_ = v_a_214_;
v___y_122_ = v___y_186_;
v___y_123_ = v___x_215_;
goto v___jp_117_;
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
v___x_221_ = lean_unbox(v_a_190_);
lean_ctor_set_uint8(v___x_220_, 1, v___x_221_);
lean_ctor_set_uint8(v___x_220_, 2, v___x_219_);
v___x_222_ = lean_unbox(v_a_190_);
lean_dec(v_a_190_);
lean_ctor_set_uint8(v___x_220_, 3, v___x_222_);
v___x_223_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_217_, v___x_220_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v_val_126_ = v_a_224_;
v___y_127_ = v___y_185_;
v___y_128_ = v___y_186_;
v___y_129_ = v___y_187_;
v___y_130_ = v___y_188_;
goto v___jp_125_;
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
v_a_233_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_189_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_189_);
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
v_a_296_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_179_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_179_);
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
v_a_304_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_177_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_177_);
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
if (lean_obj_tag(v___y_60_) == 0)
{
lean_object* v_a_61_; lean_object* v_snd_62_; 
v_a_61_ = lean_ctor_get(v___y_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___y_60_, 1);
v_snd_62_ = lean_ctor_get(v_a_61_, 1);
lean_inc(v_snd_62_);
lean_dec(v_a_61_);
v_g_52_ = v_snd_62_;
goto _start;
}
else
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
v_a_64_ = lean_ctor_get(v___y_60_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___y_60_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___y_60_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___y_60_);
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
v___jp_72_:
{
if (lean_obj_tag(v___y_73_) == 0)
{
lean_object* v_a_74_; lean_object* v_snd_75_; 
v_a_74_ = lean_ctor_get(v___y_73_, 0);
lean_inc(v_a_74_);
lean_dec_ref_known(v___y_73_, 1);
v_snd_75_ = lean_ctor_get(v_a_74_, 1);
lean_inc(v_snd_75_);
lean_dec(v_a_74_);
v_g_52_ = v_snd_75_;
goto _start;
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v_a_77_ = lean_ctor_get(v___y_73_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___y_73_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___y_73_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___y_73_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
v___jp_85_:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_box(0);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
v___jp_88_:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__2));
v___x_94_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__3));
v___x_95_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_93_, v___x_94_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_108_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_108_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_108_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_108_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
if (lean_obj_tag(v_a_96_) == 0)
{
lean_del_object(v___x_98_);
goto v___jp_85_;
}
else
{
lean_object* v_tail_100_; 
v_tail_100_ = lean_ctor_get(v_a_96_, 1);
if (lean_obj_tag(v_tail_100_) == 0)
{
lean_object* v_head_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v_head_101_ = lean_ctor_get(v_a_96_, 0);
lean_inc(v_head_101_);
lean_dec_ref_known(v_a_96_, 2);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_head_101_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_102_);
v___x_104_ = v___x_98_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec_ref_known(v_a_96_, 2);
lean_del_object(v___x_98_);
v___x_106_ = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__7, &l_Lean_MVarId_falseOrByContra___closed__7_once, _init_l_Lean_MVarId_falseOrByContra___closed__7);
v___x_107_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v___x_106_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
return v___x_107_;
}
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_a_109_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_95_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_95_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
v___jp_117_:
{
if (v___y_123_ == 0)
{
lean_dec_ref(v___y_121_);
v___y_89_ = v___y_119_;
v___y_90_ = v___y_122_;
v___y_91_ = v___y_120_;
v___y_92_ = v___y_118_;
goto v___jp_88_;
}
else
{
lean_object* v___x_124_; 
lean_dec(v_g_52_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___y_121_);
return v___x_124_;
}
}
v___jp_125_:
{
if (lean_obj_tag(v_val_126_) == 0)
{
goto v___jp_85_;
}
else
{
lean_object* v_tail_131_; 
v_tail_131_ = lean_ctor_get(v_val_126_, 1);
if (lean_obj_tag(v_tail_131_) == 0)
{
lean_object* v_head_132_; uint8_t v___x_133_; lean_object* v___x_134_; 
v_head_132_ = lean_ctor_get(v_val_126_, 0);
lean_inc(v_head_132_);
lean_dec_ref_known(v_val_126_, 2);
v___x_133_ = 0;
v___x_134_ = l_Lean_Meta_intro1Core(v_head_132_, v___x_133_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_144_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_144_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_144_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_144_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v_snd_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
v_snd_139_ = lean_ctor_get(v_a_135_, 1);
lean_inc(v_snd_139_);
lean_dec(v_a_135_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_snd_139_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_140_);
v___x_142_ = v___x_137_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_a_145_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_134_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_134_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref_known(v_val_126_, 2);
v___x_153_ = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__8, &l_Lean_MVarId_falseOrByContra___closed__8_once, _init_l_Lean_MVarId_falseOrByContra___closed__8);
v___x_154_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v___x_153_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
return v___x_154_;
}
}
}
v___jp_155_:
{
if (v___y_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec_ref(v___y_157_);
v___x_164_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__9));
lean_inc_ref(v___y_158_);
v___x_165_ = l_Lean_Name_mkStr2(v___x_164_, v___y_158_);
v___x_166_ = l_Lean_MVarId_applyConst(v_g_52_, v___x_165_, v___y_156_, v___y_160_, v___y_162_, v___y_161_, v___y_159_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v___x_166_, 1);
v_val_126_ = v_a_167_;
v___y_127_ = v___y_160_;
v___y_128_ = v___y_162_;
v___y_129_ = v___y_161_;
v___y_130_ = v___y_159_;
goto v___jp_125_;
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
v_a_168_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_166_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_166_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v___x_176_; 
lean_dec_ref(v___y_156_);
lean_dec(v_g_52_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v___y_157_);
return v___x_176_;
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
