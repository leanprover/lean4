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
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
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
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static lean_once_cell_t l_Lean_MVarId_falseOrByContra___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_MVarId_falseOrByContra___closed__14;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__15 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__15_value;
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
lean_object* v___f_8_; lean_object* v___x_6190__overap_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0));
v___x_6190__overap_9_ = lean_panic_fn_borrowed(v___f_8_, v_msg_2_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_10_ = lean_apply_5(v___x_6190__overap_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
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
static uint64_t _init_l_Lean_MVarId_falseOrByContra___closed__14(void){
_start:
{
uint8_t v___x_51_; uint64_t v___x_52_; 
v___x_51_ = 0;
v___x_52_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra(lean_object* v_g_54_, lean_object* v_useClassical_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___y_65_; lean_object* v___y_66_; lean_object* v___y_67_; lean_object* v___y_68_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v___y_98_; uint8_t v___y_99_; lean_object* v_val_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_132_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; lean_object* v___y_138_; uint8_t v___y_139_; lean_object* v___x_153_; 
lean_inc(v_g_54_);
v___x_153_ = l_Lean_MVarId_getType(v_g_54_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_155_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref(v___x_153_);
v___x_155_ = l_Lean_Meta_whnfR(v_a_154_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_347_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_347_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_347_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_347_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; 
switch(lean_obj_tag(v_a_156_))
{
case 4:
{
lean_object* v_declName_217_; 
v_declName_217_ = lean_ctor_get(v_a_156_, 0);
if (lean_obj_tag(v_declName_217_) == 1)
{
lean_object* v_pre_218_; 
v_pre_218_ = lean_ctor_get(v_declName_217_, 0);
if (lean_obj_tag(v_pre_218_) == 0)
{
lean_object* v_str_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_str_219_ = lean_ctor_get(v_declName_217_, 1);
v___x_220_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__0));
v___x_221_ = lean_string_dec_eq(v_str_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_del_object(v___x_158_);
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
v___y_163_ = v_a_58_;
v___y_164_ = v_a_59_;
goto v___jp_160_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_224_; 
lean_dec_ref(v_a_156_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v_g_54_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_222_);
v___x_224_ = v___x_158_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
else
{
lean_del_object(v___x_158_);
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
v___y_163_ = v_a_58_;
v___y_164_ = v_a_59_;
goto v___jp_160_;
}
}
else
{
lean_del_object(v___x_158_);
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
v___y_163_ = v_a_58_;
v___y_164_ = v_a_59_;
goto v___jp_160_;
}
}
case 7:
{
lean_object* v___x_226_; uint8_t v_foApprox_227_; uint8_t v_ctxApprox_228_; uint8_t v_quasiPatternApprox_229_; uint8_t v_constApprox_230_; uint8_t v_isDefEqStuckEx_231_; uint8_t v_unificationHints_232_; uint8_t v_proofIrrelevance_233_; uint8_t v_assignSyntheticOpaque_234_; uint8_t v_offsetCnstrs_235_; uint8_t v_etaStruct_236_; uint8_t v_univApprox_237_; uint8_t v_iota_238_; uint8_t v_beta_239_; uint8_t v_proj_240_; uint8_t v_zeta_241_; uint8_t v_zetaDelta_242_; uint8_t v_zetaUnused_243_; uint8_t v_zetaHave_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_a_156_);
lean_del_object(v___x_158_);
v___x_226_ = l_Lean_Meta_Context_config(v_a_56_);
v_foApprox_227_ = lean_ctor_get_uint8(v___x_226_, 0);
v_ctxApprox_228_ = lean_ctor_get_uint8(v___x_226_, 1);
v_quasiPatternApprox_229_ = lean_ctor_get_uint8(v___x_226_, 2);
v_constApprox_230_ = lean_ctor_get_uint8(v___x_226_, 3);
v_isDefEqStuckEx_231_ = lean_ctor_get_uint8(v___x_226_, 4);
v_unificationHints_232_ = lean_ctor_get_uint8(v___x_226_, 5);
v_proofIrrelevance_233_ = lean_ctor_get_uint8(v___x_226_, 6);
v_assignSyntheticOpaque_234_ = lean_ctor_get_uint8(v___x_226_, 7);
v_offsetCnstrs_235_ = lean_ctor_get_uint8(v___x_226_, 8);
v_etaStruct_236_ = lean_ctor_get_uint8(v___x_226_, 10);
v_univApprox_237_ = lean_ctor_get_uint8(v___x_226_, 11);
v_iota_238_ = lean_ctor_get_uint8(v___x_226_, 12);
v_beta_239_ = lean_ctor_get_uint8(v___x_226_, 13);
v_proj_240_ = lean_ctor_get_uint8(v___x_226_, 14);
v_zeta_241_ = lean_ctor_get_uint8(v___x_226_, 15);
v_zetaDelta_242_ = lean_ctor_get_uint8(v___x_226_, 16);
v_zetaUnused_243_ = lean_ctor_get_uint8(v___x_226_, 17);
v_zetaHave_244_ = lean_ctor_get_uint8(v___x_226_, 18);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_283_ == 0)
{
v___x_246_ = v___x_226_;
v_isShared_247_ = v_isSharedCheck_283_;
goto v_resetjp_245_;
}
else
{
lean_dec(v___x_226_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_283_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v_trackZetaDelta_248_; lean_object* v_zetaDeltaSet_249_; lean_object* v_lctx_250_; lean_object* v_localInstances_251_; lean_object* v_defEqCtx_x3f_252_; lean_object* v_synthPendingDepth_253_; lean_object* v_canUnfold_x3f_254_; uint8_t v_univApprox_255_; uint8_t v_inTypeClassResolution_256_; uint8_t v_cacheInferType_257_; uint8_t v___x_258_; lean_object* v_config_260_; 
v_trackZetaDelta_248_ = lean_ctor_get_uint8(v_a_56_, sizeof(void*)*7);
v_zetaDeltaSet_249_ = lean_ctor_get(v_a_56_, 1);
v_lctx_250_ = lean_ctor_get(v_a_56_, 2);
v_localInstances_251_ = lean_ctor_get(v_a_56_, 3);
v_defEqCtx_x3f_252_ = lean_ctor_get(v_a_56_, 4);
v_synthPendingDepth_253_ = lean_ctor_get(v_a_56_, 5);
v_canUnfold_x3f_254_ = lean_ctor_get(v_a_56_, 6);
v_univApprox_255_ = lean_ctor_get_uint8(v_a_56_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_256_ = lean_ctor_get_uint8(v_a_56_, sizeof(void*)*7 + 2);
v_cacheInferType_257_ = lean_ctor_get_uint8(v_a_56_, sizeof(void*)*7 + 3);
v___x_258_ = 0;
if (v_isShared_247_ == 0)
{
v_config_260_ = v___x_246_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 0, v_foApprox_227_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 1, v_ctxApprox_228_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 2, v_quasiPatternApprox_229_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 3, v_constApprox_230_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 4, v_isDefEqStuckEx_231_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 5, v_unificationHints_232_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 6, v_proofIrrelevance_233_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 7, v_assignSyntheticOpaque_234_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 8, v_offsetCnstrs_235_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 10, v_etaStruct_236_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 11, v_univApprox_237_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 12, v_iota_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 13, v_beta_239_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 14, v_proj_240_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 15, v_zeta_241_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 16, v_zetaDelta_242_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 17, v_zetaUnused_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 18, v_zetaHave_244_);
v_config_260_ = v_reuseFailAlloc_282_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
uint64_t v___x_261_; uint64_t v___x_262_; uint64_t v___x_263_; uint64_t v___x_264_; uint64_t v___x_265_; uint64_t v_key_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; lean_object* v___x_270_; 
lean_ctor_set_uint8(v_config_260_, 9, v___x_258_);
v___x_261_ = l_Lean_Meta_Context_configKey(v_a_56_);
v___x_262_ = 2ULL;
v___x_263_ = lean_uint64_shift_right(v___x_261_, v___x_262_);
v___x_264_ = lean_uint64_shift_left(v___x_263_, v___x_262_);
v___x_265_ = lean_uint64_once(&l_Lean_MVarId_falseOrByContra___closed__14, &l_Lean_MVarId_falseOrByContra___closed__14_once, _init_l_Lean_MVarId_falseOrByContra___closed__14);
v_key_266_ = lean_uint64_lor(v___x_264_, v___x_265_);
v___x_267_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_267_, 0, v_config_260_);
lean_ctor_set_uint64(v___x_267_, sizeof(void*)*1, v_key_266_);
lean_inc(v_canUnfold_x3f_254_);
lean_inc(v_synthPendingDepth_253_);
lean_inc(v_defEqCtx_x3f_252_);
lean_inc_ref(v_localInstances_251_);
lean_inc_ref(v_lctx_250_);
lean_inc(v_zetaDeltaSet_249_);
v___x_268_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_zetaDeltaSet_249_);
lean_ctor_set(v___x_268_, 2, v_lctx_250_);
lean_ctor_set(v___x_268_, 3, v_localInstances_251_);
lean_ctor_set(v___x_268_, 4, v_defEqCtx_x3f_252_);
lean_ctor_set(v___x_268_, 5, v_synthPendingDepth_253_);
lean_ctor_set(v___x_268_, 6, v_canUnfold_x3f_254_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*7, v_trackZetaDelta_248_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*7 + 1, v_univApprox_255_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*7 + 2, v_inTypeClassResolution_256_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*7 + 3, v_cacheInferType_257_);
v___x_269_ = 1;
v___x_270_ = l_Lean_Meta_intro1Core(v_g_54_, v___x_269_, v___x_268_, v_a_57_, v_a_58_, v_a_59_);
lean_dec_ref(v___x_268_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v_snd_272_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v___x_270_);
v_snd_272_ = lean_ctor_get(v_a_271_, 1);
lean_inc(v_snd_272_);
lean_dec(v_a_271_);
v_g_54_ = v_snd_272_;
goto _start;
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_270_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_270_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fn_284_; 
lean_del_object(v___x_158_);
v_fn_284_ = lean_ctor_get(v_a_156_, 0);
if (lean_obj_tag(v_fn_284_) == 4)
{
lean_object* v_declName_285_; 
v_declName_285_ = lean_ctor_get(v_fn_284_, 0);
if (lean_obj_tag(v_declName_285_) == 1)
{
lean_object* v_pre_286_; 
v_pre_286_ = lean_ctor_get(v_declName_285_, 0);
if (lean_obj_tag(v_pre_286_) == 0)
{
lean_object* v_str_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_str_287_ = lean_ctor_get(v_declName_285_, 1);
v___x_288_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__15));
v___x_289_ = lean_string_dec_eq(v_str_287_, v___x_288_);
if (v___x_289_ == 0)
{
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
v___y_163_ = v_a_58_;
v___y_164_ = v_a_59_;
goto v___jp_160_;
}
else
{
lean_object* v___x_290_; uint8_t v_foApprox_291_; uint8_t v_ctxApprox_292_; uint8_t v_quasiPatternApprox_293_; uint8_t v_constApprox_294_; uint8_t v_isDefEqStuckEx_295_; uint8_t v_unificationHints_296_; uint8_t v_proofIrrelevance_297_; uint8_t v_assignSyntheticOpaque_298_; uint8_t v_offsetCnstrs_299_; uint8_t v_etaStruct_300_; uint8_t v_univApprox_301_; uint8_t v_iota_302_; uint8_t v_beta_303_; uint8_t v_proj_304_; uint8_t v_zeta_305_; uint8_t v_zetaDelta_306_; uint8_t v_zetaUnused_307_; uint8_t v_zetaHave_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_346_; 
lean_dec_ref(v_a_156_);
v___x_290_ = l_Lean_Meta_Context_config(v_a_56_);
v_foApprox_291_ = lean_ctor_get_uint8(v___x_290_, 0);
v_ctxApprox_292_ = lean_ctor_get_uint8(v___x_290_, 1);
v_quasiPatternApprox_293_ = lean_ctor_get_uint8(v___x_290_, 2);
v_constApprox_294_ = lean_ctor_get_uint8(v___x_290_, 3);
v_isDefEqStuckEx_295_ = lean_ctor_get_uint8(v___x_290_, 4);
v_unificationHints_296_ = lean_ctor_get_uint8(v___x_290_, 5);
v_proofIrrelevance_297_ = lean_ctor_get_uint8(v___x_290_, 6);
v_assignSyntheticOpaque_298_ = lean_ctor_get_uint8(v___x_290_, 7);
v_offsetCnstrs_299_ = lean_ctor_get_uint8(v___x_290_, 8);
v_etaStruct_300_ = lean_ctor_get_uint8(v___x_290_, 10);
v_univApprox_301_ = lean_ctor_get_uint8(v___x_290_, 11);
v_iota_302_ = lean_ctor_get_uint8(v___x_290_, 12);
v_beta_303_ = lean_ctor_get_uint8(v___x_290_, 13);
v_proj_304_ = lean_ctor_get_uint8(v___x_290_, 14);
v_zeta_305_ = lean_ctor_get_uint8(v___x_290_, 15);
v_zetaDelta_306_ = lean_ctor_get_uint8(v___x_290_, 16);
v_zetaUnused_307_ = lean_ctor_get_uint8(v___x_290_, 17);
v_zetaHave_308_ = lean_ctor_get_uint8(v___x_290_, 18);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_346_ == 0)
{
v___x_310_ = v___x_290_;
v_isShared_311_ = v_isSharedCheck_346_;
goto v_resetjp_309_;
}
else
{
lean_dec(v___x_290_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_346_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v_trackZetaDelta_312_; lean_object* v_zetaDeltaSet_313_; lean_object* v_lctx_314_; lean_object* v_localInstances_315_; lean_object* v_defEqCtx_x3f_316_; lean_object* v_synthPendingDepth_317_; lean_object* v_canUnfold_x3f_318_; uint8_t v_univApprox_319_; uint8_t v_inTypeClassResolution_320_; uint8_t v_cacheInferType_321_; uint8_t v___x_322_; lean_object* v_config_324_; 
v_trackZetaDelta_312_ = lean_ctor_get_uint8(v_a_56_, sizeof(void*)*7);
v_zetaDeltaSet_313_ = lean_ctor_get(v_a_56_, 1);
v_lctx_314_ = lean_ctor_get(v_a_56_, 2);
v_localInstances_315_ = lean_ctor_get(v_a_56_, 3);
v_defEqCtx_x3f_316_ = lean_ctor_get(v_a_56_, 4);
v_synthPendingDepth_317_ = lean_ctor_get(v_a_56_, 5);
v_canUnfold_x3f_318_ = lean_ctor_get(v_a_56_, 6);
v_univApprox_319_ = lean_ctor_get_uint8(v_a_56_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_320_ = lean_ctor_get_uint8(v_a_56_, sizeof(void*)*7 + 2);
v_cacheInferType_321_ = lean_ctor_get_uint8(v_a_56_, sizeof(void*)*7 + 3);
v___x_322_ = 0;
if (v_isShared_311_ == 0)
{
v_config_324_ = v___x_310_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 0, v_foApprox_291_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 1, v_ctxApprox_292_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 2, v_quasiPatternApprox_293_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 3, v_constApprox_294_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 4, v_isDefEqStuckEx_295_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 5, v_unificationHints_296_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 6, v_proofIrrelevance_297_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 7, v_assignSyntheticOpaque_298_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 8, v_offsetCnstrs_299_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 10, v_etaStruct_300_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 11, v_univApprox_301_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 12, v_iota_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 13, v_beta_303_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 14, v_proj_304_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 15, v_zeta_305_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 16, v_zetaDelta_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 17, v_zetaUnused_307_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, 18, v_zetaHave_308_);
v_config_324_ = v_reuseFailAlloc_345_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v_key_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
lean_ctor_set_uint8(v_config_324_, 9, v___x_322_);
v___x_325_ = l_Lean_Meta_Context_configKey(v_a_56_);
v___x_326_ = 2ULL;
v___x_327_ = lean_uint64_shift_right(v___x_325_, v___x_326_);
v___x_328_ = lean_uint64_shift_left(v___x_327_, v___x_326_);
v___x_329_ = lean_uint64_once(&l_Lean_MVarId_falseOrByContra___closed__14, &l_Lean_MVarId_falseOrByContra___closed__14_once, _init_l_Lean_MVarId_falseOrByContra___closed__14);
v_key_330_ = lean_uint64_lor(v___x_328_, v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_331_, 0, v_config_324_);
lean_ctor_set_uint64(v___x_331_, sizeof(void*)*1, v_key_330_);
lean_inc(v_canUnfold_x3f_318_);
lean_inc(v_synthPendingDepth_317_);
lean_inc(v_defEqCtx_x3f_316_);
lean_inc_ref(v_localInstances_315_);
lean_inc_ref(v_lctx_314_);
lean_inc(v_zetaDeltaSet_313_);
v___x_332_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_zetaDeltaSet_313_);
lean_ctor_set(v___x_332_, 2, v_lctx_314_);
lean_ctor_set(v___x_332_, 3, v_localInstances_315_);
lean_ctor_set(v___x_332_, 4, v_defEqCtx_x3f_316_);
lean_ctor_set(v___x_332_, 5, v_synthPendingDepth_317_);
lean_ctor_set(v___x_332_, 6, v_canUnfold_x3f_318_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*7, v_trackZetaDelta_312_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*7 + 1, v_univApprox_319_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*7 + 2, v_inTypeClassResolution_320_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*7 + 3, v_cacheInferType_321_);
v___x_333_ = l_Lean_Meta_intro1Core(v_g_54_, v___x_289_, v___x_332_, v_a_57_, v_a_58_, v_a_59_);
lean_dec_ref(v___x_332_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v_snd_335_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref(v___x_333_);
v_snd_335_ = lean_ctor_get(v_a_334_, 1);
lean_inc(v_snd_335_);
lean_dec(v_a_334_);
v_g_54_ = v_snd_335_;
goto _start;
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_a_337_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_333_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_333_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
}
else
{
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
v___y_163_ = v_a_58_;
v___y_164_ = v_a_59_;
goto v___jp_160_;
}
}
else
{
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
v___y_163_ = v_a_58_;
v___y_164_ = v_a_59_;
goto v___jp_160_;
}
}
else
{
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
v___y_163_ = v_a_58_;
v___y_164_ = v_a_59_;
goto v___jp_160_;
}
}
default: 
{
lean_del_object(v___x_158_);
v___y_161_ = v_a_56_;
v___y_162_ = v_a_57_;
v___y_163_ = v_a_58_;
v___y_164_ = v_a_59_;
goto v___jp_160_;
}
}
v___jp_160_:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_isProp(v_a_156_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; uint8_t v___x_167_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref(v___x_165_);
v___x_167_ = lean_unbox(v_a_166_);
if (v___x_167_ == 0)
{
lean_dec(v_a_166_);
v___y_65_ = v___y_161_;
v___y_66_ = v___y_162_;
v___y_67_ = v___y_163_;
v___y_68_ = v___y_164_;
goto v___jp_64_;
}
else
{
if (lean_obj_tag(v_useClassical_55_) == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; uint8_t v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; 
v___x_168_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__11));
v___x_169_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
v___x_170_ = 0;
v___x_171_ = 0;
v___x_172_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_172_, 0, v___x_170_);
v___x_173_ = lean_unbox(v_a_166_);
lean_ctor_set_uint8(v___x_172_, 1, v___x_173_);
lean_ctor_set_uint8(v___x_172_, 2, v___x_171_);
v___x_174_ = lean_unbox(v_a_166_);
lean_dec(v_a_166_);
lean_ctor_set_uint8(v___x_172_, 3, v___x_174_);
lean_inc_ref(v___x_172_);
lean_inc(v_g_54_);
v___x_175_ = l_Lean_MVarId_applyConst(v_g_54_, v___x_169_, v___x_172_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; 
lean_dec_ref(v___x_172_);
lean_dec(v_g_54_);
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref(v___x_175_);
v_val_102_ = v_a_176_;
v___y_103_ = v___y_161_;
v___y_104_ = v___y_162_;
v___y_105_ = v___y_163_;
v___y_106_ = v___y_164_;
goto v___jp_101_;
}
else
{
lean_object* v_a_177_; uint8_t v___x_178_; 
v_a_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_177_);
lean_dec_ref(v___x_175_);
v___x_178_ = l_Lean_Exception_isInterrupt(v_a_177_);
if (v___x_178_ == 0)
{
uint8_t v___x_179_; 
lean_inc(v_a_177_);
v___x_179_ = l_Lean_Exception_isRuntime(v_a_177_);
v___y_132_ = v___y_164_;
v___y_133_ = v___x_172_;
v___y_134_ = v___y_161_;
v___y_135_ = v___x_168_;
v___y_136_ = v_a_177_;
v___y_137_ = v___y_162_;
v___y_138_ = v___y_163_;
v___y_139_ = v___x_179_;
goto v___jp_131_;
}
else
{
v___y_132_ = v___y_164_;
v___y_133_ = v___x_172_;
v___y_134_ = v___y_161_;
v___y_135_ = v___x_168_;
v___y_136_ = v_a_177_;
v___y_137_ = v___y_162_;
v___y_138_ = v___y_163_;
v___y_139_ = v___x_178_;
goto v___jp_131_;
}
}
}
else
{
lean_object* v_val_180_; uint8_t v___x_181_; 
v_val_180_ = lean_ctor_get(v_useClassical_55_, 0);
v___x_181_ = lean_unbox(v_val_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; uint8_t v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; uint8_t v___x_186_; uint8_t v___x_187_; lean_object* v___x_188_; 
v___x_182_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
v___x_183_ = 0;
v___x_184_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_184_, 0, v___x_183_);
v___x_185_ = lean_unbox(v_a_166_);
lean_ctor_set_uint8(v___x_184_, 1, v___x_185_);
v___x_186_ = lean_unbox(v_val_180_);
lean_ctor_set_uint8(v___x_184_, 2, v___x_186_);
v___x_187_ = lean_unbox(v_a_166_);
lean_dec(v_a_166_);
lean_ctor_set_uint8(v___x_184_, 3, v___x_187_);
lean_inc(v_g_54_);
v___x_188_ = l_Lean_MVarId_applyConst(v_g_54_, v___x_182_, v___x_184_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; 
lean_dec(v_g_54_);
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref(v___x_188_);
v_val_102_ = v_a_189_;
v___y_103_ = v___y_161_;
v___y_104_ = v___y_162_;
v___y_105_ = v___y_163_;
v___y_106_ = v___y_164_;
goto v___jp_101_;
}
else
{
lean_object* v_a_190_; uint8_t v___x_191_; 
v_a_190_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_190_);
lean_dec_ref(v___x_188_);
v___x_191_ = l_Lean_Exception_isInterrupt(v_a_190_);
if (v___x_191_ == 0)
{
uint8_t v___x_192_; 
lean_inc(v_a_190_);
v___x_192_ = l_Lean_Exception_isRuntime(v_a_190_);
v___y_94_ = v___y_164_;
v___y_95_ = v_a_190_;
v___y_96_ = v___y_161_;
v___y_97_ = v___y_162_;
v___y_98_ = v___y_163_;
v___y_99_ = v___x_192_;
goto v___jp_93_;
}
else
{
v___y_94_ = v___y_164_;
v___y_95_ = v_a_190_;
v___y_96_ = v___y_161_;
v___y_97_ = v___y_162_;
v___y_98_ = v___y_163_;
v___y_99_ = v___x_191_;
goto v___jp_93_;
}
}
}
else
{
lean_object* v___x_193_; uint8_t v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; 
v___x_193_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__13));
v___x_194_ = 0;
v___x_195_ = 0;
v___x_196_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_196_, 0, v___x_194_);
v___x_197_ = lean_unbox(v_a_166_);
lean_ctor_set_uint8(v___x_196_, 1, v___x_197_);
lean_ctor_set_uint8(v___x_196_, 2, v___x_195_);
v___x_198_ = lean_unbox(v_a_166_);
lean_dec(v_a_166_);
lean_ctor_set_uint8(v___x_196_, 3, v___x_198_);
v___x_199_ = l_Lean_MVarId_applyConst(v_g_54_, v___x_193_, v___x_196_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref(v___x_199_);
v_val_102_ = v_a_200_;
v___y_103_ = v___y_161_;
v___y_104_ = v___y_162_;
v___y_105_ = v___y_163_;
v___y_106_ = v___y_164_;
goto v___jp_101_;
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_a_201_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_199_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec(v_g_54_);
v_a_209_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_165_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_165_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
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
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_g_54_);
v_a_348_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_155_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_155_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_g_54_);
v_a_356_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_153_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_153_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
v___jp_61_:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_box(0);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
v___jp_64_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__2));
v___x_70_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__3));
v___x_71_ = l_Lean_MVarId_applyConst(v_g_54_, v___x_69_, v___x_70_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_84_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_84_ == 0)
{
v___x_74_ = v___x_71_;
v_isShared_75_ = v_isSharedCheck_84_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_84_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
if (lean_obj_tag(v_a_72_) == 0)
{
lean_del_object(v___x_74_);
goto v___jp_61_;
}
else
{
lean_object* v_tail_76_; 
v_tail_76_ = lean_ctor_get(v_a_72_, 1);
if (lean_obj_tag(v_tail_76_) == 0)
{
lean_object* v_head_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v_head_77_ = lean_ctor_get(v_a_72_, 0);
lean_inc(v_head_77_);
lean_dec_ref(v_a_72_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v_head_77_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_78_);
v___x_80_ = v___x_74_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec_ref(v_a_72_);
lean_del_object(v___x_74_);
v___x_82_ = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__7, &l_Lean_MVarId_falseOrByContra___closed__7_once, _init_l_Lean_MVarId_falseOrByContra___closed__7);
v___x_83_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v___x_82_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
return v___x_83_;
}
}
}
}
else
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_a_85_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_71_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_71_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
v___jp_93_:
{
if (v___y_99_ == 0)
{
lean_dec_ref(v___y_95_);
v___y_65_ = v___y_96_;
v___y_66_ = v___y_97_;
v___y_67_ = v___y_98_;
v___y_68_ = v___y_94_;
goto v___jp_64_;
}
else
{
lean_object* v___x_100_; 
lean_dec(v_g_54_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___y_95_);
return v___x_100_;
}
}
v___jp_101_:
{
if (lean_obj_tag(v_val_102_) == 0)
{
goto v___jp_61_;
}
else
{
lean_object* v_tail_107_; 
v_tail_107_ = lean_ctor_get(v_val_102_, 1);
if (lean_obj_tag(v_tail_107_) == 0)
{
lean_object* v_head_108_; uint8_t v___x_109_; lean_object* v___x_110_; 
v_head_108_ = lean_ctor_get(v_val_102_, 0);
lean_inc(v_head_108_);
lean_dec_ref(v_val_102_);
v___x_109_ = 0;
v___x_110_ = l_Lean_Meta_intro1Core(v_head_108_, v___x_109_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_120_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_120_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_120_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_120_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_snd_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v_snd_115_ = lean_ctor_get(v_a_111_, 1);
lean_inc(v_snd_115_);
lean_dec(v_a_111_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_snd_115_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_116_);
v___x_118_ = v___x_113_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_a_121_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_110_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_110_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec_ref(v_val_102_);
v___x_129_ = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__8, &l_Lean_MVarId_falseOrByContra___closed__8_once, _init_l_Lean_MVarId_falseOrByContra___closed__8);
v___x_130_ = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(v___x_129_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
return v___x_130_;
}
}
}
v___jp_131_:
{
if (v___y_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec_ref(v___y_136_);
v___x_140_ = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__9));
lean_inc_ref(v___y_135_);
v___x_141_ = l_Lean_Name_mkStr2(v___x_140_, v___y_135_);
v___x_142_ = l_Lean_MVarId_applyConst(v_g_54_, v___x_141_, v___y_133_, v___y_134_, v___y_137_, v___y_138_, v___y_132_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref(v___x_142_);
v_val_102_ = v_a_143_;
v___y_103_ = v___y_134_;
v___y_104_ = v___y_137_;
v___y_105_ = v___y_138_;
v___y_106_ = v___y_132_;
goto v___jp_101_;
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_a_144_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_142_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v___x_152_; 
lean_dec_ref(v___y_133_);
lean_dec(v_g_54_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___y_136_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra___boxed(lean_object* v_g_364_, lean_object* v_useClassical_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_MVarId_falseOrByContra(v_g_364_, v_useClassical_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_useClassical_365_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_box(0);
v___x_373_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg(){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___boxed(lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(lean_object* v_00_u03b1_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___boxed(lean_object* v_00_u03b1_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(v_00_u03b1_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0(lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_403_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v___x_411_);
v___x_413_ = lean_box(0);
v___x_414_ = l_Lean_MVarId_falseOrByContra(v_a_412_, v___x_413_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v___x_414_);
if (lean_obj_tag(v_a_415_) == 1)
{
lean_object* v_val_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_val_416_ = lean_ctor_get(v_a_415_, 0);
lean_inc(v_val_416_);
lean_dec_ref(v_a_415_);
v___x_417_ = lean_box(0);
v___x_418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_418_, 0, v_val_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_418_, v___y_403_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_a_415_);
v___x_420_ = lean_box(0);
v___x_421_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_420_, v___y_403_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v___x_421_;
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v_a_422_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_414_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_414_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_a_430_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_411_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_411_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed(lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_MVarId_elabFalseOrByContra___lam__0(v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra(lean_object* v_x_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
v___x_469_ = l_Lean_Syntax_isOfKind(v_x_458_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return v___x_470_;
}
else
{
lean_object* v___f_471_; lean_object* v___x_472_; 
v___f_471_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__5));
v___x_472_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_471_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___boxed(lean_object* v_x_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_MVarId_elabFalseOrByContra(v_x_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1(){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_492_ = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
v___x_493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
v___x_494_ = lean_alloc_closure((void*)(l_Lean_MVarId_elabFalseOrByContra___boxed), 10, 0);
v___x_495_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_491_, v___x_492_, v___x_493_, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___boxed(lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3(){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
v___x_525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6));
v___x_526_ = l_Lean_addBuiltinDeclarationRanges(v___x_524_, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___boxed(lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Elab_Tactic_FalseOrByContra_0__Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
return v_res_528_;
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
