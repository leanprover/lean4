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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__0 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__0_value;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__1 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_once_cell_t l_Lean_MVarId_falseOrByContra___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_MVarId_falseOrByContra___closed__14;
static const lean_string_object l_Lean_MVarId_falseOrByContra___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_MVarId_falseOrByContra___closed__15 = (const lean_object*)&l_Lean_MVarId_falseOrByContra___closed__15_value;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_0),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_1),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value_aux_2),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 186, 236, 85, 98, 241, 184, 126)}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__4 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__4_value;
static const lean_closure_object l_Lean_MVarId_elabFalseOrByContra___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___closed__5 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__5_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "MVarId"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value;
static const lean_string_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabFalseOrByContra"};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_0),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 186, 234, 138, 172, 166, 87, 74)}};
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value_aux_1),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(16, 121, 168, 236, 1, 165, 84, 207)}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2_value;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(62) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__1_value),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(62) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(62) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__4_value),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__2_value),((lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6 = (const lean_object*)&l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6_value;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___closed__0));
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MVarId_falseOrByContra_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_falseOrByContra___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__6));
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(66u);
x_4 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__5));
x_5 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_MVarId_falseOrByContra___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__6));
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_unsigned_to_nat(61u);
x_4 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__5));
x_5 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static uint64_t _init_l_Lean_MVarId_falseOrByContra___closed__14(void) {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_100; 
lean_inc(x_1);
x_100 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_102 = l_Lean_Meta_whnfR(x_101, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_294; 
x_103 = lean_ctor_get(x_102, 0);
x_294 = !lean_is_exclusive(x_102);
if (x_294 == 0)
{
x_104 = x_102;
x_105 = x_294;
goto block_293;
}
else
{
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_box(0);
x_105 = x_294;
goto block_293;
}
block_293:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
switch (lean_obj_tag(x_103)) {
case 4:
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_103, 0);
if (lean_obj_tag(x_163) == 1)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_165 = lean_ctor_get(x_163, 1);
x_166 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__0));
x_167 = lean_string_dec_eq(x_165, x_166);
if (x_167 == 0)
{
lean_del_object(x_104);
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
goto block_162;
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec_ref(x_103);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_1);
if (x_105 == 0)
{
lean_ctor_set(x_104, 0, x_168);
x_169 = x_104;
goto block_170;
}
else
{
lean_object* x_171; 
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_168);
x_169 = x_171;
goto block_170;
}
block_170:
{
return x_169;
}
}
}
else
{
lean_del_object(x_104);
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
goto block_162;
}
}
else
{
lean_del_object(x_104);
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
goto block_162;
}
}
case 7:
{
lean_object* x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; lean_object* x_191; uint8_t x_192; uint8_t x_229; 
lean_dec_ref(x_103);
lean_del_object(x_104);
x_172 = l_Lean_Meta_Context_config(x_3);
x_173 = lean_ctor_get_uint8(x_172, 0);
x_174 = lean_ctor_get_uint8(x_172, 1);
x_175 = lean_ctor_get_uint8(x_172, 2);
x_176 = lean_ctor_get_uint8(x_172, 3);
x_177 = lean_ctor_get_uint8(x_172, 4);
x_178 = lean_ctor_get_uint8(x_172, 5);
x_179 = lean_ctor_get_uint8(x_172, 6);
x_180 = lean_ctor_get_uint8(x_172, 7);
x_181 = lean_ctor_get_uint8(x_172, 8);
x_182 = lean_ctor_get_uint8(x_172, 10);
x_183 = lean_ctor_get_uint8(x_172, 11);
x_184 = lean_ctor_get_uint8(x_172, 12);
x_185 = lean_ctor_get_uint8(x_172, 13);
x_186 = lean_ctor_get_uint8(x_172, 14);
x_187 = lean_ctor_get_uint8(x_172, 15);
x_188 = lean_ctor_get_uint8(x_172, 16);
x_189 = lean_ctor_get_uint8(x_172, 17);
x_190 = lean_ctor_get_uint8(x_172, 18);
x_229 = !lean_is_exclusive(x_172);
if (x_229 == 0)
{
x_191 = x_172;
x_192 = x_229;
goto block_228;
}
else
{
lean_dec(x_172);
x_191 = lean_box(0);
x_192 = x_229;
goto block_228;
}
block_228:
{
uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; lean_object* x_204; 
x_193 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_194 = lean_ctor_get(x_3, 1);
x_195 = lean_ctor_get(x_3, 2);
x_196 = lean_ctor_get(x_3, 3);
x_197 = lean_ctor_get(x_3, 4);
x_198 = lean_ctor_get(x_3, 5);
x_199 = lean_ctor_get(x_3, 6);
x_200 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_201 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_202 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
x_203 = 0;
if (x_192 == 0)
{
x_204 = x_191;
goto block_226;
}
else
{
lean_object* x_227; 
x_227 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_227, 0, x_173);
lean_ctor_set_uint8(x_227, 1, x_174);
lean_ctor_set_uint8(x_227, 2, x_175);
lean_ctor_set_uint8(x_227, 3, x_176);
lean_ctor_set_uint8(x_227, 4, x_177);
lean_ctor_set_uint8(x_227, 5, x_178);
lean_ctor_set_uint8(x_227, 6, x_179);
lean_ctor_set_uint8(x_227, 7, x_180);
lean_ctor_set_uint8(x_227, 8, x_181);
lean_ctor_set_uint8(x_227, 10, x_182);
lean_ctor_set_uint8(x_227, 11, x_183);
lean_ctor_set_uint8(x_227, 12, x_184);
lean_ctor_set_uint8(x_227, 13, x_185);
lean_ctor_set_uint8(x_227, 14, x_186);
lean_ctor_set_uint8(x_227, 15, x_187);
lean_ctor_set_uint8(x_227, 16, x_188);
lean_ctor_set_uint8(x_227, 17, x_189);
lean_ctor_set_uint8(x_227, 18, x_190);
x_204 = x_227;
goto block_226;
}
block_226:
{
uint64_t x_205; uint64_t x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; uint64_t x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; 
lean_ctor_set_uint8(x_204, 9, x_203);
x_205 = l_Lean_Meta_Context_configKey(x_3);
x_206 = 2;
x_207 = lean_uint64_shift_right(x_205, x_206);
x_208 = lean_uint64_shift_left(x_207, x_206);
x_209 = lean_uint64_once(&l_Lean_MVarId_falseOrByContra___closed__14, &l_Lean_MVarId_falseOrByContra___closed__14_once, _init_l_Lean_MVarId_falseOrByContra___closed__14);
x_210 = lean_uint64_lor(x_208, x_209);
x_211 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_211, 0, x_204);
lean_ctor_set_uint64(x_211, sizeof(void*)*1, x_210);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc_ref(x_196);
lean_inc_ref(x_195);
lean_inc(x_194);
x_212 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_194);
lean_ctor_set(x_212, 2, x_195);
lean_ctor_set(x_212, 3, x_196);
lean_ctor_set(x_212, 4, x_197);
lean_ctor_set(x_212, 5, x_198);
lean_ctor_set(x_212, 6, x_199);
lean_ctor_set_uint8(x_212, sizeof(void*)*7, x_193);
lean_ctor_set_uint8(x_212, sizeof(void*)*7 + 1, x_200);
lean_ctor_set_uint8(x_212, sizeof(void*)*7 + 2, x_201);
lean_ctor_set_uint8(x_212, sizeof(void*)*7 + 3, x_202);
x_213 = 1;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_214 = l_Lean_Meta_intro1Core(x_1, x_213, x_212, x_4, x_5, x_6);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
lean_dec_ref(x_214);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_1 = x_216;
goto _start;
}
else
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_225; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_218 = lean_ctor_get(x_214, 0);
x_225 = !lean_is_exclusive(x_214);
if (x_225 == 0)
{
x_219 = x_214;
x_220 = x_225;
goto block_224;
}
else
{
lean_inc(x_218);
lean_dec(x_214);
x_219 = lean_box(0);
x_220 = x_225;
goto block_224;
}
block_224:
{
lean_object* x_221; 
if (x_220 == 0)
{
x_221 = x_219;
goto block_222;
}
else
{
lean_object* x_223; 
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_218);
x_221 = x_223;
goto block_222;
}
block_222:
{
return x_221;
}
}
}
}
}
}
case 5:
{
lean_object* x_230; 
lean_del_object(x_104);
x_230 = lean_ctor_get(x_103, 0);
if (lean_obj_tag(x_230) == 4)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_230, 0);
if (lean_obj_tag(x_231) == 1)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_231, 0);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_233 = lean_ctor_get(x_231, 1);
x_234 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__15));
x_235 = lean_string_dec_eq(x_233, x_234);
if (x_235 == 0)
{
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
goto block_162;
}
else
{
lean_object* x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; uint8_t x_254; lean_object* x_255; uint8_t x_256; uint8_t x_292; 
lean_dec_ref(x_103);
x_236 = l_Lean_Meta_Context_config(x_3);
x_237 = lean_ctor_get_uint8(x_236, 0);
x_238 = lean_ctor_get_uint8(x_236, 1);
x_239 = lean_ctor_get_uint8(x_236, 2);
x_240 = lean_ctor_get_uint8(x_236, 3);
x_241 = lean_ctor_get_uint8(x_236, 4);
x_242 = lean_ctor_get_uint8(x_236, 5);
x_243 = lean_ctor_get_uint8(x_236, 6);
x_244 = lean_ctor_get_uint8(x_236, 7);
x_245 = lean_ctor_get_uint8(x_236, 8);
x_246 = lean_ctor_get_uint8(x_236, 10);
x_247 = lean_ctor_get_uint8(x_236, 11);
x_248 = lean_ctor_get_uint8(x_236, 12);
x_249 = lean_ctor_get_uint8(x_236, 13);
x_250 = lean_ctor_get_uint8(x_236, 14);
x_251 = lean_ctor_get_uint8(x_236, 15);
x_252 = lean_ctor_get_uint8(x_236, 16);
x_253 = lean_ctor_get_uint8(x_236, 17);
x_254 = lean_ctor_get_uint8(x_236, 18);
x_292 = !lean_is_exclusive(x_236);
if (x_292 == 0)
{
x_255 = x_236;
x_256 = x_292;
goto block_291;
}
else
{
lean_dec(x_236);
x_255 = lean_box(0);
x_256 = x_292;
goto block_291;
}
block_291:
{
uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_265; uint8_t x_266; uint8_t x_267; lean_object* x_268; 
x_257 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_258 = lean_ctor_get(x_3, 1);
x_259 = lean_ctor_get(x_3, 2);
x_260 = lean_ctor_get(x_3, 3);
x_261 = lean_ctor_get(x_3, 4);
x_262 = lean_ctor_get(x_3, 5);
x_263 = lean_ctor_get(x_3, 6);
x_264 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_265 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_266 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 3);
x_267 = 0;
if (x_256 == 0)
{
x_268 = x_255;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_290, 0, x_237);
lean_ctor_set_uint8(x_290, 1, x_238);
lean_ctor_set_uint8(x_290, 2, x_239);
lean_ctor_set_uint8(x_290, 3, x_240);
lean_ctor_set_uint8(x_290, 4, x_241);
lean_ctor_set_uint8(x_290, 5, x_242);
lean_ctor_set_uint8(x_290, 6, x_243);
lean_ctor_set_uint8(x_290, 7, x_244);
lean_ctor_set_uint8(x_290, 8, x_245);
lean_ctor_set_uint8(x_290, 10, x_246);
lean_ctor_set_uint8(x_290, 11, x_247);
lean_ctor_set_uint8(x_290, 12, x_248);
lean_ctor_set_uint8(x_290, 13, x_249);
lean_ctor_set_uint8(x_290, 14, x_250);
lean_ctor_set_uint8(x_290, 15, x_251);
lean_ctor_set_uint8(x_290, 16, x_252);
lean_ctor_set_uint8(x_290, 17, x_253);
lean_ctor_set_uint8(x_290, 18, x_254);
x_268 = x_290;
goto block_289;
}
block_289:
{
uint64_t x_269; uint64_t x_270; uint64_t x_271; uint64_t x_272; uint64_t x_273; uint64_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_ctor_set_uint8(x_268, 9, x_267);
x_269 = l_Lean_Meta_Context_configKey(x_3);
x_270 = 2;
x_271 = lean_uint64_shift_right(x_269, x_270);
x_272 = lean_uint64_shift_left(x_271, x_270);
x_273 = lean_uint64_once(&l_Lean_MVarId_falseOrByContra___closed__14, &l_Lean_MVarId_falseOrByContra___closed__14_once, _init_l_Lean_MVarId_falseOrByContra___closed__14);
x_274 = lean_uint64_lor(x_272, x_273);
x_275 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_275, 0, x_268);
lean_ctor_set_uint64(x_275, sizeof(void*)*1, x_274);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc_ref(x_260);
lean_inc_ref(x_259);
lean_inc(x_258);
x_276 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_258);
lean_ctor_set(x_276, 2, x_259);
lean_ctor_set(x_276, 3, x_260);
lean_ctor_set(x_276, 4, x_261);
lean_ctor_set(x_276, 5, x_262);
lean_ctor_set(x_276, 6, x_263);
lean_ctor_set_uint8(x_276, sizeof(void*)*7, x_257);
lean_ctor_set_uint8(x_276, sizeof(void*)*7 + 1, x_264);
lean_ctor_set_uint8(x_276, sizeof(void*)*7 + 2, x_265);
lean_ctor_set_uint8(x_276, sizeof(void*)*7 + 3, x_266);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_277 = l_Lean_Meta_intro1Core(x_1, x_235, x_276, x_4, x_5, x_6);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
lean_dec_ref(x_277);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_1 = x_279;
goto _start;
}
else
{
lean_object* x_281; lean_object* x_282; uint8_t x_283; uint8_t x_288; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_281 = lean_ctor_get(x_277, 0);
x_288 = !lean_is_exclusive(x_277);
if (x_288 == 0)
{
x_282 = x_277;
x_283 = x_288;
goto block_287;
}
else
{
lean_inc(x_281);
lean_dec(x_277);
x_282 = lean_box(0);
x_283 = x_288;
goto block_287;
}
block_287:
{
lean_object* x_284; 
if (x_283 == 0)
{
x_284 = x_282;
goto block_285;
}
else
{
lean_object* x_286; 
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_281);
x_284 = x_286;
goto block_285;
}
block_285:
{
return x_284;
}
}
}
}
}
}
}
else
{
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
goto block_162;
}
}
else
{
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
goto block_162;
}
}
else
{
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
goto block_162;
}
}
default: 
{
lean_del_object(x_104);
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
goto block_162;
}
}
block_162:
{
lean_object* x_110; 
lean_inc(x_109);
lean_inc_ref(x_108);
lean_inc(x_107);
lean_inc_ref(x_106);
x_110 = l_Lean_Meta_isProp(x_103, x_106, x_107, x_108, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
lean_dec(x_111);
x_11 = x_106;
x_12 = x_107;
x_13 = x_108;
x_14 = x_109;
goto block_39;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; 
x_113 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__11));
x_114 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
x_115 = 0;
x_116 = 0;
x_117 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_117, 0, x_115);
x_118 = lean_unbox(x_111);
lean_ctor_set_uint8(x_117, 1, x_118);
lean_ctor_set_uint8(x_117, 2, x_116);
x_119 = lean_unbox(x_111);
lean_dec(x_111);
lean_ctor_set_uint8(x_117, 3, x_119);
lean_inc(x_109);
lean_inc_ref(x_108);
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc_ref(x_117);
lean_inc(x_1);
x_120 = l_Lean_MVarId_applyConst(x_1, x_114, x_117, x_106, x_107, x_108, x_109);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
lean_dec_ref(x_117);
lean_dec(x_1);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_48 = x_121;
x_49 = x_106;
x_50 = x_107;
x_51 = x_108;
x_52 = x_109;
goto block_77;
}
else
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = l_Lean_Exception_isInterrupt(x_122);
if (x_123 == 0)
{
uint8_t x_124; 
lean_inc(x_122);
x_124 = l_Lean_Exception_isRuntime(x_122);
x_78 = x_117;
x_79 = x_122;
x_80 = x_109;
x_81 = x_108;
x_82 = x_107;
x_83 = x_113;
x_84 = x_106;
x_85 = x_124;
goto block_99;
}
else
{
x_78 = x_117;
x_79 = x_122;
x_80 = x_109;
x_81 = x_108;
x_82 = x_107;
x_83 = x_113;
x_84 = x_106;
x_85 = x_123;
goto block_99;
}
}
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_2, 0);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; 
x_127 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__12));
x_128 = 0;
x_129 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_129, 0, x_128);
x_130 = lean_unbox(x_111);
lean_ctor_set_uint8(x_129, 1, x_130);
x_131 = lean_unbox(x_125);
lean_ctor_set_uint8(x_129, 2, x_131);
x_132 = lean_unbox(x_111);
lean_dec(x_111);
lean_ctor_set_uint8(x_129, 3, x_132);
lean_inc(x_109);
lean_inc_ref(x_108);
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc(x_1);
x_133 = l_Lean_MVarId_applyConst(x_1, x_127, x_129, x_106, x_107, x_108, x_109);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
lean_dec(x_1);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_48 = x_134;
x_49 = x_106;
x_50 = x_107;
x_51 = x_108;
x_52 = x_109;
goto block_77;
}
else
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = l_Lean_Exception_isInterrupt(x_135);
if (x_136 == 0)
{
uint8_t x_137; 
lean_inc(x_135);
x_137 = l_Lean_Exception_isRuntime(x_135);
x_40 = x_135;
x_41 = x_109;
x_42 = x_108;
x_43 = x_107;
x_44 = x_106;
x_45 = x_137;
goto block_47;
}
else
{
x_40 = x_135;
x_41 = x_109;
x_42 = x_108;
x_43 = x_107;
x_44 = x_106;
x_45 = x_136;
goto block_47;
}
}
}
else
{
lean_object* x_138; uint8_t x_139; uint8_t x_140; lean_object* x_141; uint8_t x_142; uint8_t x_143; lean_object* x_144; 
x_138 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__13));
x_139 = 0;
x_140 = 0;
x_141 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_141, 0, x_139);
x_142 = lean_unbox(x_111);
lean_ctor_set_uint8(x_141, 1, x_142);
lean_ctor_set_uint8(x_141, 2, x_140);
x_143 = lean_unbox(x_111);
lean_dec(x_111);
lean_ctor_set_uint8(x_141, 3, x_143);
lean_inc(x_109);
lean_inc_ref(x_108);
lean_inc(x_107);
lean_inc_ref(x_106);
x_144 = l_Lean_MVarId_applyConst(x_1, x_138, x_141, x_106, x_107, x_108, x_109);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_48 = x_145;
x_49 = x_106;
x_50 = x_107;
x_51 = x_108;
x_52 = x_109;
goto block_77;
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_153; 
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
x_146 = lean_ctor_get(x_144, 0);
x_153 = !lean_is_exclusive(x_144);
if (x_153 == 0)
{
x_147 = x_144;
x_148 = x_153;
goto block_152;
}
else
{
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_box(0);
x_148 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_149; 
if (x_148 == 0)
{
x_149 = x_147;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_146);
x_149 = x_151;
goto block_150;
}
block_150:
{
return x_149;
}
}
}
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_161; 
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_1);
x_154 = lean_ctor_get(x_110, 0);
x_161 = !lean_is_exclusive(x_110);
if (x_161 == 0)
{
x_155 = x_110;
x_156 = x_161;
goto block_160;
}
else
{
lean_inc(x_154);
lean_dec(x_110);
x_155 = lean_box(0);
x_156 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_157; 
if (x_156 == 0)
{
x_157 = x_155;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_154);
x_157 = x_159;
goto block_158;
}
block_158:
{
return x_157;
}
}
}
}
}
}
else
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; uint8_t x_302; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_295 = lean_ctor_get(x_102, 0);
x_302 = !lean_is_exclusive(x_102);
if (x_302 == 0)
{
x_296 = x_102;
x_297 = x_302;
goto block_301;
}
else
{
lean_inc(x_295);
lean_dec(x_102);
x_296 = lean_box(0);
x_297 = x_302;
goto block_301;
}
block_301:
{
lean_object* x_298; 
if (x_297 == 0)
{
x_298 = x_296;
goto block_299;
}
else
{
lean_object* x_300; 
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_295);
x_298 = x_300;
goto block_299;
}
block_299:
{
return x_298;
}
}
}
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_310; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_303 = lean_ctor_get(x_100, 0);
x_310 = !lean_is_exclusive(x_100);
if (x_310 == 0)
{
x_304 = x_100;
x_305 = x_310;
goto block_309;
}
else
{
lean_inc(x_303);
lean_dec(x_100);
x_304 = lean_box(0);
x_305 = x_310;
goto block_309;
}
block_309:
{
lean_object* x_306; 
if (x_305 == 0)
{
x_306 = x_304;
goto block_307;
}
else
{
lean_object* x_308; 
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_303);
x_306 = x_308;
goto block_307;
}
block_307:
{
return x_306;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_39:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__2));
x_16 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__3));
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_17 = l_Lean_MVarId_applyConst(x_1, x_15, x_16, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_30; 
x_18 = lean_ctor_get(x_17, 0);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
x_19 = x_17;
x_20 = x_30;
goto block_29;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_30;
goto block_29;
}
block_29:
{
if (lean_obj_tag(x_18) == 0)
{
lean_del_object(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
goto block_10;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 1);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec_ref(x_18);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_23);
x_24 = x_19;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_18);
lean_del_object(x_19);
x_27 = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__7, &l_Lean_MVarId_falseOrByContra___closed__7_once, _init_l_Lean_MVarId_falseOrByContra___closed__7);
x_28 = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(x_27, x_11, x_12, x_13, x_14);
return x_28;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_31 = lean_ctor_get(x_17, 0);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
x_32 = x_17;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
block_47:
{
if (x_45 == 0)
{
lean_dec_ref(x_40);
x_11 = x_44;
x_12 = x_43;
x_13 = x_42;
x_14 = x_41;
goto block_39;
}
else
{
lean_object* x_46; 
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_1);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_40);
return x_46;
}
}
block_77:
{
if (lean_obj_tag(x_48) == 0)
{
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
goto block_10;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_48, 1);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec_ref(x_48);
x_55 = 0;
x_56 = l_Lean_Meta_intro1Core(x_54, x_55, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_66; 
x_57 = lean_ctor_get(x_56, 0);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
x_58 = x_56;
x_59 = x_66;
goto block_65;
}
else
{
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
if (x_59 == 0)
{
lean_ctor_set(x_58, 0, x_61);
x_62 = x_58;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_61);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
x_67 = lean_ctor_get(x_56, 0);
x_74 = !lean_is_exclusive(x_56);
if (x_74 == 0)
{
x_68 = x_56;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_48);
x_75 = lean_obj_once(&l_Lean_MVarId_falseOrByContra___closed__8, &l_Lean_MVarId_falseOrByContra___closed__8_once, _init_l_Lean_MVarId_falseOrByContra___closed__8);
x_76 = l_panic___at___00Lean_MVarId_falseOrByContra_spec__0(x_75, x_49, x_50, x_51, x_52);
return x_76;
}
}
}
block_99:
{
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_79);
x_86 = ((lean_object*)(l_Lean_MVarId_falseOrByContra___closed__9));
x_87 = l_Lean_Name_mkStr2(x_86, x_83);
lean_inc(x_80);
lean_inc_ref(x_81);
lean_inc(x_82);
lean_inc_ref(x_84);
x_88 = l_Lean_MVarId_applyConst(x_1, x_87, x_78, x_84, x_82, x_81, x_80);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_48 = x_89;
x_49 = x_84;
x_50 = x_82;
x_51 = x_81;
x_52 = x_80;
goto block_77;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec_ref(x_84);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
x_90 = lean_ctor_get(x_88, 0);
x_97 = !lean_is_exclusive(x_88);
if (x_97 == 0)
{
x_91 = x_88;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
else
{
lean_object* x_98; 
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_78);
lean_dec(x_1);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_79);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_falseOrByContra___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_falseOrByContra(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = l_Lean_MVarId_falseOrByContra(x_11, x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_17, x_2, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_19, x_2, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_21 = lean_ctor_get(x_13, 0);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
x_22 = x_13;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_29 = lean_ctor_get(x_10, 0);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
x_30 = x_10;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_elabFalseOrByContra___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_MVarId_elabFalseOrByContra_spec__0___redArg();
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__5));
x_15 = l_Lean_Elab_Tactic_withMainContext___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_elabFalseOrByContra(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___closed__4));
x_4 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
x_5 = lean_alloc_closure((void*)(l_Lean_MVarId_elabFalseOrByContra___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1___closed__2));
x_3 = ((lean_object*)(l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3();
return x_2;
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
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_MVarId_elabFalseOrByContra___regBuiltin_Lean_MVarId_elabFalseOrByContra_declRange__3()
;
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
res = initialize_Lean_Elab_Tactic_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
}
#ifdef __cplusplus
}
#endif
