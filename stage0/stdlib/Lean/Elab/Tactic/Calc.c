// Lean compiler output
// Module: Lean.Elab.Tactic.Calc
// Imports: public import Lean.Elab.Calc public import Lean.Elab.Tactic.ElabTerm
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkCalcStepViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_runTermElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pushGoals___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Elab.Tactic.Calc"};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Elab.Tactic.evalCalc"};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalCalc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalCalc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "calcTactic"};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalCalc___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalCalc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 188, 49, 237, 47, 139, 25, 127)}};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalCalc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "calcSteps"};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalCalc___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalCalc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(115, 10, 254, 10, 206, 238, 242, 161)}};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_evalCalc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "calc"};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalCalc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__5_value),LEAN_SCALAR_PTR_LITERAL(106, 115, 195, 202, 19, 184, 143, 94)}};
static const lean_object* l_Lean_Elab_Tactic_evalCalc___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalCalc"};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalCalc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(42, 16, 105, 192, 5, 134, 77, 195)}};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Elaborator for the `calc` tactic mode variant. "};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(15) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(34) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1_value),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(15) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(15) << 1) | 1)),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4_value),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0(void){
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(lean_object* v_e_31_, lean_object* v___y_32_){
_start:
{
uint8_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = l_Lean_Expr_hasMVar(v_e_31_);
v___x_35_ = lean_bool_not(v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v_mctx_37_; lean_object* v___x_38_; lean_object* v_fst_39_; lean_object* v_snd_40_; lean_object* v___x_41_; lean_object* v_cache_42_; lean_object* v_zetaDeltaFVarIds_43_; lean_object* v_postponed_44_; lean_object* v_diag_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_54_; 
v___x_36_ = lean_st_ref_get(v___y_32_);
v_mctx_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc_ref(v_mctx_37_);
lean_dec(v___x_36_);
v___x_38_ = l_Lean_instantiateMVarsCore(v_mctx_37_, v_e_31_);
v_fst_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_fst_39_);
v_snd_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_snd_40_);
lean_dec_ref(v___x_38_);
v___x_41_ = lean_st_ref_take(v___y_32_);
v_cache_42_ = lean_ctor_get(v___x_41_, 1);
v_zetaDeltaFVarIds_43_ = lean_ctor_get(v___x_41_, 2);
v_postponed_44_ = lean_ctor_get(v___x_41_, 3);
v_diag_45_ = lean_ctor_get(v___x_41_, 4);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_54_ == 0)
{
lean_object* v_unused_55_; 
v_unused_55_ = lean_ctor_get(v___x_41_, 0);
lean_dec(v_unused_55_);
v___x_47_ = v___x_41_;
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_diag_45_);
lean_inc(v_postponed_44_);
lean_inc(v_zetaDeltaFVarIds_43_);
lean_inc(v_cache_42_);
lean_dec(v___x_41_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v_snd_40_);
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_snd_40_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_cache_42_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v_zetaDeltaFVarIds_43_);
lean_ctor_set(v_reuseFailAlloc_53_, 3, v_postponed_44_);
lean_ctor_set(v_reuseFailAlloc_53_, 4, v_diag_45_);
v___x_50_ = v_reuseFailAlloc_53_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_st_ref_set(v___y_32_, v___x_50_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v_fst_39_);
return v___x_52_;
}
}
}
else
{
lean_object* v___x_56_; 
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v_e_31_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg___boxed(lean_object* v_e_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_e_57_, v___y_58_);
lean_dec(v___y_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(lean_object* v_e_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_e_61_, v___y_67_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___boxed(lean_object* v_e_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(v_e_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
return v_res_82_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(lean_object* v_msg_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_11010__overap_93_; lean_object* v___x_94_; 
v___x_92_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0, &l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0);
v___x_11010__overap_93_ = lean_panic_fn_borrowed(v___x_92_, v_msg_84_);
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
v___x_94_ = lean_apply_7(v___x_11010__overap_93_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, lean_box(0));
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___boxed(lean_object* v_msg_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(v_msg_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__0(lean_object* v_a_104_, lean_object* v_x_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_104_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__0___boxed(lean_object* v_a_114_, lean_object* v_x_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Elab_Tactic_evalCalc___lam__0(v_a_114_, v_x_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v_x_115_);
lean_dec_ref(v_a_114_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__1(lean_object* v_a_124_, lean_object* v_x_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_124_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__1___boxed(lean_object* v_a_134_, lean_object* v_x_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Elab_Tactic_evalCalc___lam__1(v_a_134_, v_x_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v_x_135_);
lean_dec_ref(v_a_134_);
return v_res_143_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_148_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3));
v___x_149_ = lean_unsigned_to_nat(65u);
v___x_150_ = lean_unsigned_to_nat(32u);
v___x_151_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2));
v___x_152_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1));
v___x_153_ = l_mkPanicMessageWithDecl(v___x_152_, v___x_151_, v___x_150_, v___x_149_, v___x_148_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2(lean_object* v_a_154_, lean_object* v___x_155_, lean_object* v___f_156_, lean_object* v___f_157_, lean_object* v___x_158_, lean_object* v_tag_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Elab_Term_elabCalcSteps(v_a_154_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_284_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_284_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_284_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_284_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_180_; lean_object* v___y_184_; uint8_t v___y_185_; lean_object* v_a_190_; lean_object* v___x_193_; 
v_fst_172_ = lean_ctor_get(v_a_168_, 0);
lean_inc(v_fst_172_);
v_snd_173_ = lean_ctor_get(v_a_168_, 1);
lean_inc_n(v_snd_173_, 2);
lean_dec(v_a_168_);
lean_inc_ref(v___x_155_);
v___x_193_ = l_Lean_Meta_isExprDefEq(v_snd_173_, v___x_155_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_275_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_275_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_275_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_275_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
uint8_t v___x_198_; 
v___x_198_ = lean_unbox(v_a_194_);
lean_dec(v_a_194_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_del_object(v___x_196_);
v___x_199_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_snd_173_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_199_, 1);
if (lean_obj_tag(v_a_200_) == 1)
{
lean_object* v_val_201_; lean_object* v_snd_202_; lean_object* v_fst_203_; lean_object* v_snd_204_; lean_object* v___x_205_; 
v_val_201_ = lean_ctor_get(v_a_200_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v_a_200_, 1);
v_snd_202_ = lean_ctor_get(v_val_201_, 1);
lean_inc(v_snd_202_);
lean_dec(v_val_201_);
v_fst_203_ = lean_ctor_get(v_snd_202_, 0);
lean_inc(v_fst_203_);
v_snd_204_ = lean_ctor_get(v_snd_202_, 1);
lean_inc(v_snd_204_);
lean_dec(v_snd_202_);
v___x_205_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_155_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
if (lean_obj_tag(v_a_206_) == 1)
{
lean_object* v_val_207_; lean_object* v_snd_208_; lean_object* v_fst_209_; lean_object* v_fst_210_; lean_object* v_snd_211_; lean_object* v___y_213_; lean_object* v___x_246_; 
v_val_207_ = lean_ctor_get(v_a_206_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v_a_206_, 1);
v_snd_208_ = lean_ctor_get(v_val_207_, 1);
lean_inc(v_snd_208_);
v_fst_209_ = lean_ctor_get(v_val_207_, 0);
lean_inc(v_fst_209_);
lean_dec(v_val_207_);
v_fst_210_ = lean_ctor_get(v_snd_208_, 0);
lean_inc(v_fst_210_);
v_snd_211_ = lean_ctor_get(v_snd_208_, 1);
lean_inc(v_snd_211_);
lean_dec(v_snd_208_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
lean_inc(v_snd_204_);
v___x_246_ = lean_infer_type(v_snd_204_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_248_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 1);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
lean_inc(v_fst_210_);
v___x_248_ = lean_infer_type(v_fst_210_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v___x_250_ = l_Lean_Meta_isExprDefEq(v_fst_203_, v_fst_210_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; uint8_t v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
v___x_252_ = lean_unbox(v_a_251_);
lean_dec(v_a_251_);
if (v___x_252_ == 0)
{
lean_dec(v_a_249_);
lean_dec(v_a_247_);
v___y_213_ = v___x_250_;
goto v___jp_212_;
}
else
{
lean_object* v___x_253_; 
lean_dec_ref_known(v___x_250_, 1);
v___x_253_ = l_Lean_Meta_isExprDefEq(v_a_247_, v_a_249_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
v___y_213_ = v___x_253_;
goto v___jp_212_;
}
}
else
{
lean_dec(v_a_249_);
lean_dec(v_a_247_);
v___y_213_ = v___x_250_;
goto v___jp_212_;
}
}
else
{
lean_dec(v_a_247_);
lean_dec(v_snd_211_);
lean_dec(v_fst_210_);
lean_dec(v_fst_209_);
lean_dec(v_snd_204_);
lean_dec(v_fst_203_);
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
lean_del_object(v___x_170_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
return v___x_248_;
}
}
else
{
lean_dec(v_snd_211_);
lean_dec(v_fst_210_);
lean_dec(v_fst_209_);
lean_dec(v_snd_204_);
lean_dec(v_fst_203_);
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
lean_del_object(v___x_170_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
return v___x_246_;
}
v___jp_212_:
{
if (lean_obj_tag(v___y_213_) == 0)
{
lean_object* v_a_214_; uint8_t v___x_215_; 
v_a_214_ = lean_ctor_get(v___y_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___y_213_, 1);
v___x_215_ = lean_unbox(v_a_214_);
lean_dec(v_a_214_);
if (v___x_215_ == 0)
{
lean_dec(v_snd_211_);
lean_dec(v_fst_209_);
lean_dec(v_snd_204_);
lean_dec(v_snd_173_);
lean_del_object(v___x_170_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
v___y_175_ = v___y_160_;
v___y_176_ = v___y_161_;
v___y_177_ = v___y_162_;
v___y_178_ = v___y_163_;
v___y_179_ = v___y_164_;
v___y_180_ = v___y_165_;
goto v___jp_174_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_216_ = l_Lean_mkAppB(v_fst_209_, v_snd_204_, v_snd_211_);
v___x_217_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0));
v___x_218_ = l_Lean_Name_mkStr2(v___x_158_, v___x_217_);
v___x_219_ = l_Lean_Name_append(v_tag_159_, v___x_218_);
lean_inc_ref(v___x_216_);
v___x_220_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_216_, v___x_219_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
lean_inc(v_fst_172_);
v___x_222_ = l_Lean_Elab_Term_mkCalcTrans(v_fst_172_, v_snd_173_, v_a_221_, v___x_216_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v_snd_173_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v_fst_224_; lean_object* v_snd_225_; lean_object* v___x_226_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref_known(v___x_222_, 1);
v_fst_224_ = lean_ctor_get(v_a_223_, 0);
lean_inc(v_fst_224_);
v_snd_225_ = lean_ctor_get(v_a_223_, 1);
lean_inc(v_snd_225_);
lean_dec(v_a_223_);
lean_inc_ref(v___x_155_);
v___x_226_ = l_Lean_Meta_isExprDefEq(v_snd_225_, v___x_155_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_235_; 
lean_del_object(v___x_170_);
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_235_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_235_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_235_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
uint8_t v___x_231_; 
v___x_231_ = lean_unbox(v_a_227_);
lean_dec(v_a_227_);
if (v___x_231_ == 0)
{
lean_del_object(v___x_229_);
lean_dec(v_fst_224_);
v___y_175_ = v___y_160_;
v___y_176_ = v___y_161_;
v___y_177_ = v___y_162_;
v___y_178_ = v___y_163_;
v___y_179_ = v___y_164_;
v___y_180_ = v___y_165_;
goto v___jp_174_;
}
else
{
lean_object* v___x_233_; 
lean_dec(v_fst_172_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v_fst_224_);
v___x_233_ = v___x_229_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_fst_224_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; 
lean_dec(v_fst_224_);
v_a_236_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_226_, 1);
v_a_190_ = v_a_236_;
goto v___jp_189_;
}
}
else
{
lean_object* v_a_237_; 
v_a_237_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_222_, 1);
v_a_190_ = v_a_237_;
goto v___jp_189_;
}
}
else
{
lean_dec_ref(v___x_216_);
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
lean_del_object(v___x_170_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
return v___x_220_;
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_snd_211_);
lean_dec(v_fst_209_);
lean_dec(v_snd_204_);
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
lean_del_object(v___x_170_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
v_a_238_ = lean_ctor_get(v___y_213_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___y_213_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___y_213_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___y_213_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
else
{
lean_dec(v_a_206_);
lean_dec(v_snd_204_);
lean_dec(v_fst_203_);
lean_dec(v_snd_173_);
lean_del_object(v___x_170_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
v___y_175_ = v___y_160_;
v___y_176_ = v___y_161_;
v___y_177_ = v___y_162_;
v___y_178_ = v___y_163_;
v___y_179_ = v___y_164_;
v___y_180_ = v___y_165_;
goto v___jp_174_;
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec(v_snd_204_);
lean_dec(v_fst_203_);
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
lean_del_object(v___x_170_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
v_a_254_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_205_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_205_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_a_200_);
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
lean_del_object(v___x_170_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
v___x_262_ = lean_obj_once(&l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4, &l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4);
v___x_263_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(v___x_262_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v___x_263_;
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
lean_del_object(v___x_170_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
v_a_264_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_199_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_199_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v___x_273_; 
lean_dec(v_snd_173_);
lean_del_object(v___x_170_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v_fst_172_);
v___x_273_ = v___x_196_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_fst_172_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
lean_del_object(v___x_170_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
v_a_276_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_193_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_193_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
v___jp_174_:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_155_);
v___x_182_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(v___x_181_, v_fst_172_, v___f_156_, v___f_157_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v___x_182_;
}
v___jp_183_:
{
if (v___y_185_ == 0)
{
lean_dec_ref(v___y_184_);
lean_del_object(v___x_170_);
v___y_175_ = v___y_160_;
v___y_176_ = v___y_161_;
v___y_177_ = v___y_162_;
v___y_178_ = v___y_163_;
v___y_179_ = v___y_164_;
v___y_180_ = v___y_165_;
goto v___jp_174_;
}
else
{
lean_object* v___x_187_; 
lean_dec(v_fst_172_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 1);
lean_ctor_set(v___x_170_, 0, v___y_184_);
v___x_187_ = v___x_170_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___y_184_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
v___jp_189_:
{
uint8_t v___x_191_; 
v___x_191_ = l_Lean_Exception_isInterrupt(v_a_190_);
if (v___x_191_ == 0)
{
uint8_t v___x_192_; 
lean_inc_ref(v_a_190_);
v___x_192_ = l_Lean_Exception_isRuntime(v_a_190_);
v___y_184_ = v_a_190_;
v___y_185_ = v___x_192_;
goto v___jp_183_;
}
else
{
v___y_184_ = v_a_190_;
v___y_185_ = v___x_191_;
goto v___jp_183_;
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v_tag_159_);
lean_dec_ref(v___x_158_);
lean_dec_ref(v___f_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___x_155_);
v_a_285_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_167_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_167_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2___boxed(lean_object* v_a_293_, lean_object* v___x_294_, lean_object* v___f_295_, lean_object* v___f_296_, lean_object* v___x_297_, lean_object* v_tag_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Elab_Tactic_evalCalc___lam__2(v_a_293_, v___x_294_, v___f_295_, v___f_296_, v___x_297_, v_tag_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec_ref(v_a_293_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__3(lean_object* v_steps_307_, lean_object* v_target_308_, lean_object* v___x_309_, lean_object* v_tag_310_, lean_object* v___x_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_307_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v_a_324_; lean_object* v___f_325_; lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___f_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc_n(v_a_322_, 3);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_target_308_, v___y_317_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref(v___x_323_);
v___f_325_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__0___boxed), 9, 1);
lean_closure_set(v___f_325_, 0, v_a_322_);
v___f_326_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__1___boxed), 9, 1);
lean_closure_set(v___f_326_, 0, v_a_322_);
v___x_327_ = l_Lean_Expr_consumeMData(v_a_324_);
lean_dec(v_a_324_);
lean_inc(v_tag_310_);
v___f_328_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__2___boxed), 13, 6);
lean_closure_set(v___f_328_, 0, v_a_322_);
lean_closure_set(v___f_328_, 1, v___x_327_);
lean_closure_set(v___f_328_, 2, v___f_326_);
lean_closure_set(v___f_328_, 3, v___f_325_);
lean_closure_set(v___f_328_, 4, v___x_309_);
lean_closure_set(v___f_328_, 5, v_tag_310_);
v___x_329_ = 0;
v___x_330_ = lean_box(v___x_329_);
v___x_331_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___boxed), 12, 3);
lean_closure_set(v___x_331_, 0, lean_box(0));
lean_closure_set(v___x_331_, 1, v___f_328_);
lean_closure_set(v___x_331_, 2, v___x_330_);
v___x_332_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_331_, v_tag_310_, v___x_311_, v___x_329_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v_fst_334_; lean_object* v_snd_335_; lean_object* v___x_336_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref_known(v___x_332_, 1);
v_fst_334_ = lean_ctor_get(v_a_333_, 0);
lean_inc(v_fst_334_);
v_snd_335_ = lean_ctor_get(v_a_333_, 1);
lean_inc(v_snd_335_);
lean_dec(v_a_333_);
v___x_336_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_335_, v___y_313_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v___x_336_, 0);
lean_dec(v_unused_344_);
v___x_338_ = v___x_336_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_dec(v___x_336_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v_fst_334_);
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_fst_334_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_fst_334_);
v_a_345_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_336_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_336_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_a_353_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_332_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_332_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec(v___x_311_);
lean_dec(v_tag_310_);
lean_dec_ref(v___x_309_);
lean_dec_ref(v_target_308_);
v_a_361_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_321_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_321_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__3___boxed(lean_object* v_steps_369_, lean_object* v_target_370_, lean_object* v___x_371_, lean_object* v_tag_372_, lean_object* v___x_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Elab_Tactic_evalCalc___lam__3(v_steps_369_, v_target_370_, v___x_371_, v_tag_372_, v___x_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__4(lean_object* v_a_384_, lean_object* v_trees_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
lean_inc(v___y_393_);
lean_inc_ref(v___y_392_);
lean_inc(v___y_391_);
lean_inc_ref(v___y_390_);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
v___x_395_ = lean_apply_9(v_a_384_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, lean_box(0));
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_400_, 0, v_a_396_);
lean_ctor_set(v___x_400_, 1, v_trees_385_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_trees_385_);
v_a_405_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_395_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_395_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__4___boxed(lean_object* v_a_413_, lean_object* v_trees_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Elab_Tactic_evalCalc___lam__4(v_a_413_, v_trees_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(lean_object* v___y_425_, lean_object* v_mkInfoTree_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v_a_434_, lean_object* v_a_x3f_435_){
_start:
{
lean_object* v___x_437_; lean_object* v_infoState_438_; lean_object* v_trees_439_; lean_object* v___x_440_; 
v___x_437_ = lean_st_ref_get(v___y_425_);
v_infoState_438_ = lean_ctor_get(v___x_437_, 7);
lean_inc_ref(v_infoState_438_);
lean_dec(v___x_437_);
v_trees_439_ = lean_ctor_get(v_infoState_438_, 2);
lean_inc_ref(v_trees_439_);
lean_dec_ref(v_infoState_438_);
lean_inc(v___y_425_);
lean_inc_ref(v___y_433_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
v___x_440_ = lean_apply_10(v_mkInfoTree_426_, v_trees_439_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_425_, lean_box(0));
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_479_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_479_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_479_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_479_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v_infoState_446_; lean_object* v_env_447_; lean_object* v_nextMacroScope_448_; lean_object* v_ngen_449_; lean_object* v_auxDeclNGen_450_; lean_object* v_traceState_451_; lean_object* v_cache_452_; lean_object* v_messages_453_; lean_object* v_snapshotTasks_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_478_; 
v___x_445_ = lean_st_ref_take(v___y_425_);
v_infoState_446_ = lean_ctor_get(v___x_445_, 7);
v_env_447_ = lean_ctor_get(v___x_445_, 0);
v_nextMacroScope_448_ = lean_ctor_get(v___x_445_, 1);
v_ngen_449_ = lean_ctor_get(v___x_445_, 2);
v_auxDeclNGen_450_ = lean_ctor_get(v___x_445_, 3);
v_traceState_451_ = lean_ctor_get(v___x_445_, 4);
v_cache_452_ = lean_ctor_get(v___x_445_, 5);
v_messages_453_ = lean_ctor_get(v___x_445_, 6);
v_snapshotTasks_454_ = lean_ctor_get(v___x_445_, 8);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_478_ == 0)
{
v___x_456_ = v___x_445_;
v_isShared_457_ = v_isSharedCheck_478_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_snapshotTasks_454_);
lean_inc(v_infoState_446_);
lean_inc(v_messages_453_);
lean_inc(v_cache_452_);
lean_inc(v_traceState_451_);
lean_inc(v_auxDeclNGen_450_);
lean_inc(v_ngen_449_);
lean_inc(v_nextMacroScope_448_);
lean_inc(v_env_447_);
lean_dec(v___x_445_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_478_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
uint8_t v_enabled_458_; lean_object* v_assignment_459_; lean_object* v_lazyAssignment_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_476_; 
v_enabled_458_ = lean_ctor_get_uint8(v_infoState_446_, sizeof(void*)*3);
v_assignment_459_ = lean_ctor_get(v_infoState_446_, 0);
v_lazyAssignment_460_ = lean_ctor_get(v_infoState_446_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_infoState_446_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; 
v_unused_477_ = lean_ctor_get(v_infoState_446_, 2);
lean_dec(v_unused_477_);
v___x_462_ = v_infoState_446_;
v_isShared_463_ = v_isSharedCheck_476_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_lazyAssignment_460_);
lean_inc(v_assignment_459_);
lean_dec(v_infoState_446_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_476_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = l_Lean_PersistentArray_push___redArg(v_a_434_, v_a_441_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 2, v___x_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_assignment_459_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_lazyAssignment_460_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v___x_464_);
lean_ctor_set_uint8(v_reuseFailAlloc_475_, sizeof(void*)*3, v_enabled_458_);
v___x_466_ = v_reuseFailAlloc_475_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 7, v___x_466_);
v___x_468_ = v___x_456_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_env_447_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_nextMacroScope_448_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_ngen_449_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_auxDeclNGen_450_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_traceState_451_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_cache_452_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_messages_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_snapshotTasks_454_);
v___x_468_ = v_reuseFailAlloc_474_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = lean_st_ref_set(v___y_425_, v___x_468_);
v___x_470_ = lean_box(0);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_470_);
v___x_472_ = v___x_443_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v_a_434_);
v_a_480_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_440_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_440_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0___boxed(lean_object* v___y_488_, lean_object* v_mkInfoTree_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v_a_497_, lean_object* v_a_x3f_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_488_, v_mkInfoTree_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v_a_497_, v_a_x3f_498_);
lean_dec(v_a_x3f_498_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_488_);
return v_res_500_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_unsigned_to_nat(32u);
v___x_502_ = lean_mk_empty_array_with_capacity(v___x_501_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_504_ = ((size_t)5ULL);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_unsigned_to_nat(32u);
v___x_507_ = lean_mk_empty_array_with_capacity(v___x_506_);
v___x_508_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0);
v___x_509_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
lean_ctor_set(v___x_509_, 2, v___x_505_);
lean_ctor_set(v___x_509_, 3, v___x_505_);
lean_ctor_set_usize(v___x_509_, 4, v___x_504_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v_infoState_513_; lean_object* v_trees_514_; lean_object* v___x_515_; lean_object* v_infoState_516_; lean_object* v_env_517_; lean_object* v_nextMacroScope_518_; lean_object* v_ngen_519_; lean_object* v_auxDeclNGen_520_; lean_object* v_traceState_521_; lean_object* v_cache_522_; lean_object* v_messages_523_; lean_object* v_snapshotTasks_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_545_; 
v___x_512_ = lean_st_ref_get(v___y_510_);
v_infoState_513_ = lean_ctor_get(v___x_512_, 7);
lean_inc_ref(v_infoState_513_);
lean_dec(v___x_512_);
v_trees_514_ = lean_ctor_get(v_infoState_513_, 2);
lean_inc_ref(v_trees_514_);
lean_dec_ref(v_infoState_513_);
v___x_515_ = lean_st_ref_take(v___y_510_);
v_infoState_516_ = lean_ctor_get(v___x_515_, 7);
v_env_517_ = lean_ctor_get(v___x_515_, 0);
v_nextMacroScope_518_ = lean_ctor_get(v___x_515_, 1);
v_ngen_519_ = lean_ctor_get(v___x_515_, 2);
v_auxDeclNGen_520_ = lean_ctor_get(v___x_515_, 3);
v_traceState_521_ = lean_ctor_get(v___x_515_, 4);
v_cache_522_ = lean_ctor_get(v___x_515_, 5);
v_messages_523_ = lean_ctor_get(v___x_515_, 6);
v_snapshotTasks_524_ = lean_ctor_get(v___x_515_, 8);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_545_ == 0)
{
v___x_526_ = v___x_515_;
v_isShared_527_ = v_isSharedCheck_545_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_snapshotTasks_524_);
lean_inc(v_infoState_516_);
lean_inc(v_messages_523_);
lean_inc(v_cache_522_);
lean_inc(v_traceState_521_);
lean_inc(v_auxDeclNGen_520_);
lean_inc(v_ngen_519_);
lean_inc(v_nextMacroScope_518_);
lean_inc(v_env_517_);
lean_dec(v___x_515_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_545_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
uint8_t v_enabled_528_; lean_object* v_assignment_529_; lean_object* v_lazyAssignment_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_543_; 
v_enabled_528_ = lean_ctor_get_uint8(v_infoState_516_, sizeof(void*)*3);
v_assignment_529_ = lean_ctor_get(v_infoState_516_, 0);
v_lazyAssignment_530_ = lean_ctor_get(v_infoState_516_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_infoState_516_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v_infoState_516_, 2);
lean_dec(v_unused_544_);
v___x_532_ = v_infoState_516_;
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_lazyAssignment_530_);
lean_inc(v_assignment_529_);
lean_dec(v_infoState_516_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 2, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_assignment_529_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_lazyAssignment_530_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v___x_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_542_, sizeof(void*)*3, v_enabled_528_);
v___x_536_ = v_reuseFailAlloc_542_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 7, v___x_536_);
v___x_538_ = v___x_526_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_env_517_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_nextMacroScope_518_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_ngen_519_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_auxDeclNGen_520_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v_traceState_521_);
lean_ctor_set(v_reuseFailAlloc_541_, 5, v_cache_522_);
lean_ctor_set(v_reuseFailAlloc_541_, 6, v_messages_523_);
lean_ctor_set(v_reuseFailAlloc_541_, 7, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_541_, 8, v_snapshotTasks_524_);
v___x_538_ = v_reuseFailAlloc_541_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_st_ref_set(v___y_510_, v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_trees_514_);
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___boxed(lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_546_);
lean_dec(v___y_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(lean_object* v_x_549_, lean_object* v_mkInfoTree_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; lean_object* v_infoState_561_; uint8_t v_enabled_562_; 
v___x_560_ = lean_st_ref_get(v___y_558_);
v_infoState_561_ = lean_ctor_get(v___x_560_, 7);
lean_inc_ref(v_infoState_561_);
lean_dec(v___x_560_);
v_enabled_562_ = lean_ctor_get_uint8(v_infoState_561_, sizeof(void*)*3);
lean_dec_ref(v_infoState_561_);
if (v_enabled_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec_ref(v_mkInfoTree_550_);
lean_inc(v___y_558_);
lean_inc_ref(v___y_557_);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
v___x_563_ = lean_apply_9(v_x_549_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, lean_box(0));
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v_a_565_; lean_object* v_r_566_; 
v___x_564_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_558_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref(v___x_564_);
lean_inc(v___y_558_);
lean_inc_ref(v___y_557_);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
v_r_566_ = lean_apply_9(v_x_549_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, lean_box(0));
if (lean_obj_tag(v_r_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_591_; 
v_a_567_ = lean_ctor_get(v_r_566_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_r_566_);
if (v_isSharedCheck_591_ == 0)
{
v___x_569_ = v_r_566_;
v_isShared_570_ = v_isSharedCheck_591_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v_r_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_591_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
lean_inc(v_a_567_);
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 1);
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_590_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_558_, v_mkInfoTree_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v_a_565_, v___x_572_);
lean_dec_ref(v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v___x_573_, 0);
lean_dec(v_unused_581_);
v___x_575_ = v___x_573_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_dec(v___x_573_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_a_567_);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_567_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec(v_a_567_);
v_a_582_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_573_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_573_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_a_592_ = lean_ctor_get(v_r_566_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v_r_566_, 1);
v___x_593_ = lean_box(0);
v___x_594_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_558_, v_mkInfoTree_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v_a_565_, v___x_593_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_594_, 0);
lean_dec(v_unused_602_);
v___x_596_ = v___x_594_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_dec(v___x_594_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 1);
lean_ctor_set(v___x_596_, 0, v_a_592_);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_592_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_a_592_);
v_a_603_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_594_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_594_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___boxed(lean_object* v_x_611_, lean_object* v_mkInfoTree_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v_x_611_, v_mkInfoTree_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__5(lean_object* v_steps_623_, lean_object* v___x_624_, lean_object* v___x_625_, lean_object* v_target_626_, lean_object* v_tag_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; 
lean_inc(v_steps_623_);
v___x_637_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_steps_623_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___x_641_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___f_639_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__3___boxed), 14, 5);
lean_closure_set(v___f_639_, 0, v_steps_623_);
lean_closure_set(v___f_639_, 1, v_target_626_);
lean_closure_set(v___f_639_, 2, v___x_624_);
lean_closure_set(v___f_639_, 3, v_tag_627_);
lean_closure_set(v___f_639_, 4, v___x_625_);
v___f_640_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__4___boxed), 11, 1);
lean_closure_set(v___f_640_, 0, v_a_638_);
v___x_641_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v___f_639_, v___f_640_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
return v___x_641_;
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v_tag_627_);
lean_dec_ref(v_target_626_);
lean_dec(v___x_625_);
lean_dec_ref(v___x_624_);
lean_dec(v_steps_623_);
v_a_642_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_637_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_637_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__5___boxed(lean_object* v_steps_650_, lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v_target_653_, lean_object* v_tag_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Elab_Tactic_evalCalc___lam__5(v_steps_650_, v___x_651_, v___x_652_, v_target_653_, v_tag_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc(lean_object* v_x_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__2));
lean_inc(v_x_677_);
v___x_688_ = l_Lean_Syntax_isOfKind(v_x_677_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v_x_677_);
v___x_689_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v_steps_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_690_ = lean_unsigned_to_nat(1u);
v_steps_691_ = l_Lean_Syntax_getArg(v_x_677_, v___x_690_);
v___x_692_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__4));
lean_inc(v_steps_691_);
v___x_693_ = l_Lean_Syntax_isOfKind(v_steps_691_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
lean_dec(v_steps_691_);
lean_dec(v_x_677_);
v___x_694_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v___x_694_;
}
else
{
lean_object* v_fileName_695_; lean_object* v_fileMap_696_; lean_object* v_options_697_; lean_object* v_currRecDepth_698_; lean_object* v_maxRecDepth_699_; lean_object* v_ref_700_; lean_object* v_currNamespace_701_; lean_object* v_openDecls_702_; lean_object* v_initHeartbeats_703_; lean_object* v_maxHeartbeats_704_; lean_object* v_quotContext_705_; lean_object* v_currMacroScope_706_; uint8_t v_diag_707_; lean_object* v_cancelTk_x3f_708_; uint8_t v_suppressElabErrors_709_; lean_object* v_inheritedTraceOptions_710_; lean_object* v___x_711_; lean_object* v_tk_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___f_715_; uint8_t v___x_716_; lean_object* v_ref_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_fileName_695_ = lean_ctor_get(v_a_684_, 0);
v_fileMap_696_ = lean_ctor_get(v_a_684_, 1);
v_options_697_ = lean_ctor_get(v_a_684_, 2);
v_currRecDepth_698_ = lean_ctor_get(v_a_684_, 3);
v_maxRecDepth_699_ = lean_ctor_get(v_a_684_, 4);
v_ref_700_ = lean_ctor_get(v_a_684_, 5);
v_currNamespace_701_ = lean_ctor_get(v_a_684_, 6);
v_openDecls_702_ = lean_ctor_get(v_a_684_, 7);
v_initHeartbeats_703_ = lean_ctor_get(v_a_684_, 8);
v_maxHeartbeats_704_ = lean_ctor_get(v_a_684_, 9);
v_quotContext_705_ = lean_ctor_get(v_a_684_, 10);
v_currMacroScope_706_ = lean_ctor_get(v_a_684_, 11);
v_diag_707_ = lean_ctor_get_uint8(v_a_684_, sizeof(void*)*14);
v_cancelTk_x3f_708_ = lean_ctor_get(v_a_684_, 12);
v_suppressElabErrors_709_ = lean_ctor_get_uint8(v_a_684_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_710_ = lean_ctor_get(v_a_684_, 13);
v___x_711_ = lean_unsigned_to_nat(0u);
v_tk_712_ = l_Lean_Syntax_getArg(v_x_677_, v___x_711_);
lean_dec(v_x_677_);
v___x_713_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__5));
v___x_714_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__6));
v___f_715_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__5___boxed), 14, 3);
lean_closure_set(v___f_715_, 0, v_steps_691_);
lean_closure_set(v___f_715_, 1, v___x_713_);
lean_closure_set(v___f_715_, 2, v___x_714_);
v___x_716_ = 0;
v_ref_717_ = l_Lean_replaceRef(v_tk_712_, v_ref_700_);
lean_dec(v_tk_712_);
lean_inc_ref(v_inheritedTraceOptions_710_);
lean_inc(v_cancelTk_x3f_708_);
lean_inc(v_currMacroScope_706_);
lean_inc(v_quotContext_705_);
lean_inc(v_maxHeartbeats_704_);
lean_inc(v_initHeartbeats_703_);
lean_inc(v_openDecls_702_);
lean_inc(v_currNamespace_701_);
lean_inc(v_maxRecDepth_699_);
lean_inc(v_currRecDepth_698_);
lean_inc_ref(v_options_697_);
lean_inc_ref(v_fileMap_696_);
lean_inc_ref(v_fileName_695_);
v___x_718_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_718_, 0, v_fileName_695_);
lean_ctor_set(v___x_718_, 1, v_fileMap_696_);
lean_ctor_set(v___x_718_, 2, v_options_697_);
lean_ctor_set(v___x_718_, 3, v_currRecDepth_698_);
lean_ctor_set(v___x_718_, 4, v_maxRecDepth_699_);
lean_ctor_set(v___x_718_, 5, v_ref_717_);
lean_ctor_set(v___x_718_, 6, v_currNamespace_701_);
lean_ctor_set(v___x_718_, 7, v_openDecls_702_);
lean_ctor_set(v___x_718_, 8, v_initHeartbeats_703_);
lean_ctor_set(v___x_718_, 9, v_maxHeartbeats_704_);
lean_ctor_set(v___x_718_, 10, v_quotContext_705_);
lean_ctor_set(v___x_718_, 11, v_currMacroScope_706_);
lean_ctor_set(v___x_718_, 12, v_cancelTk_x3f_708_);
lean_ctor_set(v___x_718_, 13, v_inheritedTraceOptions_710_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*14, v_diag_707_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*14 + 1, v_suppressElabErrors_709_);
v___x_719_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v___x_714_, v___f_715_, v___x_716_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v___x_718_, v_a_685_);
lean_dec_ref_known(v___x_718_, 14);
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___boxed(lean_object* v_x_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Elab_Tactic_evalCalc(v_x_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___boxed(lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(lean_object* v_00_u03b1_751_, lean_object* v_x_752_, lean_object* v_mkInfoTree_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v_x_752_, v_mkInfoTree_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___boxed(lean_object* v_00_u03b1_764_, lean_object* v_x_765_, lean_object* v_mkInfoTree_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(v_00_u03b1_764_, v_x_765_, v_mkInfoTree_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1(){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_786_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_787_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__2));
v___x_788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_789_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___boxed), 10, 0);
v___x_790_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_786_, v___x_787_, v___x_788_, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___boxed(lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3(){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0));
v___x_797_ = l_Lean_addBuiltinDocString(v___x_795_, v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___boxed(lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5(){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6));
v___x_828_ = l_Lean_addBuiltinDeclarationRanges(v___x_826_, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___boxed(lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
return v_res_830_;
}
}
lean_object* runtime_initialize_Lean_Elab_Calc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Calc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Calc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Calc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Calc(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Calc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Calc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Calc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Calc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Calc(builtin);
}
#ifdef __cplusplus
}
#endif
