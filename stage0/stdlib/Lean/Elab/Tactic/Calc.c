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
uint8_t v___x_34_; 
v___x_34_ = l_Lean_Expr_hasMVar(v_e_31_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v_e_31_);
return v___x_35_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg___boxed(lean_object* v_e_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_e_56_, v___y_57_);
lean_dec(v___y_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(lean_object* v_e_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_e_60_, v___y_66_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___boxed(lean_object* v_e_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(v_e_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_81_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(lean_object* v_msg_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_11010__overap_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0, &l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0);
v___x_11010__overap_92_ = lean_panic_fn_borrowed(v___x_91_, v_msg_83_);
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
v___x_93_ = lean_apply_7(v___x_11010__overap_92_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, lean_box(0));
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___boxed(lean_object* v_msg_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(v_msg_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__0(lean_object* v_a_103_, lean_object* v_x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_103_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__0___boxed(lean_object* v_a_113_, lean_object* v_x_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Elab_Tactic_evalCalc___lam__0(v_a_113_, v_x_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v_x_114_);
lean_dec_ref(v_a_113_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__1(lean_object* v_a_123_, lean_object* v_x_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_123_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__1___boxed(lean_object* v_a_133_, lean_object* v_x_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Elab_Tactic_evalCalc___lam__1(v_a_133_, v_x_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v_x_134_);
lean_dec_ref(v_a_133_);
return v_res_142_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_147_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3));
v___x_148_ = lean_unsigned_to_nat(65u);
v___x_149_ = lean_unsigned_to_nat(32u);
v___x_150_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2));
v___x_151_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1));
v___x_152_ = l_mkPanicMessageWithDecl(v___x_151_, v___x_150_, v___x_149_, v___x_148_, v___x_147_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2(lean_object* v_a_153_, lean_object* v___x_154_, lean_object* v___f_155_, lean_object* v___f_156_, lean_object* v___x_157_, lean_object* v_tag_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Elab_Term_elabCalcSteps(v_a_153_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_283_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_283_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_283_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_283_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v_fst_171_; lean_object* v_snd_172_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_183_; uint8_t v___y_184_; lean_object* v_a_189_; lean_object* v___x_192_; 
v_fst_171_ = lean_ctor_get(v_a_167_, 0);
lean_inc(v_fst_171_);
v_snd_172_ = lean_ctor_get(v_a_167_, 1);
lean_inc_n(v_snd_172_, 2);
lean_dec(v_a_167_);
lean_inc_ref(v___x_154_);
v___x_192_ = l_Lean_Meta_isExprDefEq(v_snd_172_, v___x_154_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_274_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_274_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_274_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_274_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
uint8_t v___x_197_; 
v___x_197_ = lean_unbox(v_a_193_);
lean_dec(v_a_193_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_del_object(v___x_195_);
v___x_198_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_snd_172_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref(v___x_198_);
if (lean_obj_tag(v_a_199_) == 1)
{
lean_object* v_val_200_; lean_object* v_snd_201_; lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_204_; 
v_val_200_ = lean_ctor_get(v_a_199_, 0);
lean_inc(v_val_200_);
lean_dec_ref(v_a_199_);
v_snd_201_ = lean_ctor_get(v_val_200_, 1);
lean_inc(v_snd_201_);
lean_dec(v_val_200_);
v_fst_202_ = lean_ctor_get(v_snd_201_, 0);
lean_inc(v_fst_202_);
v_snd_203_ = lean_ctor_get(v_snd_201_, 1);
lean_inc(v_snd_203_);
lean_dec(v_snd_201_);
v___x_204_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_154_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref(v___x_204_);
if (lean_obj_tag(v_a_205_) == 1)
{
lean_object* v_val_206_; lean_object* v_snd_207_; lean_object* v_fst_208_; lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___y_212_; lean_object* v___x_245_; 
v_val_206_ = lean_ctor_get(v_a_205_, 0);
lean_inc(v_val_206_);
lean_dec_ref(v_a_205_);
v_snd_207_ = lean_ctor_get(v_val_206_, 1);
lean_inc(v_snd_207_);
v_fst_208_ = lean_ctor_get(v_val_206_, 0);
lean_inc(v_fst_208_);
lean_dec(v_val_206_);
v_fst_209_ = lean_ctor_get(v_snd_207_, 0);
lean_inc(v_fst_209_);
v_snd_210_ = lean_ctor_get(v_snd_207_, 1);
lean_inc(v_snd_210_);
lean_dec(v_snd_207_);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v___y_162_);
lean_inc_ref(v___y_161_);
lean_inc(v_snd_203_);
v___x_245_ = lean_infer_type(v_snd_203_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref(v___x_245_);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v___y_162_);
lean_inc_ref(v___y_161_);
lean_inc(v_fst_209_);
v___x_247_ = lean_infer_type(v_fst_209_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref(v___x_247_);
v___x_249_ = l_Lean_Meta_isExprDefEq(v_fst_202_, v_fst_209_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; uint8_t v___x_251_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
v___x_251_ = lean_unbox(v_a_250_);
lean_dec(v_a_250_);
if (v___x_251_ == 0)
{
lean_dec(v_a_248_);
lean_dec(v_a_246_);
v___y_212_ = v___x_249_;
goto v___jp_211_;
}
else
{
lean_object* v___x_252_; 
lean_dec_ref(v___x_249_);
v___x_252_ = l_Lean_Meta_isExprDefEq(v_a_246_, v_a_248_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
v___y_212_ = v___x_252_;
goto v___jp_211_;
}
}
else
{
lean_dec(v_a_248_);
lean_dec(v_a_246_);
v___y_212_ = v___x_249_;
goto v___jp_211_;
}
}
else
{
lean_dec(v_a_246_);
lean_dec(v_snd_210_);
lean_dec(v_fst_209_);
lean_dec(v_fst_208_);
lean_dec(v_snd_203_);
lean_dec(v_fst_202_);
lean_dec(v_snd_172_);
lean_dec(v_fst_171_);
lean_del_object(v___x_169_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
return v___x_247_;
}
}
else
{
lean_dec(v_snd_210_);
lean_dec(v_fst_209_);
lean_dec(v_fst_208_);
lean_dec(v_snd_203_);
lean_dec(v_fst_202_);
lean_dec(v_snd_172_);
lean_dec(v_fst_171_);
lean_del_object(v___x_169_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
return v___x_245_;
}
v___jp_211_:
{
if (lean_obj_tag(v___y_212_) == 0)
{
lean_object* v_a_213_; uint8_t v___x_214_; 
v_a_213_ = lean_ctor_get(v___y_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref(v___y_212_);
v___x_214_ = lean_unbox(v_a_213_);
lean_dec(v_a_213_);
if (v___x_214_ == 0)
{
lean_dec(v_snd_210_);
lean_dec(v_fst_208_);
lean_dec(v_snd_203_);
lean_dec(v_snd_172_);
lean_del_object(v___x_169_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
v___y_174_ = v___y_159_;
v___y_175_ = v___y_160_;
v___y_176_ = v___y_161_;
v___y_177_ = v___y_162_;
v___y_178_ = v___y_163_;
v___y_179_ = v___y_164_;
goto v___jp_173_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_215_ = l_Lean_mkAppB(v_fst_208_, v_snd_203_, v_snd_210_);
v___x_216_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0));
v___x_217_ = l_Lean_Name_mkStr2(v___x_157_, v___x_216_);
v___x_218_ = l_Lean_Name_append(v_tag_158_, v___x_217_);
lean_inc_ref(v___x_215_);
v___x_219_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_215_, v___x_218_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_221_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_a_220_);
lean_dec_ref(v___x_219_);
lean_inc(v_fst_171_);
v___x_221_ = l_Lean_Elab_Term_mkCalcTrans(v_fst_171_, v_snd_172_, v_a_220_, v___x_215_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v_snd_172_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v_fst_223_; lean_object* v_snd_224_; lean_object* v___x_225_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref(v___x_221_);
v_fst_223_ = lean_ctor_get(v_a_222_, 0);
lean_inc(v_fst_223_);
v_snd_224_ = lean_ctor_get(v_a_222_, 1);
lean_inc(v_snd_224_);
lean_dec(v_a_222_);
lean_inc_ref(v___x_154_);
v___x_225_ = l_Lean_Meta_isExprDefEq(v_snd_224_, v___x_154_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
lean_del_object(v___x_169_);
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
uint8_t v___x_230_; 
v___x_230_ = lean_unbox(v_a_226_);
lean_dec(v_a_226_);
if (v___x_230_ == 0)
{
lean_del_object(v___x_228_);
lean_dec(v_fst_223_);
v___y_174_ = v___y_159_;
v___y_175_ = v___y_160_;
v___y_176_ = v___y_161_;
v___y_177_ = v___y_162_;
v___y_178_ = v___y_163_;
v___y_179_ = v___y_164_;
goto v___jp_173_;
}
else
{
lean_object* v___x_232_; 
lean_dec(v_fst_171_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v_fst_223_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_fst_223_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v_a_235_; 
lean_dec(v_fst_223_);
v_a_235_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_235_);
lean_dec_ref(v___x_225_);
v_a_189_ = v_a_235_;
goto v___jp_188_;
}
}
else
{
lean_object* v_a_236_; 
v_a_236_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_236_);
lean_dec_ref(v___x_221_);
v_a_189_ = v_a_236_;
goto v___jp_188_;
}
}
else
{
lean_dec_ref(v___x_215_);
lean_dec(v_snd_172_);
lean_dec(v_fst_171_);
lean_del_object(v___x_169_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
return v___x_219_;
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_snd_210_);
lean_dec(v_fst_208_);
lean_dec(v_snd_203_);
lean_dec(v_snd_172_);
lean_dec(v_fst_171_);
lean_del_object(v___x_169_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
v_a_237_ = lean_ctor_get(v___y_212_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___y_212_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___y_212_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___y_212_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
else
{
lean_dec(v_a_205_);
lean_dec(v_snd_203_);
lean_dec(v_fst_202_);
lean_dec(v_snd_172_);
lean_del_object(v___x_169_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
v___y_174_ = v___y_159_;
v___y_175_ = v___y_160_;
v___y_176_ = v___y_161_;
v___y_177_ = v___y_162_;
v___y_178_ = v___y_163_;
v___y_179_ = v___y_164_;
goto v___jp_173_;
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_snd_203_);
lean_dec(v_fst_202_);
lean_dec(v_snd_172_);
lean_dec(v_fst_171_);
lean_del_object(v___x_169_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
v_a_253_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_204_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_204_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v_a_199_);
lean_dec(v_snd_172_);
lean_dec(v_fst_171_);
lean_del_object(v___x_169_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
v___x_261_ = lean_obj_once(&l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4, &l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4);
v___x_262_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(v___x_261_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v___x_262_;
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec(v_snd_172_);
lean_dec(v_fst_171_);
lean_del_object(v___x_169_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
v_a_263_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_198_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_198_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v___x_272_; 
lean_dec(v_snd_172_);
lean_del_object(v___x_169_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v_fst_171_);
v___x_272_ = v___x_195_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_fst_171_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec(v_snd_172_);
lean_dec(v_fst_171_);
lean_del_object(v___x_169_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
v_a_275_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_192_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_192_);
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
v___jp_173_:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_154_);
v___x_181_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(v___x_180_, v_fst_171_, v___f_155_, v___f_156_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v___x_181_;
}
v___jp_182_:
{
if (v___y_184_ == 0)
{
lean_dec_ref(v___y_183_);
lean_del_object(v___x_169_);
v___y_174_ = v___y_159_;
v___y_175_ = v___y_160_;
v___y_176_ = v___y_161_;
v___y_177_ = v___y_162_;
v___y_178_ = v___y_163_;
v___y_179_ = v___y_164_;
goto v___jp_173_;
}
else
{
lean_object* v___x_186_; 
lean_dec(v_fst_171_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 1);
lean_ctor_set(v___x_169_, 0, v___y_183_);
v___x_186_ = v___x_169_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___y_183_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
v___jp_188_:
{
uint8_t v___x_190_; 
v___x_190_ = l_Lean_Exception_isInterrupt(v_a_189_);
if (v___x_190_ == 0)
{
uint8_t v___x_191_; 
lean_inc_ref(v_a_189_);
v___x_191_ = l_Lean_Exception_isRuntime(v_a_189_);
v___y_183_ = v_a_189_;
v___y_184_ = v___x_191_;
goto v___jp_182_;
}
else
{
v___y_183_ = v_a_189_;
v___y_184_ = v___x_190_;
goto v___jp_182_;
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
v_a_284_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_166_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_166_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2___boxed(lean_object* v_a_292_, lean_object* v___x_293_, lean_object* v___f_294_, lean_object* v___f_295_, lean_object* v___x_296_, lean_object* v_tag_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Elab_Tactic_evalCalc___lam__2(v_a_292_, v___x_293_, v___f_294_, v___f_295_, v___x_296_, v_tag_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec_ref(v_a_292_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__3(lean_object* v_steps_306_, lean_object* v_target_307_, lean_object* v___x_308_, lean_object* v_tag_309_, lean_object* v___x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_306_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; lean_object* v_a_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___x_326_; lean_object* v___f_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc_n(v_a_321_, 3);
lean_dec_ref(v___x_320_);
v___x_322_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_target_307_, v___y_316_);
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref(v___x_322_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__0___boxed), 9, 1);
lean_closure_set(v___f_324_, 0, v_a_321_);
v___f_325_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__1___boxed), 9, 1);
lean_closure_set(v___f_325_, 0, v_a_321_);
v___x_326_ = l_Lean_Expr_consumeMData(v_a_323_);
lean_dec(v_a_323_);
lean_inc(v_tag_309_);
v___f_327_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__2___boxed), 13, 6);
lean_closure_set(v___f_327_, 0, v_a_321_);
lean_closure_set(v___f_327_, 1, v___x_326_);
lean_closure_set(v___f_327_, 2, v___f_325_);
lean_closure_set(v___f_327_, 3, v___f_324_);
lean_closure_set(v___f_327_, 4, v___x_308_);
lean_closure_set(v___f_327_, 5, v_tag_309_);
v___x_328_ = 0;
v___x_329_ = lean_box(v___x_328_);
v___x_330_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___boxed), 12, 3);
lean_closure_set(v___x_330_, 0, lean_box(0));
lean_closure_set(v___x_330_, 1, v___f_327_);
lean_closure_set(v___x_330_, 2, v___x_329_);
v___x_331_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_330_, v_tag_309_, v___x_310_, v___x_328_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v___x_335_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref(v___x_331_);
v_fst_333_ = lean_ctor_get(v_a_332_, 0);
lean_inc(v_fst_333_);
v_snd_334_ = lean_ctor_get(v_a_332_, 1);
lean_inc(v_snd_334_);
lean_dec(v_a_332_);
v___x_335_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_334_, v___y_312_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; 
v_unused_343_ = lean_ctor_get(v___x_335_, 0);
lean_dec(v_unused_343_);
v___x_337_ = v___x_335_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_dec(v___x_335_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v_fst_333_);
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_fst_333_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_fst_333_);
v_a_344_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_335_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_335_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_331_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_331_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec(v___x_310_);
lean_dec(v_tag_309_);
lean_dec_ref(v___x_308_);
lean_dec_ref(v_target_307_);
v_a_360_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_320_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_320_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__3___boxed(lean_object* v_steps_368_, lean_object* v_target_369_, lean_object* v___x_370_, lean_object* v_tag_371_, lean_object* v___x_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Elab_Tactic_evalCalc___lam__3(v_steps_368_, v_target_369_, v___x_370_, v_tag_371_, v___x_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__4(lean_object* v_a_383_, lean_object* v_trees_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
lean_inc(v___y_392_);
lean_inc_ref(v___y_391_);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
lean_inc(v___y_386_);
lean_inc_ref(v___y_385_);
v___x_394_ = lean_apply_9(v_a_383_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, lean_box(0));
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v_a_395_);
lean_ctor_set(v___x_399_, 1, v_trees_384_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec_ref(v_trees_384_);
v_a_404_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_394_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_394_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__4___boxed(lean_object* v_a_412_, lean_object* v_trees_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Elab_Tactic_evalCalc___lam__4(v_a_412_, v_trees_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(lean_object* v___y_424_, lean_object* v_mkInfoTree_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v_a_433_, lean_object* v_a_x3f_434_){
_start:
{
lean_object* v___x_436_; lean_object* v_infoState_437_; lean_object* v_trees_438_; lean_object* v___x_439_; 
v___x_436_ = lean_st_ref_get(v___y_424_);
v_infoState_437_ = lean_ctor_get(v___x_436_, 7);
lean_inc_ref(v_infoState_437_);
lean_dec(v___x_436_);
v_trees_438_ = lean_ctor_get(v_infoState_437_, 2);
lean_inc_ref(v_trees_438_);
lean_dec_ref(v_infoState_437_);
lean_inc(v___y_424_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
lean_inc(v___y_427_);
lean_inc_ref(v___y_426_);
v___x_439_ = lean_apply_10(v_mkInfoTree_425_, v_trees_438_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_424_, lean_box(0));
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_479_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_479_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_479_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_479_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v_infoState_445_; lean_object* v_env_446_; lean_object* v_nextMacroScope_447_; lean_object* v_ngen_448_; lean_object* v_auxDeclNGen_449_; lean_object* v_traceState_450_; lean_object* v_cache_451_; lean_object* v_messages_452_; lean_object* v_snapshotTasks_453_; lean_object* v_newDecls_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_478_; 
v___x_444_ = lean_st_ref_take(v___y_424_);
v_infoState_445_ = lean_ctor_get(v___x_444_, 7);
v_env_446_ = lean_ctor_get(v___x_444_, 0);
v_nextMacroScope_447_ = lean_ctor_get(v___x_444_, 1);
v_ngen_448_ = lean_ctor_get(v___x_444_, 2);
v_auxDeclNGen_449_ = lean_ctor_get(v___x_444_, 3);
v_traceState_450_ = lean_ctor_get(v___x_444_, 4);
v_cache_451_ = lean_ctor_get(v___x_444_, 5);
v_messages_452_ = lean_ctor_get(v___x_444_, 6);
v_snapshotTasks_453_ = lean_ctor_get(v___x_444_, 8);
v_newDecls_454_ = lean_ctor_get(v___x_444_, 9);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_478_ == 0)
{
v___x_456_ = v___x_444_;
v_isShared_457_ = v_isSharedCheck_478_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_newDecls_454_);
lean_inc(v_snapshotTasks_453_);
lean_inc(v_infoState_445_);
lean_inc(v_messages_452_);
lean_inc(v_cache_451_);
lean_inc(v_traceState_450_);
lean_inc(v_auxDeclNGen_449_);
lean_inc(v_ngen_448_);
lean_inc(v_nextMacroScope_447_);
lean_inc(v_env_446_);
lean_dec(v___x_444_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_478_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
uint8_t v_enabled_458_; lean_object* v_assignment_459_; lean_object* v_lazyAssignment_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_476_; 
v_enabled_458_ = lean_ctor_get_uint8(v_infoState_445_, sizeof(void*)*3);
v_assignment_459_ = lean_ctor_get(v_infoState_445_, 0);
v_lazyAssignment_460_ = lean_ctor_get(v_infoState_445_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_infoState_445_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; 
v_unused_477_ = lean_ctor_get(v_infoState_445_, 2);
lean_dec(v_unused_477_);
v___x_462_ = v_infoState_445_;
v_isShared_463_ = v_isSharedCheck_476_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_lazyAssignment_460_);
lean_inc(v_assignment_459_);
lean_dec(v_infoState_445_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_476_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = l_Lean_PersistentArray_push___redArg(v_a_433_, v_a_440_);
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
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_env_446_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_nextMacroScope_447_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_ngen_448_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_auxDeclNGen_449_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_traceState_450_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_cache_451_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_messages_452_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_snapshotTasks_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 9, v_newDecls_454_);
v___x_468_ = v_reuseFailAlloc_474_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = lean_st_ref_set(v___y_424_, v___x_468_);
v___x_470_ = lean_box(0);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_470_);
v___x_472_ = v___x_442_;
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
lean_dec_ref(v_a_433_);
v_a_480_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_439_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_439_);
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
lean_object* v___x_512_; lean_object* v_infoState_513_; lean_object* v_trees_514_; lean_object* v___x_515_; lean_object* v_infoState_516_; lean_object* v_env_517_; lean_object* v_nextMacroScope_518_; lean_object* v_ngen_519_; lean_object* v_auxDeclNGen_520_; lean_object* v_traceState_521_; lean_object* v_cache_522_; lean_object* v_messages_523_; lean_object* v_snapshotTasks_524_; lean_object* v_newDecls_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_546_; 
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
v_newDecls_525_ = lean_ctor_get(v___x_515_, 9);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_546_ == 0)
{
v___x_527_ = v___x_515_;
v_isShared_528_ = v_isSharedCheck_546_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_newDecls_525_);
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
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_546_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint8_t v_enabled_529_; lean_object* v_assignment_530_; lean_object* v_lazyAssignment_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_544_; 
v_enabled_529_ = lean_ctor_get_uint8(v_infoState_516_, sizeof(void*)*3);
v_assignment_530_ = lean_ctor_get(v_infoState_516_, 0);
v_lazyAssignment_531_ = lean_ctor_get(v_infoState_516_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_infoState_516_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v_infoState_516_, 2);
lean_dec(v_unused_545_);
v___x_533_ = v_infoState_516_;
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_lazyAssignment_531_);
lean_inc(v_assignment_530_);
lean_dec(v_infoState_516_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 2, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_assignment_530_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_lazyAssignment_531_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v___x_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_543_, sizeof(void*)*3, v_enabled_529_);
v___x_537_ = v_reuseFailAlloc_543_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_539_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 7, v___x_537_);
v___x_539_ = v___x_527_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_env_517_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_nextMacroScope_518_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_ngen_519_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_auxDeclNGen_520_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_traceState_521_);
lean_ctor_set(v_reuseFailAlloc_542_, 5, v_cache_522_);
lean_ctor_set(v_reuseFailAlloc_542_, 6, v_messages_523_);
lean_ctor_set(v_reuseFailAlloc_542_, 7, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_542_, 8, v_snapshotTasks_524_);
lean_ctor_set(v_reuseFailAlloc_542_, 9, v_newDecls_525_);
v___x_539_ = v_reuseFailAlloc_542_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_st_ref_set(v___y_510_, v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v_trees_514_);
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___boxed(lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_547_);
lean_dec(v___y_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(lean_object* v_x_550_, lean_object* v_mkInfoTree_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; lean_object* v_infoState_562_; uint8_t v_enabled_563_; 
v___x_561_ = lean_st_ref_get(v___y_559_);
v_infoState_562_ = lean_ctor_get(v___x_561_, 7);
lean_inc_ref(v_infoState_562_);
lean_dec(v___x_561_);
v_enabled_563_ = lean_ctor_get_uint8(v_infoState_562_, sizeof(void*)*3);
lean_dec_ref(v_infoState_562_);
if (v_enabled_563_ == 0)
{
lean_object* v___x_564_; 
lean_dec_ref(v_mkInfoTree_551_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___y_557_);
lean_inc_ref(v___y_556_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
v___x_564_ = lean_apply_9(v_x_550_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, lean_box(0));
return v___x_564_;
}
else
{
lean_object* v___x_565_; lean_object* v_a_566_; lean_object* v_r_567_; 
v___x_565_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_559_);
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref(v___x_565_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___y_557_);
lean_inc_ref(v___y_556_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
v_r_567_ = lean_apply_9(v_x_550_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, lean_box(0));
if (lean_obj_tag(v_r_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_592_; 
v_a_568_ = lean_ctor_get(v_r_567_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_r_567_);
if (v_isSharedCheck_592_ == 0)
{
v___x_570_ = v_r_567_;
v_isShared_571_ = v_isSharedCheck_592_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v_r_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_592_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
lean_inc(v_a_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 1);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_591_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_559_, v_mkInfoTree_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v_a_566_, v___x_573_);
lean_dec_ref(v___x_573_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v___x_574_, 0);
lean_dec(v_unused_582_);
v___x_576_ = v___x_574_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_dec(v___x_574_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v_a_568_);
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_568_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_a_568_);
v_a_583_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_574_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_574_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_a_593_ = lean_ctor_get(v_r_567_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v_r_567_);
v___x_594_ = lean_box(0);
v___x_595_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_559_, v_mkInfoTree_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v_a_566_, v___x_594_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v___x_595_, 0);
lean_dec(v_unused_603_);
v___x_597_ = v___x_595_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_dec(v___x_595_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 1);
lean_ctor_set(v___x_597_, 0, v_a_593_);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_593_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_a_593_);
v_a_604_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_595_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_595_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___boxed(lean_object* v_x_612_, lean_object* v_mkInfoTree_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v_x_612_, v_mkInfoTree_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__5(lean_object* v_steps_624_, lean_object* v___x_625_, lean_object* v___x_626_, lean_object* v_target_627_, lean_object* v_tag_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_638_; 
lean_inc(v_steps_624_);
v___x_638_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_steps_624_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___f_640_; lean_object* v___f_641_; lean_object* v___x_642_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
v___f_640_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__3___boxed), 14, 5);
lean_closure_set(v___f_640_, 0, v_steps_624_);
lean_closure_set(v___f_640_, 1, v_target_627_);
lean_closure_set(v___f_640_, 2, v___x_625_);
lean_closure_set(v___f_640_, 3, v_tag_628_);
lean_closure_set(v___f_640_, 4, v___x_626_);
v___f_641_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__4___boxed), 11, 1);
lean_closure_set(v___f_641_, 0, v_a_639_);
v___x_642_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v___f_640_, v___f_641_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_642_;
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_tag_628_);
lean_dec_ref(v_target_627_);
lean_dec(v___x_626_);
lean_dec_ref(v___x_625_);
lean_dec(v_steps_624_);
v_a_643_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_638_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_638_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__5___boxed(lean_object* v_steps_651_, lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v_target_654_, lean_object* v_tag_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Elab_Tactic_evalCalc___lam__5(v_steps_651_, v___x_652_, v___x_653_, v_target_654_, v_tag_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc(lean_object* v_x_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__2));
lean_inc(v_x_678_);
v___x_689_ = l_Lean_Syntax_isOfKind(v_x_678_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
lean_dec(v_x_678_);
v___x_690_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v___x_690_;
}
else
{
lean_object* v___x_691_; lean_object* v_steps_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_691_ = lean_unsigned_to_nat(1u);
v_steps_692_ = l_Lean_Syntax_getArg(v_x_678_, v___x_691_);
v___x_693_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__4));
lean_inc(v_steps_692_);
v___x_694_ = l_Lean_Syntax_isOfKind(v_steps_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
lean_dec(v_steps_692_);
lean_dec(v_x_678_);
v___x_695_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v___x_695_;
}
else
{
lean_object* v_fileName_696_; lean_object* v_fileMap_697_; lean_object* v_options_698_; lean_object* v_currRecDepth_699_; lean_object* v_maxRecDepth_700_; lean_object* v_ref_701_; lean_object* v_currNamespace_702_; lean_object* v_openDecls_703_; lean_object* v_initHeartbeats_704_; lean_object* v_maxHeartbeats_705_; lean_object* v_quotContext_706_; lean_object* v_currMacroScope_707_; uint8_t v_diag_708_; lean_object* v_cancelTk_x3f_709_; uint8_t v_suppressElabErrors_710_; lean_object* v_inheritedTraceOptions_711_; lean_object* v___x_712_; lean_object* v_tk_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___f_716_; uint8_t v___x_717_; lean_object* v_ref_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_fileName_696_ = lean_ctor_get(v_a_685_, 0);
v_fileMap_697_ = lean_ctor_get(v_a_685_, 1);
v_options_698_ = lean_ctor_get(v_a_685_, 2);
v_currRecDepth_699_ = lean_ctor_get(v_a_685_, 3);
v_maxRecDepth_700_ = lean_ctor_get(v_a_685_, 4);
v_ref_701_ = lean_ctor_get(v_a_685_, 5);
v_currNamespace_702_ = lean_ctor_get(v_a_685_, 6);
v_openDecls_703_ = lean_ctor_get(v_a_685_, 7);
v_initHeartbeats_704_ = lean_ctor_get(v_a_685_, 8);
v_maxHeartbeats_705_ = lean_ctor_get(v_a_685_, 9);
v_quotContext_706_ = lean_ctor_get(v_a_685_, 10);
v_currMacroScope_707_ = lean_ctor_get(v_a_685_, 11);
v_diag_708_ = lean_ctor_get_uint8(v_a_685_, sizeof(void*)*14);
v_cancelTk_x3f_709_ = lean_ctor_get(v_a_685_, 12);
v_suppressElabErrors_710_ = lean_ctor_get_uint8(v_a_685_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_711_ = lean_ctor_get(v_a_685_, 13);
v___x_712_ = lean_unsigned_to_nat(0u);
v_tk_713_ = l_Lean_Syntax_getArg(v_x_678_, v___x_712_);
lean_dec(v_x_678_);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__5));
v___x_715_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__6));
v___f_716_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__5___boxed), 14, 3);
lean_closure_set(v___f_716_, 0, v_steps_692_);
lean_closure_set(v___f_716_, 1, v___x_714_);
lean_closure_set(v___f_716_, 2, v___x_715_);
v___x_717_ = 0;
v_ref_718_ = l_Lean_replaceRef(v_tk_713_, v_ref_701_);
lean_dec(v_tk_713_);
lean_inc_ref(v_inheritedTraceOptions_711_);
lean_inc(v_cancelTk_x3f_709_);
lean_inc(v_currMacroScope_707_);
lean_inc(v_quotContext_706_);
lean_inc(v_maxHeartbeats_705_);
lean_inc(v_initHeartbeats_704_);
lean_inc(v_openDecls_703_);
lean_inc(v_currNamespace_702_);
lean_inc(v_maxRecDepth_700_);
lean_inc(v_currRecDepth_699_);
lean_inc_ref(v_options_698_);
lean_inc_ref(v_fileMap_697_);
lean_inc_ref(v_fileName_696_);
v___x_719_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_719_, 0, v_fileName_696_);
lean_ctor_set(v___x_719_, 1, v_fileMap_697_);
lean_ctor_set(v___x_719_, 2, v_options_698_);
lean_ctor_set(v___x_719_, 3, v_currRecDepth_699_);
lean_ctor_set(v___x_719_, 4, v_maxRecDepth_700_);
lean_ctor_set(v___x_719_, 5, v_ref_718_);
lean_ctor_set(v___x_719_, 6, v_currNamespace_702_);
lean_ctor_set(v___x_719_, 7, v_openDecls_703_);
lean_ctor_set(v___x_719_, 8, v_initHeartbeats_704_);
lean_ctor_set(v___x_719_, 9, v_maxHeartbeats_705_);
lean_ctor_set(v___x_719_, 10, v_quotContext_706_);
lean_ctor_set(v___x_719_, 11, v_currMacroScope_707_);
lean_ctor_set(v___x_719_, 12, v_cancelTk_x3f_709_);
lean_ctor_set(v___x_719_, 13, v_inheritedTraceOptions_711_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*14, v_diag_708_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*14 + 1, v_suppressElabErrors_710_);
v___x_720_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v___x_715_, v___f_716_, v___x_717_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v___x_719_, v_a_686_);
lean_dec_ref(v___x_719_);
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___boxed(lean_object* v_x_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Elab_Tactic_evalCalc(v_x_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___boxed(lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(lean_object* v_00_u03b1_752_, lean_object* v_x_753_, lean_object* v_mkInfoTree_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v_x_753_, v_mkInfoTree_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___boxed(lean_object* v_00_u03b1_765_, lean_object* v_x_766_, lean_object* v_mkInfoTree_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(v_00_u03b1_765_, v_x_766_, v_mkInfoTree_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1(){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_787_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_788_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__2));
v___x_789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_790_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___boxed), 10, 0);
v___x_791_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_787_, v___x_788_, v___x_789_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___boxed(lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3(){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_797_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0));
v___x_798_ = l_Lean_addBuiltinDocString(v___x_796_, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___boxed(lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5(){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_828_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6));
v___x_829_ = l_Lean_addBuiltinDeclarationRanges(v___x_827_, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___boxed(lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
return v_res_831_;
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
