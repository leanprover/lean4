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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Term_mkCalcStepViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_runTermElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pushGoals___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Elaborator for the `calc` tactic mode variant."};
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
v___x_51_ = lean_st_ref_put(v___y_32_, v___x_50_);
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
v___x_82_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(lean_object* v_msg_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_8984__overap_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0, &l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0);
v___x_8984__overap_92_ = lean_panic_fn_borrowed(v___x_91_, v_msg_83_);
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
v___x_93_ = lean_apply_7(v___x_8984__overap_92_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, lean_box(0));
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
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_289_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_289_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_289_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_289_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v_fst_171_; lean_object* v_snd_172_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v_a_183_; lean_object* v___x_192_; 
v_fst_171_ = lean_ctor_get(v_a_167_, 0);
lean_inc(v_fst_171_);
v_snd_172_ = lean_ctor_get(v_a_167_, 1);
lean_inc_n(v_snd_172_, 2);
lean_dec(v_a_167_);
lean_inc_ref(v___x_154_);
v___x_192_ = l_Lean_Meta_isExprDefEq(v_snd_172_, v___x_154_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_280_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_280_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_280_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_280_;
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
lean_dec_ref_known(v___x_198_, 1);
if (lean_obj_tag(v_a_199_) == 1)
{
lean_object* v_val_200_; lean_object* v_snd_201_; lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_204_; 
v_val_200_ = lean_ctor_get(v_a_199_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v_a_199_, 1);
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
lean_dec_ref_known(v___x_204_, 1);
if (lean_obj_tag(v_a_205_) == 1)
{
lean_object* v_val_206_; lean_object* v_snd_207_; lean_object* v_fst_208_; lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___x_211_; 
v_val_206_ = lean_ctor_get(v_a_205_, 0);
lean_inc(v_val_206_);
lean_dec_ref_known(v_a_205_, 1);
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
v___x_211_ = lean_infer_type(v_snd_203_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v___y_162_);
lean_inc_ref(v___y_161_);
lean_inc(v_fst_209_);
v___x_213_ = lean_infer_type(v_fst_209_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = l_Lean_Meta_isExprDefEq(v_fst_202_, v_fst_209_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; uint8_t v___x_217_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_215_, 1);
v___x_217_ = lean_unbox(v_a_216_);
lean_dec(v_a_216_);
if (v___x_217_ == 0)
{
lean_dec(v_a_214_);
lean_dec(v_a_212_);
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
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_isExprDefEq(v_a_212_, v_a_214_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; uint8_t v___x_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = lean_unbox(v_a_219_);
lean_dec(v_a_219_);
if (v___x_220_ == 0)
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
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_221_ = l_Lean_mkAppB(v_fst_208_, v_snd_203_, v_snd_210_);
v___x_222_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0));
v___x_223_ = l_Lean_Name_mkStr2(v___x_157_, v___x_222_);
v___x_224_ = l_Lean_Name_append(v_tag_158_, v___x_223_);
lean_inc_ref(v___x_221_);
v___x_225_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_221_, v___x_224_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_227_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
lean_inc(v_fst_171_);
v___x_227_ = l_Lean_Elab_Term_mkCalcTrans(v_fst_171_, v_snd_172_, v_a_226_, v___x_221_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v_snd_172_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v___x_231_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v_fst_229_ = lean_ctor_get(v_a_228_, 0);
lean_inc(v_fst_229_);
v_snd_230_ = lean_ctor_get(v_a_228_, 1);
lean_inc(v_snd_230_);
lean_dec(v_a_228_);
lean_inc_ref(v___x_154_);
v___x_231_ = l_Lean_Meta_isExprDefEq(v_snd_230_, v___x_154_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_240_; 
lean_del_object(v___x_169_);
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_240_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_240_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_240_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
uint8_t v___x_236_; 
v___x_236_ = lean_unbox(v_a_232_);
lean_dec(v_a_232_);
if (v___x_236_ == 0)
{
lean_del_object(v___x_234_);
lean_dec(v_fst_229_);
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
lean_object* v___x_238_; 
lean_dec(v_fst_171_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v_fst_229_);
v___x_238_ = v___x_234_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_fst_229_);
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
else
{
lean_object* v_a_241_; 
lean_dec(v_fst_229_);
v_a_241_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_231_, 1);
v_a_183_ = v_a_241_;
goto v___jp_182_;
}
}
else
{
lean_object* v_a_242_; 
v_a_242_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v___x_227_, 1);
v_a_183_ = v_a_242_;
goto v___jp_182_;
}
}
else
{
lean_dec_ref(v___x_221_);
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
return v___x_225_;
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
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
v_a_243_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_218_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_218_);
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
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec(v_a_214_);
lean_dec(v_a_212_);
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
v_a_251_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_215_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_215_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_dec(v_a_212_);
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
return v___x_213_;
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
return v___x_211_;
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
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
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
v_a_259_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_204_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_204_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_a_199_);
lean_dec(v_snd_172_);
lean_dec(v_fst_171_);
lean_del_object(v___x_169_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
v___x_267_ = lean_obj_once(&l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4, &l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4);
v___x_268_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(v___x_267_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v___x_268_;
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
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
v_a_269_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_198_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_198_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v___x_278_; 
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
v___x_278_ = v___x_195_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_fst_171_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
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
v_a_281_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_192_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_192_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
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
uint8_t v___x_184_; 
v___x_184_ = l_Lean_Exception_isInterrupt(v_a_183_);
if (v___x_184_ == 0)
{
uint8_t v___x_185_; 
lean_inc_ref(v_a_183_);
v___x_185_ = l_Lean_Exception_isRuntime(v_a_183_);
if (v___x_185_ == 0)
{
lean_dec_ref(v_a_183_);
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
lean_object* v___x_187_; 
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
lean_ctor_set(v___x_169_, 0, v_a_183_);
v___x_187_ = v___x_169_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_183_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
else
{
lean_object* v___x_190_; 
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
lean_ctor_set(v___x_169_, 0, v_a_183_);
v___x_190_ = v___x_169_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_183_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v_tag_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___f_156_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v___x_154_);
v_a_290_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_166_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_166_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2___boxed(lean_object* v_a_298_, lean_object* v___x_299_, lean_object* v___f_300_, lean_object* v___f_301_, lean_object* v___x_302_, lean_object* v_tag_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Elab_Tactic_evalCalc___lam__2(v_a_298_, v___x_299_, v___f_300_, v___f_301_, v___x_302_, v_tag_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec_ref(v_a_298_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__3(lean_object* v_steps_312_, lean_object* v_target_313_, lean_object* v___x_314_, lean_object* v_tag_315_, lean_object* v___x_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_312_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___f_328_; lean_object* v___f_329_; lean_object* v___x_330_; lean_object* v_a_331_; lean_object* v___x_332_; lean_object* v___f_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_n(v_a_327_, 3);
lean_dec_ref_known(v___x_326_, 1);
v___f_328_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__0___boxed), 9, 1);
lean_closure_set(v___f_328_, 0, v_a_327_);
v___f_329_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__1___boxed), 9, 1);
lean_closure_set(v___f_329_, 0, v_a_327_);
v___x_330_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_target_313_, v___y_322_);
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref(v___x_330_);
v___x_332_ = l_Lean_Expr_consumeMData(v_a_331_);
lean_dec(v_a_331_);
lean_inc(v_tag_315_);
v___f_333_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__2___boxed), 13, 6);
lean_closure_set(v___f_333_, 0, v_a_327_);
lean_closure_set(v___f_333_, 1, v___x_332_);
lean_closure_set(v___f_333_, 2, v___f_328_);
lean_closure_set(v___f_333_, 3, v___f_329_);
lean_closure_set(v___f_333_, 4, v___x_314_);
lean_closure_set(v___f_333_, 5, v_tag_315_);
v___x_334_ = 0;
v___x_335_ = lean_box(v___x_334_);
v___x_336_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___boxed), 12, 3);
lean_closure_set(v___x_336_, 0, lean_box(0));
lean_closure_set(v___x_336_, 1, v___f_333_);
lean_closure_set(v___x_336_, 2, v___x_335_);
v___x_337_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_336_, v_tag_315_, v___x_316_, v___x_334_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v_fst_339_; lean_object* v_snd_340_; lean_object* v___x_341_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v_fst_339_ = lean_ctor_get(v_a_338_, 0);
lean_inc(v_fst_339_);
v_snd_340_ = lean_ctor_get(v_a_338_, 1);
lean_inc(v_snd_340_);
lean_dec(v_a_338_);
v___x_341_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_340_, v___y_318_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v___x_341_, 0);
lean_dec(v_unused_349_);
v___x_343_ = v___x_341_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_dec(v___x_341_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v_fst_339_);
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_fst_339_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_fst_339_);
v_a_350_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_341_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_341_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_a_358_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_337_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_337_);
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
lean_dec(v___x_316_);
lean_dec(v_tag_315_);
lean_dec_ref(v___x_314_);
lean_dec_ref(v_target_313_);
v_a_366_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_326_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_326_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__3___boxed(lean_object* v_steps_374_, lean_object* v_target_375_, lean_object* v___x_376_, lean_object* v_tag_377_, lean_object* v___x_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Elab_Tactic_evalCalc___lam__3(v_steps_374_, v_target_375_, v___x_376_, v_tag_377_, v___x_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__4(lean_object* v_a_389_, lean_object* v_trees_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; 
lean_inc(v___y_398_);
lean_inc_ref(v___y_397_);
lean_inc(v___y_396_);
lean_inc_ref(v___y_395_);
lean_inc(v___y_394_);
lean_inc_ref(v___y_393_);
lean_inc(v___y_392_);
lean_inc_ref(v___y_391_);
v___x_400_ = lean_apply_9(v_a_389_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, lean_box(0));
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v_a_401_);
lean_ctor_set(v___x_405_, 1, v_trees_390_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v_trees_390_);
v_a_410_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_400_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_400_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__4___boxed(lean_object* v_a_418_, lean_object* v_trees_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Elab_Tactic_evalCalc___lam__4(v_a_418_, v_trees_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(lean_object* v___y_430_, lean_object* v_mkInfoTree_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v_a_439_, lean_object* v_a_x3f_440_){
_start:
{
lean_object* v___x_442_; lean_object* v_infoState_443_; lean_object* v_trees_444_; lean_object* v___x_445_; 
v___x_442_ = lean_st_ref_get(v___y_430_);
v_infoState_443_ = lean_ctor_get(v___x_442_, 8);
lean_inc_ref(v_infoState_443_);
lean_dec(v___x_442_);
v_trees_444_ = lean_ctor_get(v_infoState_443_, 2);
lean_inc_ref(v_trees_444_);
lean_dec_ref(v_infoState_443_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_438_);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
v___x_445_ = lean_apply_10(v_mkInfoTree_431_, v_trees_444_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_430_, lean_box(0));
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_485_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_485_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_485_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_485_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v_infoState_451_; lean_object* v_env_452_; lean_object* v_nextMacroScope_453_; lean_object* v_ngen_454_; lean_object* v_auxDeclNGen_455_; lean_object* v_traceState_456_; lean_object* v_cache_457_; lean_object* v_recordedDeps_458_; lean_object* v_messages_459_; lean_object* v_snapshotTasks_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_484_; 
v___x_450_ = lean_st_ref_take(v___y_430_);
v_infoState_451_ = lean_ctor_get(v___x_450_, 8);
v_env_452_ = lean_ctor_get(v___x_450_, 0);
v_nextMacroScope_453_ = lean_ctor_get(v___x_450_, 1);
v_ngen_454_ = lean_ctor_get(v___x_450_, 2);
v_auxDeclNGen_455_ = lean_ctor_get(v___x_450_, 3);
v_traceState_456_ = lean_ctor_get(v___x_450_, 4);
v_cache_457_ = lean_ctor_get(v___x_450_, 5);
v_recordedDeps_458_ = lean_ctor_get(v___x_450_, 6);
v_messages_459_ = lean_ctor_get(v___x_450_, 7);
v_snapshotTasks_460_ = lean_ctor_get(v___x_450_, 9);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_484_ == 0)
{
v___x_462_ = v___x_450_;
v_isShared_463_ = v_isSharedCheck_484_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_snapshotTasks_460_);
lean_inc(v_infoState_451_);
lean_inc(v_messages_459_);
lean_inc(v_recordedDeps_458_);
lean_inc(v_cache_457_);
lean_inc(v_traceState_456_);
lean_inc(v_auxDeclNGen_455_);
lean_inc(v_ngen_454_);
lean_inc(v_nextMacroScope_453_);
lean_inc(v_env_452_);
lean_dec(v___x_450_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_484_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
uint8_t v_enabled_464_; lean_object* v_assignment_465_; lean_object* v_lazyAssignment_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_482_; 
v_enabled_464_ = lean_ctor_get_uint8(v_infoState_451_, sizeof(void*)*3);
v_assignment_465_ = lean_ctor_get(v_infoState_451_, 0);
v_lazyAssignment_466_ = lean_ctor_get(v_infoState_451_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_infoState_451_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v_infoState_451_, 2);
lean_dec(v_unused_483_);
v___x_468_ = v_infoState_451_;
v_isShared_469_ = v_isSharedCheck_482_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_lazyAssignment_466_);
lean_inc(v_assignment_465_);
lean_dec(v_infoState_451_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_482_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = lean_box(0);
v___x_471_ = l_Lean_PersistentArray_push___redArg(v_a_439_, v_a_446_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 2, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_assignment_465_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_lazyAssignment_466_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v___x_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*3, v_enabled_464_);
v___x_473_ = v_reuseFailAlloc_481_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_475_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 8, v___x_473_);
v___x_475_ = v___x_462_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_env_452_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_nextMacroScope_453_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_ngen_454_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_auxDeclNGen_455_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_traceState_456_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v_cache_457_);
lean_ctor_set(v_reuseFailAlloc_480_, 6, v_recordedDeps_458_);
lean_ctor_set(v_reuseFailAlloc_480_, 7, v_messages_459_);
lean_ctor_set(v_reuseFailAlloc_480_, 8, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_480_, 9, v_snapshotTasks_460_);
v___x_475_ = v_reuseFailAlloc_480_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_st_ref_put(v___y_430_, v___x_475_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_470_);
v___x_478_ = v___x_448_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_470_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref(v_a_439_);
v_a_486_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_445_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_445_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0___boxed(lean_object* v___y_494_, lean_object* v_mkInfoTree_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v_a_503_, lean_object* v_a_x3f_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_494_, v_mkInfoTree_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v_a_503_, v_a_x3f_504_);
lean_dec(v_a_x3f_504_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_494_);
return v_res_506_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_unsigned_to_nat(32u);
v___x_508_ = lean_mk_empty_array_with_capacity(v___x_507_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_510_ = ((size_t)5ULL);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_unsigned_to_nat(32u);
v___x_513_ = lean_mk_empty_array_with_capacity(v___x_512_);
v___x_514_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0);
v___x_515_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___x_513_);
lean_ctor_set(v___x_515_, 2, v___x_511_);
lean_ctor_set(v___x_515_, 3, v___x_511_);
lean_ctor_set_usize(v___x_515_, 4, v___x_510_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; lean_object* v_infoState_519_; lean_object* v_trees_520_; lean_object* v___x_521_; lean_object* v_infoState_522_; lean_object* v_env_523_; lean_object* v_nextMacroScope_524_; lean_object* v_ngen_525_; lean_object* v_auxDeclNGen_526_; lean_object* v_traceState_527_; lean_object* v_cache_528_; lean_object* v_recordedDeps_529_; lean_object* v_messages_530_; lean_object* v_snapshotTasks_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_552_; 
v___x_518_ = lean_st_ref_get(v___y_516_);
v_infoState_519_ = lean_ctor_get(v___x_518_, 8);
lean_inc_ref(v_infoState_519_);
lean_dec(v___x_518_);
v_trees_520_ = lean_ctor_get(v_infoState_519_, 2);
lean_inc_ref(v_trees_520_);
lean_dec_ref(v_infoState_519_);
v___x_521_ = lean_st_ref_take(v___y_516_);
v_infoState_522_ = lean_ctor_get(v___x_521_, 8);
v_env_523_ = lean_ctor_get(v___x_521_, 0);
v_nextMacroScope_524_ = lean_ctor_get(v___x_521_, 1);
v_ngen_525_ = lean_ctor_get(v___x_521_, 2);
v_auxDeclNGen_526_ = lean_ctor_get(v___x_521_, 3);
v_traceState_527_ = lean_ctor_get(v___x_521_, 4);
v_cache_528_ = lean_ctor_get(v___x_521_, 5);
v_recordedDeps_529_ = lean_ctor_get(v___x_521_, 6);
v_messages_530_ = lean_ctor_get(v___x_521_, 7);
v_snapshotTasks_531_ = lean_ctor_get(v___x_521_, 9);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_552_ == 0)
{
v___x_533_ = v___x_521_;
v_isShared_534_ = v_isSharedCheck_552_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snapshotTasks_531_);
lean_inc(v_infoState_522_);
lean_inc(v_messages_530_);
lean_inc(v_recordedDeps_529_);
lean_inc(v_cache_528_);
lean_inc(v_traceState_527_);
lean_inc(v_auxDeclNGen_526_);
lean_inc(v_ngen_525_);
lean_inc(v_nextMacroScope_524_);
lean_inc(v_env_523_);
lean_dec(v___x_521_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_552_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
uint8_t v_enabled_535_; lean_object* v_assignment_536_; lean_object* v_lazyAssignment_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_550_; 
v_enabled_535_ = lean_ctor_get_uint8(v_infoState_522_, sizeof(void*)*3);
v_assignment_536_ = lean_ctor_get(v_infoState_522_, 0);
v_lazyAssignment_537_ = lean_ctor_get(v_infoState_522_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_infoState_522_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v_infoState_522_, 2);
lean_dec(v_unused_551_);
v___x_539_ = v_infoState_522_;
v_isShared_540_ = v_isSharedCheck_550_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_lazyAssignment_537_);
lean_inc(v_assignment_536_);
lean_dec(v_infoState_522_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_550_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 2, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_assignment_536_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_lazyAssignment_537_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v___x_541_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*3, v_enabled_535_);
v___x_543_ = v_reuseFailAlloc_549_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 8, v___x_543_);
v___x_545_ = v___x_533_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_env_523_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_nextMacroScope_524_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_ngen_525_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_auxDeclNGen_526_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v_traceState_527_);
lean_ctor_set(v_reuseFailAlloc_548_, 5, v_cache_528_);
lean_ctor_set(v_reuseFailAlloc_548_, 6, v_recordedDeps_529_);
lean_ctor_set(v_reuseFailAlloc_548_, 7, v_messages_530_);
lean_ctor_set(v_reuseFailAlloc_548_, 8, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_548_, 9, v_snapshotTasks_531_);
v___x_545_ = v_reuseFailAlloc_548_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_st_ref_put(v___y_516_, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v_trees_520_);
return v___x_547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___boxed(lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_553_);
lean_dec(v___y_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(lean_object* v_x_556_, lean_object* v_mkInfoTree_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; lean_object* v_infoState_568_; uint8_t v_enabled_569_; 
v___x_567_ = lean_st_ref_get(v___y_565_);
v_infoState_568_ = lean_ctor_get(v___x_567_, 8);
lean_inc_ref(v_infoState_568_);
lean_dec(v___x_567_);
v_enabled_569_ = lean_ctor_get_uint8(v_infoState_568_, sizeof(void*)*3);
lean_dec_ref(v_infoState_568_);
if (v_enabled_569_ == 0)
{
lean_object* v___x_570_; 
lean_dec_ref(v_mkInfoTree_557_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
v___x_570_ = lean_apply_9(v_x_556_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, lean_box(0));
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v_a_572_; lean_object* v_r_573_; 
v___x_571_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_565_);
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref(v___x_571_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
v_r_573_ = lean_apply_9(v_x_556_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, lean_box(0));
if (lean_obj_tag(v_r_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_598_; 
v_a_574_ = lean_ctor_get(v_r_573_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_r_573_);
if (v_isSharedCheck_598_ == 0)
{
v___x_576_ = v_r_573_;
v_isShared_577_ = v_isSharedCheck_598_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v_r_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_598_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
lean_inc(v_a_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 1);
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_597_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_565_, v_mkInfoTree_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v_a_572_, v___x_579_);
lean_dec_ref(v___x_579_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_588_);
v___x_582_ = v___x_580_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_dec(v___x_580_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v_a_574_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_574_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_a_574_);
v_a_589_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_580_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_580_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_a_599_ = lean_ctor_get(v_r_573_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v_r_573_, 1);
v___x_600_ = lean_box(0);
v___x_601_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_565_, v_mkInfoTree_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v_a_572_, v___x_600_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_601_, 0);
lean_dec(v_unused_609_);
v___x_603_ = v___x_601_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_dec(v___x_601_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set_tag(v___x_603_, 1);
lean_ctor_set(v___x_603_, 0, v_a_599_);
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_599_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_a_599_);
v_a_610_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_601_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_601_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___boxed(lean_object* v_x_618_, lean_object* v_mkInfoTree_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v_x_618_, v_mkInfoTree_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__5(lean_object* v_steps_630_, lean_object* v___x_631_, lean_object* v___x_632_, lean_object* v_target_633_, lean_object* v_tag_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___f_644_; lean_object* v___x_645_; 
lean_inc(v_steps_630_);
v___f_644_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__3___boxed), 14, 5);
lean_closure_set(v___f_644_, 0, v_steps_630_);
lean_closure_set(v___f_644_, 1, v_target_633_);
lean_closure_set(v___f_644_, 2, v___x_631_);
lean_closure_set(v___f_644_, 3, v_tag_634_);
lean_closure_set(v___f_644_, 4, v___x_632_);
v___x_645_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_steps_630_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___f_647_; lean_object* v___x_648_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v___f_647_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__4___boxed), 11, 1);
lean_closure_set(v___f_647_, 0, v_a_646_);
v___x_648_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v___f_644_, v___f_647_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
return v___x_648_;
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v___f_644_);
v_a_649_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_645_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__5___boxed(lean_object* v_steps_657_, lean_object* v___x_658_, lean_object* v___x_659_, lean_object* v_target_660_, lean_object* v_tag_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Elab_Tactic_evalCalc___lam__5(v_steps_657_, v___x_658_, v___x_659_, v_target_660_, v_tag_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc(lean_object* v_x_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__2));
lean_inc(v_x_684_);
v___x_695_ = l_Lean_Syntax_isOfKind(v_x_684_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_dec(v_x_684_);
v___x_696_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v_steps_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_697_ = lean_unsigned_to_nat(1u);
v_steps_698_ = l_Lean_Syntax_getArg(v_x_684_, v___x_697_);
v___x_699_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__4));
lean_inc(v_steps_698_);
v___x_700_ = l_Lean_Syntax_isOfKind(v_steps_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
lean_dec(v_steps_698_);
lean_dec(v_x_684_);
v___x_701_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v___x_701_;
}
else
{
lean_object* v_toCold_702_; lean_object* v_currRecDepth_703_; lean_object* v_ref_704_; uint16_t v_optionFlags_705_; uint8_t v_suppressElabErrors_706_; uint8_t v_isRecordingDeps_707_; lean_object* v___x_708_; lean_object* v_tk_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___f_712_; uint8_t v___x_713_; lean_object* v_ref_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_toCold_702_ = lean_ctor_get(v_a_691_, 0);
v_currRecDepth_703_ = lean_ctor_get(v_a_691_, 1);
v_ref_704_ = lean_ctor_get(v_a_691_, 2);
v_optionFlags_705_ = lean_ctor_get_uint16(v_a_691_, sizeof(void*)*3);
v_suppressElabErrors_706_ = lean_ctor_get_uint8(v_a_691_, sizeof(void*)*3 + 2);
v_isRecordingDeps_707_ = lean_ctor_get_uint8(v_a_691_, sizeof(void*)*3 + 3);
v___x_708_ = lean_unsigned_to_nat(0u);
v_tk_709_ = l_Lean_Syntax_getArg(v_x_684_, v___x_708_);
lean_dec(v_x_684_);
v___x_710_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__5));
v___x_711_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__6));
v___f_712_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__5___boxed), 14, 3);
lean_closure_set(v___f_712_, 0, v_steps_698_);
lean_closure_set(v___f_712_, 1, v___x_710_);
lean_closure_set(v___f_712_, 2, v___x_711_);
v___x_713_ = 0;
v_ref_714_ = l_Lean_replaceRef(v_tk_709_, v_ref_704_);
lean_dec(v_tk_709_);
lean_inc(v_currRecDepth_703_);
lean_inc_ref(v_toCold_702_);
v___x_715_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_715_, 0, v_toCold_702_);
lean_ctor_set(v___x_715_, 1, v_currRecDepth_703_);
lean_ctor_set(v___x_715_, 2, v_ref_714_);
lean_ctor_set_uint16(v___x_715_, sizeof(void*)*3, v_optionFlags_705_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*3 + 2, v_suppressElabErrors_706_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*3 + 3, v_isRecordingDeps_707_);
v___x_716_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v___x_711_, v___f_712_, v___x_713_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v___x_715_, v_a_692_);
lean_dec_ref_known(v___x_715_, 3);
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___boxed(lean_object* v_x_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Elab_Tactic_evalCalc(v_x_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___boxed(lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(lean_object* v_00_u03b1_748_, lean_object* v_x_749_, lean_object* v_mkInfoTree_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v_x_749_, v_mkInfoTree_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___boxed(lean_object* v_00_u03b1_761_, lean_object* v_x_762_, lean_object* v_mkInfoTree_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(v_00_u03b1_761_, v_x_762_, v_mkInfoTree_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1(){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_783_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_784_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__2));
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_786_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___boxed), 10, 0);
v___x_787_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_783_, v___x_784_, v___x_785_, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___boxed(lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3(){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_793_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0));
v___x_794_ = l_Lean_addBuiltinDocString(v___x_792_, v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___boxed(lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5(){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_824_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6));
v___x_825_ = l_Lean_addBuiltinDeclarationRanges(v___x_823_, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___boxed(lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
return v_res_827_;
}
}
lean_object* runtime_initialize_Lean_Elab_Calc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Calc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
