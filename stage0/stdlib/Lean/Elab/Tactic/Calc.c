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
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0_0interp(lean_interpreter_value* stack)
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
v_res_21_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___boxed(lean_object* v_00_u03b1_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0(v_00_u03b1_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
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
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(lean_object* v_e_33_, lean_object* v___y_34_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_Lean_Expr_hasMVar(v_e_33_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; 
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v_e_33_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v_mctx_39_; lean_object* v___x_40_; lean_object* v_fst_41_; lean_object* v_snd_42_; lean_object* v___x_43_; lean_object* v_cache_44_; lean_object* v_zetaDeltaFVarIds_45_; lean_object* v_postponed_46_; lean_object* v_diag_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_56_; 
v___x_38_ = lean_st_ref_get(v___y_34_);
v_mctx_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc_ref(v_mctx_39_);
lean_dec(v___x_38_);
v___x_40_ = l_Lean_instantiateMVarsCore(v_mctx_39_, v_e_33_);
v_fst_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_fst_41_);
v_snd_42_ = lean_ctor_get(v___x_40_, 1);
lean_inc(v_snd_42_);
lean_dec_ref(v___x_40_);
v___x_43_ = lean_st_ref_take(v___y_34_);
v_cache_44_ = lean_ctor_get(v___x_43_, 1);
v_zetaDeltaFVarIds_45_ = lean_ctor_get(v___x_43_, 2);
v_postponed_46_ = lean_ctor_get(v___x_43_, 3);
v_diag_47_ = lean_ctor_get(v___x_43_, 4);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_56_ == 0)
{
lean_object* v_unused_57_; 
v_unused_57_ = lean_ctor_get(v___x_43_, 0);
lean_dec(v_unused_57_);
v___x_49_ = v___x_43_;
v_isShared_50_ = v_isSharedCheck_56_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_diag_47_);
lean_inc(v_postponed_46_);
lean_inc(v_zetaDeltaFVarIds_45_);
lean_inc(v_cache_44_);
lean_dec(v___x_43_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_56_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v_snd_42_);
v___x_52_ = v___x_49_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_snd_42_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_cache_44_);
lean_ctor_set(v_reuseFailAlloc_55_, 2, v_zetaDeltaFVarIds_45_);
lean_ctor_set(v_reuseFailAlloc_55_, 3, v_postponed_46_);
lean_ctor_set(v_reuseFailAlloc_55_, 4, v_diag_47_);
v___x_52_ = v_reuseFailAlloc_55_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_st_ref_put(v___y_34_, v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v_fst_41_);
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_33_ = stack[0].m_obj;
lean_object* v___y_34_ = stack[1].m_obj;
lean_object* v_res_58_;
v_res_58_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_e_33_, v___y_34_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg___boxed(lean_object* v_e_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_e_59_, v___y_60_);
lean_dec(v___y_60_);
return v_res_62_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(lean_object* v_e_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_e_63_, v___y_69_);
return v___x_73_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_63_ = stack[0].m_obj;
lean_object* v___y_64_ = stack[1].m_obj;
lean_object* v___y_65_ = stack[2].m_obj;
lean_object* v___y_66_ = stack[3].m_obj;
lean_object* v___y_67_ = stack[4].m_obj;
lean_object* v___y_68_ = stack[5].m_obj;
lean_object* v___y_69_ = stack[6].m_obj;
lean_object* v___y_70_ = stack[7].m_obj;
lean_object* v___y_71_ = stack[8].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(v_e_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___boxed(lean_object* v_e_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(v_e_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_85_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_86_;
}
}
lean_object* l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(lean_object* v_msg_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_8895__overap_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0, &l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0);
v___x_8895__overap_96_ = lean_panic_fn_borrowed(v___x_95_, v_msg_87_);
lean_inc(v___y_93_);
lean_inc_ref(v___y_92_);
lean_inc(v___y_91_);
lean_inc_ref(v___y_90_);
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
v___x_97_ = lean_apply_7(v___x_8895__overap_96_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, lean_box(0));
return v___x_97_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_87_ = stack[0].m_obj;
lean_object* v___y_88_ = stack[1].m_obj;
lean_object* v___y_89_ = stack[2].m_obj;
lean_object* v___y_90_ = stack[3].m_obj;
lean_object* v___y_91_ = stack[4].m_obj;
lean_object* v___y_92_ = stack[5].m_obj;
lean_object* v___y_93_ = stack[6].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(v_msg_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___boxed(lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(v_msg_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_107_;
}
}
lean_object* l_Lean_Elab_Tactic_evalCalc___lam__0(lean_object* v_a_108_, lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_108_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
return v___x_117_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalCalc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_108_ = stack[0].m_obj;
lean_object* v_x_109_ = stack[1].m_obj;
lean_object* v___y_110_ = stack[2].m_obj;
lean_object* v___y_111_ = stack[3].m_obj;
lean_object* v___y_112_ = stack[4].m_obj;
lean_object* v___y_113_ = stack[5].m_obj;
lean_object* v___y_114_ = stack[6].m_obj;
lean_object* v___y_115_ = stack[7].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_Lean_Elab_Tactic_evalCalc___lam__0(v_a_108_, v_x_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__0___boxed(lean_object* v_a_119_, lean_object* v_x_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Elab_Tactic_evalCalc___lam__0(v_a_119_, v_x_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v_x_120_);
lean_dec_ref(v_a_119_);
return v_res_128_;
}
}
lean_object* l_Lean_Elab_Tactic_evalCalc___lam__1(lean_object* v_a_129_, lean_object* v_x_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Elab_Term_throwCalcFailure___redArg(v_a_129_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
return v___x_138_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalCalc___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_129_ = stack[0].m_obj;
lean_object* v_x_130_ = stack[1].m_obj;
lean_object* v___y_131_ = stack[2].m_obj;
lean_object* v___y_132_ = stack[3].m_obj;
lean_object* v___y_133_ = stack[4].m_obj;
lean_object* v___y_134_ = stack[5].m_obj;
lean_object* v___y_135_ = stack[6].m_obj;
lean_object* v___y_136_ = stack[7].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_Elab_Tactic_evalCalc___lam__1(v_a_129_, v_x_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__1___boxed(lean_object* v_a_140_, lean_object* v_x_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Elab_Tactic_evalCalc___lam__1(v_a_140_, v_x_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v_x_141_);
lean_dec_ref(v_a_140_);
return v_res_149_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_154_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3));
v___x_155_ = lean_unsigned_to_nat(65u);
v___x_156_ = lean_unsigned_to_nat(32u);
v___x_157_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2));
v___x_158_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1));
v___x_159_ = l_mkPanicMessageWithDecl(v___x_158_, v___x_157_, v___x_156_, v___x_155_, v___x_154_);
return v___x_159_;
}
}
lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2(lean_object* v_a_160_, lean_object* v___x_161_, lean_object* v___f_162_, lean_object* v___f_163_, lean_object* v___x_164_, lean_object* v_tag_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Elab_Term_elabCalcSteps(v_a_160_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_290_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_290_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_290_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_290_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_fst_178_; lean_object* v_snd_179_; lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_190_; uint8_t v___y_191_; lean_object* v_a_196_; lean_object* v___x_199_; 
v_fst_178_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_178_);
v_snd_179_ = lean_ctor_get(v_a_174_, 1);
lean_inc_n(v_snd_179_, 2);
lean_dec(v_a_174_);
lean_inc_ref(v___x_161_);
v___x_199_ = l_Lean_Meta_isExprDefEq(v_snd_179_, v___x_161_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_281_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_281_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_281_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_281_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
uint8_t v___x_204_; 
v___x_204_ = lean_unbox(v_a_200_);
lean_dec(v_a_200_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_del_object(v___x_202_);
v___x_205_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_snd_179_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
if (lean_obj_tag(v_a_206_) == 1)
{
lean_object* v_val_207_; lean_object* v_snd_208_; lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___x_211_; 
v_val_207_ = lean_ctor_get(v_a_206_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v_a_206_, 1);
v_snd_208_ = lean_ctor_get(v_val_207_, 1);
lean_inc(v_snd_208_);
lean_dec(v_val_207_);
v_fst_209_ = lean_ctor_get(v_snd_208_, 0);
lean_inc(v_fst_209_);
v_snd_210_ = lean_ctor_get(v_snd_208_, 1);
lean_inc(v_snd_210_);
lean_dec(v_snd_208_);
v___x_211_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_161_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
if (lean_obj_tag(v_a_212_) == 1)
{
lean_object* v_val_213_; lean_object* v_snd_214_; lean_object* v_fst_215_; lean_object* v_fst_216_; lean_object* v_snd_217_; lean_object* v___y_219_; lean_object* v___x_252_; 
v_val_213_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v_a_212_, 1);
v_snd_214_ = lean_ctor_get(v_val_213_, 1);
lean_inc(v_snd_214_);
v_fst_215_ = lean_ctor_get(v_val_213_, 0);
lean_inc(v_fst_215_);
lean_dec(v_val_213_);
v_fst_216_ = lean_ctor_get(v_snd_214_, 0);
lean_inc(v_fst_216_);
v_snd_217_ = lean_ctor_get(v_snd_214_, 1);
lean_inc(v_snd_217_);
lean_dec(v_snd_214_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
lean_inc(v_snd_210_);
v___x_252_ = lean_infer_type(v_snd_210_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_254_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_252_, 1);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
lean_inc(v_fst_216_);
v___x_254_ = lean_infer_type(v_fst_216_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_256_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
v___x_256_ = l_Lean_Meta_isExprDefEq(v_fst_209_, v_fst_216_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; uint8_t v___x_258_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v___x_258_ = lean_unbox(v_a_257_);
if (v___x_258_ == 0)
{
lean_dec(v_a_255_);
lean_dec(v_a_253_);
v___y_219_ = v___x_256_;
goto v___jp_218_;
}
else
{
lean_object* v___x_259_; 
lean_dec_ref_known(v___x_256_, 1);
v___x_259_ = l_Lean_Meta_isExprDefEq(v_a_253_, v_a_255_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
v___y_219_ = v___x_259_;
goto v___jp_218_;
}
}
else
{
lean_dec(v_a_255_);
lean_dec(v_a_253_);
v___y_219_ = v___x_256_;
goto v___jp_218_;
}
}
else
{
lean_dec(v_a_253_);
lean_dec(v_snd_217_);
lean_dec(v_fst_216_);
lean_dec(v_fst_215_);
lean_dec(v_snd_210_);
lean_dec(v_fst_209_);
lean_dec(v_snd_179_);
lean_dec(v_fst_178_);
lean_del_object(v___x_176_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
return v___x_254_;
}
}
else
{
lean_dec(v_snd_217_);
lean_dec(v_fst_216_);
lean_dec(v_fst_215_);
lean_dec(v_snd_210_);
lean_dec(v_fst_209_);
lean_dec(v_snd_179_);
lean_dec(v_fst_178_);
lean_del_object(v___x_176_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
return v___x_252_;
}
v___jp_218_:
{
if (lean_obj_tag(v___y_219_) == 0)
{
lean_object* v_a_220_; uint8_t v___x_221_; 
v_a_220_ = lean_ctor_get(v___y_219_, 0);
lean_inc(v_a_220_);
lean_dec_ref_known(v___y_219_, 1);
v___x_221_ = lean_unbox(v_a_220_);
lean_dec(v_a_220_);
if (v___x_221_ == 0)
{
lean_dec(v_snd_217_);
lean_dec(v_fst_215_);
lean_dec(v_snd_210_);
lean_dec(v_snd_179_);
lean_del_object(v___x_176_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
v___y_181_ = v___y_166_;
v___y_182_ = v___y_167_;
v___y_183_ = v___y_168_;
v___y_184_ = v___y_169_;
v___y_185_ = v___y_170_;
v___y_186_ = v___y_171_;
goto v___jp_180_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = l_Lean_mkAppB(v_fst_215_, v_snd_210_, v_snd_217_);
v___x_223_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0));
v___x_224_ = l_Lean_Name_mkStr2(v___x_164_, v___x_223_);
v___x_225_ = l_Lean_Name_append(v_tag_165_, v___x_224_);
lean_inc_ref(v___x_222_);
v___x_226_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_222_, v___x_225_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
lean_inc(v_fst_178_);
v___x_228_ = l_Lean_Elab_Term_mkCalcTrans(v_fst_178_, v_snd_179_, v_a_227_, v___x_222_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v_snd_179_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v_fst_230_; lean_object* v_snd_231_; lean_object* v___x_232_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
v_fst_230_ = lean_ctor_get(v_a_229_, 0);
lean_inc(v_fst_230_);
v_snd_231_ = lean_ctor_get(v_a_229_, 1);
lean_inc(v_snd_231_);
lean_dec(v_a_229_);
lean_inc_ref(v___x_161_);
v___x_232_ = l_Lean_Meta_isExprDefEq(v_snd_231_, v___x_161_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
lean_del_object(v___x_176_);
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
uint8_t v___x_237_; 
v___x_237_ = lean_unbox(v_a_233_);
lean_dec(v_a_233_);
if (v___x_237_ == 0)
{
lean_del_object(v___x_235_);
lean_dec(v_fst_230_);
v___y_181_ = v___y_166_;
v___y_182_ = v___y_167_;
v___y_183_ = v___y_168_;
v___y_184_ = v___y_169_;
v___y_185_ = v___y_170_;
v___y_186_ = v___y_171_;
goto v___jp_180_;
}
else
{
lean_object* v___x_239_; 
lean_dec(v_fst_178_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v_fst_230_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_fst_230_);
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
else
{
lean_object* v_a_242_; 
lean_dec(v_fst_230_);
v_a_242_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v___x_232_, 1);
v_a_196_ = v_a_242_;
goto v___jp_195_;
}
}
else
{
lean_object* v_a_243_; 
v_a_243_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_228_, 1);
v_a_196_ = v_a_243_;
goto v___jp_195_;
}
}
else
{
lean_dec_ref(v___x_222_);
lean_dec(v_snd_179_);
lean_dec(v_fst_178_);
lean_del_object(v___x_176_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
return v___x_226_;
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_snd_217_);
lean_dec(v_fst_215_);
lean_dec(v_snd_210_);
lean_dec(v_snd_179_);
lean_dec(v_fst_178_);
lean_del_object(v___x_176_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
v_a_244_ = lean_ctor_get(v___y_219_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___y_219_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___y_219_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___y_219_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
else
{
lean_dec(v_a_212_);
lean_dec(v_snd_210_);
lean_dec(v_fst_209_);
lean_dec(v_snd_179_);
lean_del_object(v___x_176_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
v___y_181_ = v___y_166_;
v___y_182_ = v___y_167_;
v___y_183_ = v___y_168_;
v___y_184_ = v___y_169_;
v___y_185_ = v___y_170_;
v___y_186_ = v___y_171_;
goto v___jp_180_;
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec(v_snd_210_);
lean_dec(v_fst_209_);
lean_dec(v_snd_179_);
lean_dec(v_fst_178_);
lean_del_object(v___x_176_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
v_a_260_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_211_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_211_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_a_206_);
lean_dec(v_snd_179_);
lean_dec(v_fst_178_);
lean_del_object(v___x_176_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
v___x_268_ = lean_obj_once(&l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4, &l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4_once, _init_l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4);
v___x_269_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(v___x_268_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v___x_269_;
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_snd_179_);
lean_dec(v_fst_178_);
lean_del_object(v___x_176_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
v_a_270_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_205_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_205_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v___x_279_; 
lean_dec(v_snd_179_);
lean_del_object(v___x_176_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v_fst_178_);
v___x_279_ = v___x_202_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_fst_178_);
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
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec(v_snd_179_);
lean_dec(v_fst_178_);
lean_del_object(v___x_176_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
v_a_282_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_199_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_199_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
v___jp_180_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_161_);
v___x_188_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(v___x_187_, v_fst_178_, v___f_162_, v___f_163_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v___x_188_;
}
v___jp_189_:
{
if (v___y_191_ == 0)
{
lean_dec_ref(v___y_190_);
lean_del_object(v___x_176_);
v___y_181_ = v___y_166_;
v___y_182_ = v___y_167_;
v___y_183_ = v___y_168_;
v___y_184_ = v___y_169_;
v___y_185_ = v___y_170_;
v___y_186_ = v___y_171_;
goto v___jp_180_;
}
else
{
lean_object* v___x_193_; 
lean_dec(v_fst_178_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 1);
lean_ctor_set(v___x_176_, 0, v___y_190_);
v___x_193_ = v___x_176_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___y_190_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
v___jp_195_:
{
uint8_t v___x_197_; 
v___x_197_ = l_Lean_Exception_isInterrupt(v_a_196_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
lean_inc_ref(v_a_196_);
v___x_198_ = l_Lean_Exception_isRuntime(v_a_196_);
v___y_190_ = v_a_196_;
v___y_191_ = v___x_198_;
goto v___jp_189_;
}
else
{
v___y_190_ = v_a_196_;
v___y_191_ = v___x_197_;
goto v___jp_189_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v_tag_165_);
lean_dec_ref(v___x_164_);
lean_dec_ref(v___f_163_);
lean_dec_ref(v___f_162_);
lean_dec_ref(v___x_161_);
v_a_291_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_173_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_173_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalCalc___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_160_ = stack[0].m_obj;
lean_object* v___x_161_ = stack[1].m_obj;
lean_object* v___f_162_ = stack[2].m_obj;
lean_object* v___f_163_ = stack[3].m_obj;
lean_object* v___x_164_ = stack[4].m_obj;
lean_object* v_tag_165_ = stack[5].m_obj;
lean_object* v___y_166_ = stack[6].m_obj;
lean_object* v___y_167_ = stack[7].m_obj;
lean_object* v___y_168_ = stack[8].m_obj;
lean_object* v___y_169_ = stack[9].m_obj;
lean_object* v___y_170_ = stack[10].m_obj;
lean_object* v___y_171_ = stack[11].m_obj;
lean_object* v_res_299_;
v_res_299_ = l_Lean_Elab_Tactic_evalCalc___lam__2(v_a_160_, v___x_161_, v___f_162_, v___f_163_, v___x_164_, v_tag_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__2___boxed(lean_object* v_a_300_, lean_object* v___x_301_, lean_object* v___f_302_, lean_object* v___f_303_, lean_object* v___x_304_, lean_object* v_tag_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Elab_Tactic_evalCalc___lam__2(v_a_300_, v___x_301_, v___f_302_, v___f_303_, v___x_304_, v_tag_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec_ref(v_a_300_);
return v_res_313_;
}
}
lean_object* l_Lean_Elab_Tactic_evalCalc___lam__3(lean_object* v_steps_314_, lean_object* v_target_315_, lean_object* v___x_316_, lean_object* v_tag_317_, lean_object* v___x_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Elab_Term_mkCalcStepViews(v_steps_314_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___f_330_; lean_object* v___f_331_; lean_object* v___x_332_; lean_object* v_a_333_; lean_object* v___x_334_; lean_object* v___f_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc_n(v_a_329_, 3);
lean_dec_ref_known(v___x_328_, 1);
v___f_330_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__0___boxed), 9, 1);
lean_closure_set(v___f_330_, 0, v_a_329_);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__1___boxed), 9, 1);
lean_closure_set(v___f_331_, 0, v_a_329_);
v___x_332_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(v_target_315_, v___y_324_);
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_332_);
v___x_334_ = l_Lean_Expr_consumeMData(v_a_333_);
lean_dec(v_a_333_);
lean_inc(v_tag_317_);
v___f_335_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__2___boxed), 13, 6);
lean_closure_set(v___f_335_, 0, v_a_329_);
lean_closure_set(v___f_335_, 1, v___x_334_);
lean_closure_set(v___f_335_, 2, v___f_331_);
lean_closure_set(v___f_335_, 3, v___f_330_);
lean_closure_set(v___f_335_, 4, v___x_316_);
lean_closure_set(v___f_335_, 5, v_tag_317_);
v___x_336_ = 0;
v___x_337_ = lean_box(v___x_336_);
v___x_338_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___boxed), 12, 3);
lean_closure_set(v___x_338_, 0, lean_box(0));
lean_closure_set(v___x_338_, 1, v___f_335_);
lean_closure_set(v___x_338_, 2, v___x_337_);
v___x_339_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_338_, v_tag_317_, v___x_318_, v___x_336_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v_fst_341_; lean_object* v_snd_342_; lean_object* v___x_343_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
v_fst_341_ = lean_ctor_get(v_a_340_, 0);
lean_inc(v_fst_341_);
v_snd_342_ = lean_ctor_get(v_a_340_, 1);
lean_inc(v_snd_342_);
lean_dec(v_a_340_);
v___x_343_ = l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_342_, v___y_320_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; 
v_unused_351_ = lean_ctor_get(v___x_343_, 0);
lean_dec(v_unused_351_);
v___x_345_ = v___x_343_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_dec(v___x_343_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v_fst_341_);
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_fst_341_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_fst_341_);
v_a_352_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_343_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_343_);
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
v_a_360_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_339_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_339_);
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
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v___x_318_);
lean_dec(v_tag_317_);
lean_dec_ref(v___x_316_);
lean_dec_ref(v_target_315_);
v_a_368_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_328_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_328_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalCalc___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_steps_314_ = stack[0].m_obj;
lean_object* v_target_315_ = stack[1].m_obj;
lean_object* v___x_316_ = stack[2].m_obj;
lean_object* v_tag_317_ = stack[3].m_obj;
lean_object* v___x_318_ = stack[4].m_obj;
lean_object* v___y_319_ = stack[5].m_obj;
lean_object* v___y_320_ = stack[6].m_obj;
lean_object* v___y_321_ = stack[7].m_obj;
lean_object* v___y_322_ = stack[8].m_obj;
lean_object* v___y_323_ = stack[9].m_obj;
lean_object* v___y_324_ = stack[10].m_obj;
lean_object* v___y_325_ = stack[11].m_obj;
lean_object* v___y_326_ = stack[12].m_obj;
lean_object* v_res_376_;
v_res_376_ = l_Lean_Elab_Tactic_evalCalc___lam__3(v_steps_314_, v_target_315_, v___x_316_, v_tag_317_, v___x_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
stack->m_obj
 = v_res_376_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__3___boxed(lean_object* v_steps_377_, lean_object* v_target_378_, lean_object* v___x_379_, lean_object* v_tag_380_, lean_object* v___x_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Elab_Tactic_evalCalc___lam__3(v_steps_377_, v_target_378_, v___x_379_, v_tag_380_, v___x_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_391_;
}
}
lean_object* l_Lean_Elab_Tactic_evalCalc___lam__4(lean_object* v_a_392_, lean_object* v_trees_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; 
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v___y_398_);
lean_inc(v___y_397_);
lean_inc_ref(v___y_396_);
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
v___x_403_ = lean_apply_9(v_a_392_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, lean_box(0));
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v_a_404_);
lean_ctor_set(v___x_408_, 1, v_trees_393_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref(v_trees_393_);
v_a_413_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_403_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_403_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalCalc___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_392_ = stack[0].m_obj;
lean_object* v_trees_393_ = stack[1].m_obj;
lean_object* v___y_394_ = stack[2].m_obj;
lean_object* v___y_395_ = stack[3].m_obj;
lean_object* v___y_396_ = stack[4].m_obj;
lean_object* v___y_397_ = stack[5].m_obj;
lean_object* v___y_398_ = stack[6].m_obj;
lean_object* v___y_399_ = stack[7].m_obj;
lean_object* v___y_400_ = stack[8].m_obj;
lean_object* v___y_401_ = stack[9].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_Elab_Tactic_evalCalc___lam__4(v_a_392_, v_trees_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__4___boxed(lean_object* v_a_422_, lean_object* v_trees_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Elab_Tactic_evalCalc___lam__4(v_a_422_, v_trees_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_433_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(lean_object* v___y_434_, lean_object* v_mkInfoTree_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v_a_443_, lean_object* v_a_x3f_444_){
_start:
{
lean_object* v___x_446_; lean_object* v_infoState_447_; lean_object* v_trees_448_; lean_object* v___x_449_; 
v___x_446_ = lean_st_ref_get(v___y_434_);
v_infoState_447_ = lean_ctor_get(v___x_446_, 8);
lean_inc_ref(v_infoState_447_);
lean_dec(v___x_446_);
v_trees_448_ = lean_ctor_get(v_infoState_447_, 2);
lean_inc_ref(v_trees_448_);
lean_dec_ref(v_infoState_447_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_442_);
lean_inc(v___y_441_);
lean_inc_ref(v___y_440_);
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
v___x_449_ = lean_apply_10(v_mkInfoTree_435_, v_trees_448_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_434_, lean_box(0));
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_489_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_489_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_489_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_489_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v_infoState_455_; lean_object* v_env_456_; lean_object* v_nextMacroScope_457_; lean_object* v_ngen_458_; lean_object* v_auxDeclNGen_459_; lean_object* v_traceState_460_; lean_object* v_cache_461_; lean_object* v_recordedDeps_462_; lean_object* v_messages_463_; lean_object* v_snapshotTasks_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_488_; 
v___x_454_ = lean_st_ref_take(v___y_434_);
v_infoState_455_ = lean_ctor_get(v___x_454_, 8);
v_env_456_ = lean_ctor_get(v___x_454_, 0);
v_nextMacroScope_457_ = lean_ctor_get(v___x_454_, 1);
v_ngen_458_ = lean_ctor_get(v___x_454_, 2);
v_auxDeclNGen_459_ = lean_ctor_get(v___x_454_, 3);
v_traceState_460_ = lean_ctor_get(v___x_454_, 4);
v_cache_461_ = lean_ctor_get(v___x_454_, 5);
v_recordedDeps_462_ = lean_ctor_get(v___x_454_, 6);
v_messages_463_ = lean_ctor_get(v___x_454_, 7);
v_snapshotTasks_464_ = lean_ctor_get(v___x_454_, 9);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_488_ == 0)
{
v___x_466_ = v___x_454_;
v_isShared_467_ = v_isSharedCheck_488_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_snapshotTasks_464_);
lean_inc(v_infoState_455_);
lean_inc(v_messages_463_);
lean_inc(v_recordedDeps_462_);
lean_inc(v_cache_461_);
lean_inc(v_traceState_460_);
lean_inc(v_auxDeclNGen_459_);
lean_inc(v_ngen_458_);
lean_inc(v_nextMacroScope_457_);
lean_inc(v_env_456_);
lean_dec(v___x_454_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_488_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
uint8_t v_enabled_468_; lean_object* v_assignment_469_; lean_object* v_lazyAssignment_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_486_; 
v_enabled_468_ = lean_ctor_get_uint8(v_infoState_455_, sizeof(void*)*3);
v_assignment_469_ = lean_ctor_get(v_infoState_455_, 0);
v_lazyAssignment_470_ = lean_ctor_get(v_infoState_455_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_infoState_455_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_infoState_455_, 2);
lean_dec(v_unused_487_);
v___x_472_ = v_infoState_455_;
v_isShared_473_ = v_isSharedCheck_486_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_lazyAssignment_470_);
lean_inc(v_assignment_469_);
lean_dec(v_infoState_455_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_486_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = lean_box(0);
v___x_475_ = l_Lean_PersistentArray_push___redArg(v_a_443_, v_a_450_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 2, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_assignment_469_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_lazyAssignment_470_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v___x_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*3, v_enabled_468_);
v___x_477_ = v_reuseFailAlloc_485_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_479_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 8, v___x_477_);
v___x_479_ = v___x_466_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_env_456_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_nextMacroScope_457_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_ngen_458_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_auxDeclNGen_459_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_traceState_460_);
lean_ctor_set(v_reuseFailAlloc_484_, 5, v_cache_461_);
lean_ctor_set(v_reuseFailAlloc_484_, 6, v_recordedDeps_462_);
lean_ctor_set(v_reuseFailAlloc_484_, 7, v_messages_463_);
lean_ctor_set(v_reuseFailAlloc_484_, 8, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_484_, 9, v_snapshotTasks_464_);
v___x_479_ = v_reuseFailAlloc_484_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_480_ = lean_st_ref_put(v___y_434_, v___x_479_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_474_);
v___x_482_ = v___x_452_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_474_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec_ref(v_a_443_);
v_a_490_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_449_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_449_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_434_ = stack[0].m_obj;
lean_object* v_mkInfoTree_435_ = stack[1].m_obj;
lean_object* v___y_436_ = stack[2].m_obj;
lean_object* v___y_437_ = stack[3].m_obj;
lean_object* v___y_438_ = stack[4].m_obj;
lean_object* v___y_439_ = stack[5].m_obj;
lean_object* v___y_440_ = stack[6].m_obj;
lean_object* v___y_441_ = stack[7].m_obj;
lean_object* v___y_442_ = stack[8].m_obj;
lean_object* v_a_443_ = stack[9].m_obj;
lean_object* v_a_x3f_444_ = stack[10].m_obj;
lean_object* v_res_498_;
v_res_498_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_434_, v_mkInfoTree_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v_a_443_, v_a_x3f_444_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0___boxed(lean_object* v___y_499_, lean_object* v_mkInfoTree_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v_a_508_, lean_object* v_a_x3f_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_499_, v_mkInfoTree_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v_a_508_, v_a_x3f_509_);
lean_dec(v_a_x3f_509_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_499_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_unsigned_to_nat(32u);
v___x_513_ = lean_mk_empty_array_with_capacity(v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_515_ = ((size_t)5ULL);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_unsigned_to_nat(32u);
v___x_518_ = lean_mk_empty_array_with_capacity(v___x_517_);
v___x_519_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0);
v___x_520_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_518_);
lean_ctor_set(v___x_520_, 2, v___x_516_);
lean_ctor_set(v___x_520_, 3, v___x_516_);
lean_ctor_set_usize(v___x_520_, 4, v___x_515_);
return v___x_520_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; lean_object* v_infoState_524_; lean_object* v_trees_525_; lean_object* v___x_526_; lean_object* v_infoState_527_; lean_object* v_env_528_; lean_object* v_nextMacroScope_529_; lean_object* v_ngen_530_; lean_object* v_auxDeclNGen_531_; lean_object* v_traceState_532_; lean_object* v_cache_533_; lean_object* v_recordedDeps_534_; lean_object* v_messages_535_; lean_object* v_snapshotTasks_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_557_; 
v___x_523_ = lean_st_ref_get(v___y_521_);
v_infoState_524_ = lean_ctor_get(v___x_523_, 8);
lean_inc_ref(v_infoState_524_);
lean_dec(v___x_523_);
v_trees_525_ = lean_ctor_get(v_infoState_524_, 2);
lean_inc_ref(v_trees_525_);
lean_dec_ref(v_infoState_524_);
v___x_526_ = lean_st_ref_take(v___y_521_);
v_infoState_527_ = lean_ctor_get(v___x_526_, 8);
v_env_528_ = lean_ctor_get(v___x_526_, 0);
v_nextMacroScope_529_ = lean_ctor_get(v___x_526_, 1);
v_ngen_530_ = lean_ctor_get(v___x_526_, 2);
v_auxDeclNGen_531_ = lean_ctor_get(v___x_526_, 3);
v_traceState_532_ = lean_ctor_get(v___x_526_, 4);
v_cache_533_ = lean_ctor_get(v___x_526_, 5);
v_recordedDeps_534_ = lean_ctor_get(v___x_526_, 6);
v_messages_535_ = lean_ctor_get(v___x_526_, 7);
v_snapshotTasks_536_ = lean_ctor_get(v___x_526_, 9);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_557_ == 0)
{
v___x_538_ = v___x_526_;
v_isShared_539_ = v_isSharedCheck_557_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snapshotTasks_536_);
lean_inc(v_infoState_527_);
lean_inc(v_messages_535_);
lean_inc(v_recordedDeps_534_);
lean_inc(v_cache_533_);
lean_inc(v_traceState_532_);
lean_inc(v_auxDeclNGen_531_);
lean_inc(v_ngen_530_);
lean_inc(v_nextMacroScope_529_);
lean_inc(v_env_528_);
lean_dec(v___x_526_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_557_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
uint8_t v_enabled_540_; lean_object* v_assignment_541_; lean_object* v_lazyAssignment_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_555_; 
v_enabled_540_ = lean_ctor_get_uint8(v_infoState_527_, sizeof(void*)*3);
v_assignment_541_ = lean_ctor_get(v_infoState_527_, 0);
v_lazyAssignment_542_ = lean_ctor_get(v_infoState_527_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_infoState_527_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_infoState_527_, 2);
lean_dec(v_unused_556_);
v___x_544_ = v_infoState_527_;
v_isShared_545_ = v_isSharedCheck_555_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_lazyAssignment_542_);
lean_inc(v_assignment_541_);
lean_dec(v_infoState_527_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_555_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 2, v___x_546_);
v___x_548_ = v___x_544_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_assignment_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_lazyAssignment_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v___x_546_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*3, v_enabled_540_);
v___x_548_ = v_reuseFailAlloc_554_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 8, v___x_548_);
v___x_550_ = v___x_538_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_env_528_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_nextMacroScope_529_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_ngen_530_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_auxDeclNGen_531_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_traceState_532_);
lean_ctor_set(v_reuseFailAlloc_553_, 5, v_cache_533_);
lean_ctor_set(v_reuseFailAlloc_553_, 6, v_recordedDeps_534_);
lean_ctor_set(v_reuseFailAlloc_553_, 7, v_messages_535_);
lean_ctor_set(v_reuseFailAlloc_553_, 8, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_553_, 9, v_snapshotTasks_536_);
v___x_550_ = v_reuseFailAlloc_553_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_st_ref_put(v___y_521_, v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v_trees_525_);
return v___x_552_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_521_ = stack[0].m_obj;
lean_object* v_res_558_;
v_res_558_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_521_);
stack->m_obj
 = v_res_558_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___boxed(lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_559_);
lean_dec(v___y_559_);
return v_res_561_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(lean_object* v_x_562_, lean_object* v_mkInfoTree_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; lean_object* v_infoState_574_; uint8_t v_enabled_575_; 
v___x_573_ = lean_st_ref_get(v___y_571_);
v_infoState_574_ = lean_ctor_get(v___x_573_, 8);
lean_inc_ref(v_infoState_574_);
lean_dec(v___x_573_);
v_enabled_575_ = lean_ctor_get_uint8(v_infoState_574_, sizeof(void*)*3);
lean_dec_ref(v_infoState_574_);
if (v_enabled_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec_ref(v_mkInfoTree_563_);
lean_inc(v___y_571_);
lean_inc_ref(v___y_570_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
v___x_576_ = lean_apply_9(v_x_562_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, lean_box(0));
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v_a_578_; lean_object* v_r_579_; 
v___x_577_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_571_);
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref(v___x_577_);
lean_inc(v___y_571_);
lean_inc_ref(v___y_570_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
v_r_579_ = lean_apply_9(v_x_562_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, lean_box(0));
if (lean_obj_tag(v_r_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_604_; 
v_a_580_ = lean_ctor_get(v_r_579_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v_r_579_);
if (v_isSharedCheck_604_ == 0)
{
v___x_582_ = v_r_579_;
v_isShared_583_ = v_isSharedCheck_604_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v_r_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_604_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
lean_inc(v_a_580_);
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 1);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_603_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_571_, v_mkInfoTree_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v_a_578_, v___x_585_);
lean_dec_ref(v___x_585_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_586_, 0);
lean_dec(v_unused_594_);
v___x_588_ = v___x_586_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_dec(v___x_586_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v_a_580_);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_580_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_a_580_);
v_a_595_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_586_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_586_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_a_605_ = lean_ctor_get(v_r_579_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v_r_579_, 1);
v___x_606_ = lean_box(0);
v___x_607_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_571_, v_mkInfoTree_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v_a_578_, v___x_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_607_, 0);
lean_dec(v_unused_615_);
v___x_609_ = v___x_607_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_dec(v___x_607_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 1);
lean_ctor_set(v___x_609_, 0, v_a_605_);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_605_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_605_);
v_a_616_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_607_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_607_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_562_ = stack[0].m_obj;
lean_object* v_mkInfoTree_563_ = stack[1].m_obj;
lean_object* v___y_564_ = stack[2].m_obj;
lean_object* v___y_565_ = stack[3].m_obj;
lean_object* v___y_566_ = stack[4].m_obj;
lean_object* v___y_567_ = stack[5].m_obj;
lean_object* v___y_568_ = stack[6].m_obj;
lean_object* v___y_569_ = stack[7].m_obj;
lean_object* v___y_570_ = stack[8].m_obj;
lean_object* v___y_571_ = stack[9].m_obj;
lean_object* v_res_624_;
v_res_624_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v_x_562_, v_mkInfoTree_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___boxed(lean_object* v_x_625_, lean_object* v_mkInfoTree_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v_x_625_, v_mkInfoTree_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
return v_res_636_;
}
}
lean_object* l_Lean_Elab_Tactic_evalCalc___lam__5(lean_object* v_steps_637_, lean_object* v___x_638_, lean_object* v___x_639_, lean_object* v_target_640_, lean_object* v_tag_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___f_651_; lean_object* v___x_652_; 
lean_inc(v_steps_637_);
v___f_651_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__3___boxed), 14, 5);
lean_closure_set(v___f_651_, 0, v_steps_637_);
lean_closure_set(v___f_651_, 1, v_target_640_);
lean_closure_set(v___f_651_, 2, v___x_638_);
lean_closure_set(v___f_651_, 3, v_tag_641_);
lean_closure_set(v___f_651_, 4, v___x_639_);
v___x_652_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_steps_637_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___f_654_; lean_object* v___x_655_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___f_654_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__4___boxed), 11, 1);
lean_closure_set(v___f_654_, 0, v_a_653_);
v___x_655_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v___f_651_, v___f_654_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
return v___x_655_;
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref(v___f_651_);
v_a_656_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_652_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_652_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalCalc___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_steps_637_ = stack[0].m_obj;
lean_object* v___x_638_ = stack[1].m_obj;
lean_object* v___x_639_ = stack[2].m_obj;
lean_object* v_target_640_ = stack[3].m_obj;
lean_object* v_tag_641_ = stack[4].m_obj;
lean_object* v___y_642_ = stack[5].m_obj;
lean_object* v___y_643_ = stack[6].m_obj;
lean_object* v___y_644_ = stack[7].m_obj;
lean_object* v___y_645_ = stack[8].m_obj;
lean_object* v___y_646_ = stack[9].m_obj;
lean_object* v___y_647_ = stack[10].m_obj;
lean_object* v___y_648_ = stack[11].m_obj;
lean_object* v___y_649_ = stack[12].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Lean_Elab_Tactic_evalCalc___lam__5(v_steps_637_, v___x_638_, v___x_639_, v_target_640_, v_tag_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___lam__5___boxed(lean_object* v_steps_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v_target_668_, lean_object* v_tag_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Elab_Tactic_evalCalc___lam__5(v_steps_665_, v___x_666_, v___x_667_, v_target_668_, v_tag_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_679_;
}
}
lean_object* l_Lean_Elab_Tactic_evalCalc(lean_object* v_x_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__2));
lean_inc(v_x_692_);
v___x_703_ = l_Lean_Syntax_isOfKind(v_x_692_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
lean_dec(v_x_692_);
v___x_704_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v_steps_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v_steps_706_ = l_Lean_Syntax_getArg(v_x_692_, v___x_705_);
v___x_707_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__4));
lean_inc(v_steps_706_);
v___x_708_ = l_Lean_Syntax_isOfKind(v_steps_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec(v_steps_706_);
lean_dec(v_x_692_);
v___x_709_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
return v___x_709_;
}
else
{
lean_object* v_toCold_710_; lean_object* v_currRecDepth_711_; lean_object* v_ref_712_; uint16_t v_optionFlags_713_; uint8_t v_suppressElabErrors_714_; uint8_t v_isRecordingDeps_715_; lean_object* v___x_716_; lean_object* v_tk_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___f_720_; uint8_t v___x_721_; lean_object* v_ref_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_toCold_710_ = lean_ctor_get(v_a_699_, 0);
v_currRecDepth_711_ = lean_ctor_get(v_a_699_, 1);
v_ref_712_ = lean_ctor_get(v_a_699_, 2);
v_optionFlags_713_ = lean_ctor_get_uint16(v_a_699_, sizeof(void*)*3);
v_suppressElabErrors_714_ = lean_ctor_get_uint8(v_a_699_, sizeof(void*)*3 + 2);
v_isRecordingDeps_715_ = lean_ctor_get_uint8(v_a_699_, sizeof(void*)*3 + 3);
v___x_716_ = lean_unsigned_to_nat(0u);
v_tk_717_ = l_Lean_Syntax_getArg(v_x_692_, v___x_716_);
lean_dec(v_x_692_);
v___x_718_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__5));
v___x_719_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__6));
v___f_720_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___lam__5___boxed), 14, 3);
lean_closure_set(v___f_720_, 0, v_steps_706_);
lean_closure_set(v___f_720_, 1, v___x_718_);
lean_closure_set(v___f_720_, 2, v___x_719_);
v___x_721_ = 0;
v_ref_722_ = l_Lean_replaceRef(v_tk_717_, v_ref_712_);
lean_dec(v_tk_717_);
lean_inc(v_currRecDepth_711_);
lean_inc_ref(v_toCold_710_);
v___x_723_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_723_, 0, v_toCold_710_);
lean_ctor_set(v___x_723_, 1, v_currRecDepth_711_);
lean_ctor_set(v___x_723_, 2, v_ref_722_);
lean_ctor_set_uint16(v___x_723_, sizeof(void*)*3, v_optionFlags_713_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*3 + 2, v_suppressElabErrors_714_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*3 + 3, v_isRecordingDeps_715_);
v___x_724_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v___x_719_, v___f_720_, v___x_721_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v___x_723_, v_a_700_);
lean_dec_ref_known(v___x_723_, 3);
return v___x_724_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalCalc_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_692_ = stack[0].m_obj;
lean_object* v_a_693_ = stack[1].m_obj;
lean_object* v_a_694_ = stack[2].m_obj;
lean_object* v_a_695_ = stack[3].m_obj;
lean_object* v_a_696_ = stack[4].m_obj;
lean_object* v_a_697_ = stack[5].m_obj;
lean_object* v_a_698_ = stack[6].m_obj;
lean_object* v_a_699_ = stack[7].m_obj;
lean_object* v_a_700_ = stack[8].m_obj;
lean_object* v_res_725_;
v_res_725_ = l_Lean_Elab_Tactic_evalCalc(v_x_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
stack->m_obj
 = v_res_725_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalCalc___boxed(lean_object* v_x_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Elab_Tactic_evalCalc(v_x_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
return v_res_736_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_744_);
return v___x_746_;
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_737_ = stack[0].m_obj;
lean_object* v___y_738_ = stack[1].m_obj;
lean_object* v___y_739_ = stack[2].m_obj;
lean_object* v___y_740_ = stack[3].m_obj;
lean_object* v___y_741_ = stack[4].m_obj;
lean_object* v___y_742_ = stack[5].m_obj;
lean_object* v___y_743_ = stack[6].m_obj;
lean_object* v___y_744_ = stack[7].m_obj;
lean_object* v_res_747_;
v_res_747_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
stack->m_obj
 = v_res_747_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___boxed(lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_757_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(lean_object* v_00_u03b1_758_, lean_object* v_x_759_, lean_object* v_mkInfoTree_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v_x_759_, v_mkInfoTree_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
return v___x_770_;
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_759_ = stack[1].m_obj;
lean_object* v_mkInfoTree_760_ = stack[2].m_obj;
lean_object* v___y_761_ = stack[3].m_obj;
lean_object* v___y_762_ = stack[4].m_obj;
lean_object* v___y_763_ = stack[5].m_obj;
lean_object* v___y_764_ = stack[6].m_obj;
lean_object* v___y_765_ = stack[7].m_obj;
lean_object* v___y_766_ = stack[8].m_obj;
lean_object* v___y_767_ = stack[9].m_obj;
lean_object* v___y_768_ = stack[10].m_obj;
lean_object* v_res_771_;
v_res_771_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(lean_box(0), v_x_759_, v_mkInfoTree_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
stack->m_obj
 = v_res_771_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___boxed(lean_object* v_00_u03b1_772_, lean_object* v_x_773_, lean_object* v_mkInfoTree_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(v_00_u03b1_772_, v_x_773_, v_mkInfoTree_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_784_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1(){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_794_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_795_ = ((lean_object*)(l_Lean_Elab_Tactic_evalCalc___closed__2));
v___x_796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_797_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCalc___boxed), 10, 0);
v___x_798_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_794_, v___x_795_, v___x_796_, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_799_;
v_res_799_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
stack->m_obj
 = v_res_799_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___boxed(lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
return v_res_801_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3(){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0));
v___x_806_ = l_Lean_addBuiltinDocString(v___x_804_, v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_807_;
v_res_807_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___boxed(lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
return v_res_809_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5(){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3));
v___x_837_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6));
v___x_838_ = l_Lean_addBuiltinDeclarationRanges(v___x_836_, v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_839_;
v_res_839_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
stack->m_obj
 = v_res_839_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___boxed(lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
return v_res_841_;
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
