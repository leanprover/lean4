// Lean compiler output
// Module: Lean.Elab.ConfigEval.MetaInstances
// Imports: public import Lean.Elab.ConfigEval.Commands public import Lean.Elab.ConfigEval.Instances import Lean.Elab.ConfigEval.DeriveEvalTerm import Lean.Elab.ConfigEval.DeriveEvalExpr
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat;
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "nonDependentFirst"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nonDependentOnly"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ApplyNewGoals"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___boxed, .m_arity = 12, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(136, 184, 156, 67, 64, 216, 140, 26)}};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals;
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "notClasses"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "EtaStructMode"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___boxed, .m_arity = 12, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 23, 158, 244, 131, 240, 129, 151)}};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "TransparencyMode"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___boxed, .m_arity = 12, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 50, 227, 172, 92, 117, 235, 109)}};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4;
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Occurrences"};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___boxed, .m_arity = 12, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value)} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 174, 204, 146, 85, 200, 104, 141)}};
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences;
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0(void){
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___boxed(lean_object* v_00_u03b1_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0(v_00_u03b1_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0(lean_object* v___x_30_, lean_object* v___x_31_, lean_object* v___x_32_, lean_object* v_ctor_33_, lean_object* v_args_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_42_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_43_ = lean_string_dec_eq(v_ctor_33_, v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1));
v___x_45_ = lean_string_dec_eq(v_ctor_33_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2));
v___x_47_ = lean_string_dec_eq(v_ctor_33_, v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; 
lean_dec_ref(v___x_32_);
lean_dec_ref(v___x_31_);
lean_dec_ref(v___x_30_);
v___x_48_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_48_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = l_Lean_Name_mkStr4(v___x_30_, v___x_31_, v___x_32_, v___x_46_);
v___x_50_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_49_);
v___x_51_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_49_, v___x_50_, v_args_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_63_; 
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_63_ == 0)
{
lean_object* v_unused_64_; 
v_unused_64_ = lean_ctor_get(v___x_51_, 0);
lean_dec(v_unused_64_);
v___x_53_ = v___x_51_;
v_isShared_54_ = v_isSharedCheck_63_;
goto v_resetjp_52_;
}
else
{
lean_dec(v___x_51_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_63_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_61_; 
v___x_55_ = 1;
v___x_56_ = lean_box(0);
v___x_57_ = l_Lean_Expr_const___override(v___x_49_, v___x_56_);
v___x_58_ = lean_box(v___x_55_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_59_);
v___x_61_ = v___x_53_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
else
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
lean_dec(v___x_49_);
v_a_65_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_51_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_51_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = l_Lean_Name_mkStr4(v___x_30_, v___x_31_, v___x_32_, v___x_44_);
v___x_74_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_73_);
v___x_75_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_73_, v___x_74_, v_args_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_87_; 
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v___x_75_, 0);
lean_dec(v_unused_88_);
v___x_77_ = v___x_75_;
v_isShared_78_ = v_isSharedCheck_87_;
goto v_resetjp_76_;
}
else
{
lean_dec(v___x_75_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_87_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
uint8_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_79_ = 0;
v___x_80_ = lean_box(0);
v___x_81_ = l_Lean_Expr_const___override(v___x_73_, v___x_80_);
v___x_82_ = lean_box(v___x_79_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_83_);
v___x_85_ = v___x_77_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec(v___x_73_);
v_a_89_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_75_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_75_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = l_Lean_Name_mkStr4(v___x_30_, v___x_31_, v___x_32_, v___x_42_);
v___x_98_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_97_);
v___x_99_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_97_, v___x_98_, v_args_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_111_; 
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v___x_99_, 0);
lean_dec(v_unused_112_);
v___x_101_ = v___x_99_;
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
else
{
lean_dec(v___x_99_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_103_ = 2;
v___x_104_ = lean_box(0);
v___x_105_ = l_Lean_Expr_const___override(v___x_97_, v___x_104_);
v___x_106_ = lean_box(v___x_103_);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_107_);
v___x_109_ = v___x_101_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_dec(v___x_97_);
v_a_113_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_99_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_99_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___boxed(lean_object* v___x_121_, lean_object* v___x_122_, lean_object* v___x_123_, lean_object* v_ctor_124_, lean_object* v_args_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0(v___x_121_, v___x_122_, v___x_123_, v_ctor_124_, v_args_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec_ref(v_args_125_);
lean_dec_ref(v_ctor_124_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___f_153_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3));
v___x_154_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4));
v___x_155_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_154_, v___f_153_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___boxed(lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
return v_res_164_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_box(0);
v___x_167_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4));
v___x_168_ = l_Lean_Expr_const___override(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1);
v___x_170_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0));
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2, &l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_box(0);
v___x_174_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0);
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___boxed(lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0(lean_object* v_00_u03b1_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0(v_00_u03b1_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(lean_object* v_msgData_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; lean_object* v_env_202_; lean_object* v___x_203_; lean_object* v_mctx_204_; lean_object* v_lctx_205_; lean_object* v_options_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_201_ = lean_st_ref_get(v___y_199_);
v_env_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc_ref(v_env_202_);
lean_dec(v___x_201_);
v___x_203_ = lean_st_ref_get(v___y_197_);
v_mctx_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc_ref(v_mctx_204_);
lean_dec(v___x_203_);
v_lctx_205_ = lean_ctor_get(v___y_196_, 2);
v_options_206_ = lean_ctor_get(v___y_198_, 2);
lean_inc_ref(v_options_206_);
lean_inc_ref(v_lctx_205_);
v___x_207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_207_, 0, v_env_202_);
lean_ctor_set(v___x_207_, 1, v_mctx_204_);
lean_ctor_set(v___x_207_, 2, v_lctx_205_);
lean_ctor_set(v___x_207_, 3, v_options_206_);
v___x_208_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_msgData_195_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(v_msgData_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(lean_object* v_msg_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_ref_223_; lean_object* v___x_224_; lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_233_; 
v_ref_223_ = lean_ctor_get(v___y_220_, 5);
v___x_224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(v_msg_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_233_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_inc(v_ref_223_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v_ref_223_);
lean_ctor_set(v___x_229_, 1, v_a_225_);
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 1);
lean_ctor_set(v___x_227_, 0, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v_msg_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0(lean_object* v_ctor_244_, lean_object* v_args_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_264_ = lean_string_dec_eq(v_ctor_244_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1));
v___x_266_ = lean_string_dec_eq(v_ctor_244_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2));
v___x_268_ = lean_string_dec_eq(v_ctor_244_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_array_get_size(v_args_245_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_nat_dec_eq(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v___x_273_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_274_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_273_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
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
else
{
goto v___jp_251_;
}
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_283_ = lean_array_get_size(v_args_245_);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_nat_dec_eq(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
v___x_286_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_287_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_286_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
goto v___jp_255_;
}
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_array_get_size(v_args_245_);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_nat_dec_eq(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v___x_299_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_300_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_299_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
goto v___jp_259_;
}
}
v___jp_251_:
{
uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = 1;
v___x_253_ = lean_box(v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
v___jp_255_:
{
uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = 0;
v___x_257_ = lean_box(v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
v___jp_259_:
{
uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = 2;
v___x_261_ = lean_box(v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___boxed(lean_object* v_ctor_309_, lean_object* v_args_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0(v_ctor_309_, v_args_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec_ref(v_args_310_);
lean_dec_ref(v_ctor_309_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___f_324_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0));
v___x_325_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4));
v___x_326_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_325_, v___f_324_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___boxed(lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1(lean_object* v_00_u03b1_334_, lean_object* v_msg_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v_msg_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_342_, lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1(v_00_u03b1_342_, v_msg_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1);
v___x_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1);
v___x_354_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0));
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0(lean_object* v___x_359_, lean_object* v___x_360_, lean_object* v___x_361_, lean_object* v_ctor_362_, lean_object* v_args_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_372_ = lean_string_dec_eq(v_ctor_362_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0));
v___x_374_ = lean_string_dec_eq(v_ctor_362_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1));
v___x_376_ = lean_string_dec_eq(v_ctor_362_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec_ref(v___x_361_);
lean_dec_ref(v___x_360_);
lean_dec_ref(v___x_359_);
v___x_377_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = l_Lean_Name_mkStr4(v___x_359_, v___x_360_, v___x_361_, v___x_375_);
v___x_379_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_378_);
v___x_380_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_378_, v___x_379_, v_args_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_392_; 
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v___x_380_, 0);
lean_dec(v_unused_393_);
v___x_382_ = v___x_380_;
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
else
{
lean_dec(v___x_380_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_384_ = 1;
v___x_385_ = lean_box(0);
v___x_386_ = l_Lean_Expr_const___override(v___x_378_, v___x_385_);
v___x_387_ = lean_box(v___x_384_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_388_);
v___x_390_ = v___x_382_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v___x_378_);
v_a_394_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_380_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_380_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = l_Lean_Name_mkStr4(v___x_359_, v___x_360_, v___x_361_, v___x_373_);
v___x_403_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_402_);
v___x_404_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_402_, v___x_403_, v_args_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_416_; 
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; 
v_unused_417_ = lean_ctor_get(v___x_404_, 0);
lean_dec(v_unused_417_);
v___x_406_ = v___x_404_;
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
else
{
lean_dec(v___x_404_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_408_ = 2;
v___x_409_ = lean_box(0);
v___x_410_ = l_Lean_Expr_const___override(v___x_402_, v___x_409_);
v___x_411_ = lean_box(v___x_408_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_412_);
v___x_414_ = v___x_406_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec(v___x_402_);
v_a_418_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_404_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_404_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = l_Lean_Name_mkStr4(v___x_359_, v___x_360_, v___x_361_, v___x_371_);
v___x_427_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_426_);
v___x_428_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_426_, v___x_427_, v_args_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_440_; 
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v___x_428_, 0);
lean_dec(v_unused_441_);
v___x_430_ = v___x_428_;
v_isShared_431_ = v_isSharedCheck_440_;
goto v_resetjp_429_;
}
else
{
lean_dec(v___x_428_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_440_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_432_ = 0;
v___x_433_ = lean_box(0);
v___x_434_ = l_Lean_Expr_const___override(v___x_426_, v___x_433_);
v___x_435_ = lean_box(v___x_432_);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_436_);
v___x_438_ = v___x_430_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec(v___x_426_);
v_a_442_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_428_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_428_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___boxed(lean_object* v___x_450_, lean_object* v___x_451_, lean_object* v___x_452_, lean_object* v_ctor_453_, lean_object* v_args_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0(v___x_450_, v___x_451_, v___x_452_, v_ctor_453_, v_args_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec_ref(v_args_454_);
lean_dec_ref(v_ctor_453_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm(lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___f_480_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1));
v___x_481_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2));
v___x_482_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_481_, v___f_480_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___boxed(lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm(v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
return v_res_491_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_box(0);
v___x_494_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2));
v___x_495_ = l_Lean_Expr_const___override(v___x_494_, v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1);
v___x_497_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0));
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___x_496_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode(void){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2, &l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0(lean_object* v_ctor_500_, lean_object* v_args_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_520_ = lean_string_dec_eq(v_ctor_500_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0));
v___x_522_ = lean_string_dec_eq(v_ctor_500_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1));
v___x_524_ = lean_string_dec_eq(v_ctor_500_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_525_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_array_get_size(v_args_501_);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_nat_dec_eq(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v___x_529_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_530_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_529_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
goto v___jp_507_;
}
}
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_539_ = lean_array_get_size(v_args_501_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_nat_dec_eq(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v___x_542_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_543_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_542_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
goto v___jp_511_;
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = lean_array_get_size(v_args_501_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_nat_dec_eq(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
v___x_555_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_556_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_555_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
goto v___jp_515_;
}
}
v___jp_507_:
{
uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = 1;
v___x_509_ = lean_box(v___x_508_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
v___jp_511_:
{
uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = 2;
v___x_513_ = lean_box(v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
v___jp_515_:
{
uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = 0;
v___x_517_ = lean_box(v___x_516_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0___boxed(lean_object* v_ctor_565_, lean_object* v_args_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0(v_ctor_565_, v_args_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v_args_566_);
lean_dec_ref(v_ctor_565_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr(lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___f_580_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0));
v___x_581_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2));
v___x_582_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_581_, v___f_580_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___boxed(lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr(v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
return v_res_589_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1);
v___x_594_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0));
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode(void){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2, &l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(lean_object* v___x_600_, lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v_ctor_603_, lean_object* v_args_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_613_ = lean_string_dec_eq(v_ctor_603_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0));
v___x_615_ = lean_string_dec_eq(v_ctor_603_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1));
v___x_617_ = lean_string_dec_eq(v_ctor_603_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0));
v___x_619_ = lean_string_dec_eq(v_ctor_603_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2));
v___x_621_ = lean_string_dec_eq(v_ctor_603_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_dec_ref(v___x_602_);
lean_dec_ref(v___x_601_);
lean_dec_ref(v___x_600_);
v___x_622_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = l_Lean_Name_mkStr4(v___x_600_, v___x_601_, v___x_602_, v___x_620_);
v___x_624_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_623_);
v___x_625_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_623_, v___x_624_, v_args_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_637_; 
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v___x_625_, 0);
lean_dec(v_unused_638_);
v___x_627_ = v___x_625_;
v_isShared_628_ = v_isSharedCheck_637_;
goto v_resetjp_626_;
}
else
{
lean_dec(v___x_625_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_637_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_629_ = 2;
v___x_630_ = lean_box(0);
v___x_631_ = l_Lean_Expr_const___override(v___x_623_, v___x_630_);
v___x_632_ = lean_box(v___x_629_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_633_);
v___x_635_ = v___x_627_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v___x_623_);
v_a_639_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_625_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_625_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = l_Lean_Name_mkStr4(v___x_600_, v___x_601_, v___x_602_, v___x_618_);
v___x_648_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_647_);
v___x_649_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_647_, v___x_648_, v_args_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_661_; 
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v___x_649_, 0);
lean_dec(v_unused_662_);
v___x_651_ = v___x_649_;
v_isShared_652_ = v_isSharedCheck_661_;
goto v_resetjp_650_;
}
else
{
lean_dec(v___x_649_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_661_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_653_ = 4;
v___x_654_ = lean_box(0);
v___x_655_ = l_Lean_Expr_const___override(v___x_647_, v___x_654_);
v___x_656_ = lean_box(v___x_653_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_657_);
v___x_659_ = v___x_651_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v___x_647_);
v_a_663_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_649_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_649_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = l_Lean_Name_mkStr4(v___x_600_, v___x_601_, v___x_602_, v___x_616_);
v___x_672_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_671_);
v___x_673_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_671_, v___x_672_, v_args_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_685_; 
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v___x_673_, 0);
lean_dec(v_unused_686_);
v___x_675_ = v___x_673_;
v_isShared_676_ = v_isSharedCheck_685_;
goto v_resetjp_674_;
}
else
{
lean_dec(v___x_673_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_685_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_677_ = 3;
v___x_678_ = lean_box(0);
v___x_679_ = l_Lean_Expr_const___override(v___x_671_, v___x_678_);
v___x_680_ = lean_box(v___x_677_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_681_);
v___x_683_ = v___x_675_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec(v___x_671_);
v_a_687_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_673_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_673_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = l_Lean_Name_mkStr4(v___x_600_, v___x_601_, v___x_602_, v___x_614_);
v___x_696_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_695_);
v___x_697_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_695_, v___x_696_, v_args_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_709_; 
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_697_, 0);
lean_dec(v_unused_710_);
v___x_699_ = v___x_697_;
v_isShared_700_ = v_isSharedCheck_709_;
goto v_resetjp_698_;
}
else
{
lean_dec(v___x_697_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_709_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_701_ = 1;
v___x_702_ = lean_box(0);
v___x_703_ = l_Lean_Expr_const___override(v___x_695_, v___x_702_);
v___x_704_ = lean_box(v___x_701_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___x_703_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_705_);
v___x_707_ = v___x_699_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v___x_695_);
v_a_711_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_697_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_697_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = l_Lean_Name_mkStr4(v___x_600_, v___x_601_, v___x_602_, v___x_612_);
v___x_720_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_719_);
v___x_721_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_719_, v___x_720_, v_args_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_733_; 
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v___x_721_, 0);
lean_dec(v_unused_734_);
v___x_723_ = v___x_721_;
v_isShared_724_ = v_isSharedCheck_733_;
goto v_resetjp_722_;
}
else
{
lean_dec(v___x_721_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_733_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_725_ = 0;
v___x_726_ = lean_box(0);
v___x_727_ = l_Lean_Expr_const___override(v___x_719_, v___x_726_);
v___x_728_ = lean_box(v___x_725_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_729_);
v___x_731_ = v___x_723_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v___x_719_);
v_a_735_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_721_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_721_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___boxed(lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v___x_745_, lean_object* v_ctor_746_, lean_object* v_args_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(v___x_743_, v___x_744_, v___x_745_, v_ctor_746_, v_args_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec_ref(v_args_747_);
lean_dec_ref(v_ctor_746_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___f_773_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1));
v___x_774_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2));
v___x_775_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_774_, v___f_773_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___boxed(lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
return v_res_784_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_box(0);
v___x_787_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2));
v___x_788_ = l_Lean_Expr_const___override(v___x_787_, v___x_786_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1);
v___x_790_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0));
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_789_);
return v___x_791_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode(void){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2, &l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(lean_object* v_ctor_793_, lean_object* v_args_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_821_ = lean_string_dec_eq(v_ctor_793_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0));
v___x_823_ = lean_string_dec_eq(v_ctor_793_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1));
v___x_825_ = lean_string_dec_eq(v_ctor_793_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0));
v___x_827_ = lean_string_dec_eq(v_ctor_793_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2));
v___x_829_ = lean_string_dec_eq(v_ctor_793_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_830_;
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_831_ = lean_array_get_size(v_args_794_);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_nat_dec_eq(v___x_831_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v___x_834_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_835_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_834_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
goto v___jp_800_;
}
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_array_get_size(v_args_794_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_nat_dec_eq(v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v___x_847_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_848_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_847_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
goto v___jp_804_;
}
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_857_ = lean_array_get_size(v_args_794_);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_nat_dec_eq(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v___x_860_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_861_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_860_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
else
{
goto v___jp_808_;
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_870_ = lean_array_get_size(v_args_794_);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_nat_dec_eq(v___x_870_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v___x_873_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_874_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_873_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
else
{
goto v___jp_812_;
}
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_883_ = lean_array_get_size(v_args_794_);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_nat_dec_eq(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v___x_886_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_887_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_886_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
goto v___jp_816_;
}
}
v___jp_800_:
{
uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = 2;
v___x_802_ = lean_box(v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
v___jp_804_:
{
uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = 4;
v___x_806_ = lean_box(v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
v___jp_808_:
{
uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = 3;
v___x_810_ = lean_box(v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
v___jp_812_:
{
uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = 1;
v___x_814_ = lean_box(v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
v___jp_816_:
{
uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = 0;
v___x_818_ = lean_box(v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0___boxed(lean_object* v_ctor_896_, lean_object* v_args_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(v_ctor_896_, v_args_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec_ref(v_args_897_);
lean_dec_ref(v_ctor_896_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___f_911_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0));
v___x_912_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2));
v___x_913_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_912_, v___f_911_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___boxed(lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
return v_res_920_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1);
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1);
v___x_925_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0));
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode(void){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2, &l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_box(0);
v___x_934_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3));
v___x_935_ = l_Lean_mkConst(v___x_934_, v___x_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(lean_object* v___x_937_, lean_object* v___x_938_, lean_object* v___x_939_, lean_object* v_ctor_940_, lean_object* v_args_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_950_ = lean_string_dec_eq(v_ctor_940_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0));
v___x_952_ = lean_string_dec_eq(v_ctor_940_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1));
v___x_954_ = lean_string_dec_eq(v_ctor_940_, v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
lean_dec_ref(v___x_939_);
lean_dec_ref(v___x_938_);
lean_dec_ref(v___x_937_);
v___x_955_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = l_Lean_Name_mkStr4(v___x_937_, v___x_938_, v___x_939_, v___x_953_);
v___x_957_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_956_);
v___x_958_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_956_, v___x_957_, v_args_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec_ref_known(v___x_958_, 1);
v___x_959_ = lean_box(0);
v___x_960_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4);
v___x_961_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5));
v___x_962_ = lean_box(0);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_array_get_borrowed(v___x_962_, v_args_941_, v___x_963_);
lean_inc(v___x_964_);
v___x_965_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v___x_960_, v___x_961_, v___x_964_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_985_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_985_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_985_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_985_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v_fst_970_; lean_object* v_snd_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_984_; 
v_fst_970_ = lean_ctor_get(v_a_966_, 0);
v_snd_971_ = lean_ctor_get(v_a_966_, 1);
v_isSharedCheck_984_ = !lean_is_exclusive(v_a_966_);
if (v_isSharedCheck_984_ == 0)
{
v___x_973_ = v_a_966_;
v_isShared_974_ = v_isSharedCheck_984_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_snd_971_);
lean_inc(v_fst_970_);
lean_dec(v_a_966_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_984_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v_fst_970_);
v___x_976_ = l_Lean_Expr_const___override(v___x_956_, v___x_959_);
v___x_977_ = l_Lean_Expr_app___override(v___x_976_, v_snd_971_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 1, v___x_977_);
lean_ctor_set(v___x_973_, 0, v___x_975_);
v___x_979_ = v___x_973_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_977_);
v___x_979_ = v_reuseFailAlloc_983_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_981_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_979_);
v___x_981_ = v___x_968_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v___x_956_);
v_a_986_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_965_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_965_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v___x_956_);
v_a_994_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_958_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_958_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = l_Lean_Name_mkStr4(v___x_937_, v___x_938_, v___x_939_, v___x_951_);
v___x_1003_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1002_);
v___x_1004_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_1002_, v___x_1003_, v_args_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec_ref_known(v___x_1004_, 1);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5));
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = lean_array_get_borrowed(v___x_1008_, v_args_941_, v___x_1009_);
lean_inc(v___x_1010_);
v___x_1011_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v___x_1006_, v___x_1007_, v___x_1010_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1031_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1031_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1031_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_fst_1016_; lean_object* v_snd_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1030_; 
v_fst_1016_ = lean_ctor_get(v_a_1012_, 0);
v_snd_1017_ = lean_ctor_get(v_a_1012_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_a_1012_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1019_ = v_a_1012_;
v_isShared_1020_ = v_isSharedCheck_1030_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_snd_1017_);
lean_inc(v_fst_1016_);
lean_dec(v_a_1012_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1030_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1021_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_fst_1016_);
v___x_1022_ = l_Lean_Expr_const___override(v___x_1002_, v___x_1005_);
v___x_1023_ = l_Lean_Expr_app___override(v___x_1022_, v_snd_1017_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v___x_1023_);
lean_ctor_set(v___x_1019_, 0, v___x_1021_);
v___x_1025_ = v___x_1019_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1027_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1025_);
v___x_1027_ = v___x_1014_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v___x_1002_);
v_a_1032_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1011_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1011_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec(v___x_1002_);
v_a_1040_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1004_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1004_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = l_Lean_Name_mkStr4(v___x_937_, v___x_938_, v___x_939_, v___x_949_);
v___x_1049_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1048_);
v___x_1050_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_1048_, v___x_1049_, v_args_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1061_; 
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v___x_1050_, 0);
lean_dec(v_unused_1062_);
v___x_1052_ = v___x_1050_;
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
else
{
lean_dec(v___x_1050_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_box(0);
v___x_1056_ = l_Lean_Expr_const___override(v___x_1048_, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1054_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1057_);
v___x_1059_ = v___x_1052_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v___x_1048_);
v_a_1063_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1050_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1050_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___boxed(lean_object* v___x_1071_, lean_object* v___x_1072_, lean_object* v___x_1073_, lean_object* v_ctor_1074_, lean_object* v_args_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(v___x_1071_, v___x_1072_, v___x_1073_, v_ctor_1074_, v_args_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec_ref(v_args_1075_);
lean_dec_ref(v_ctor_1074_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___f_1101_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1));
v___x_1102_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2));
v___x_1103_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_1102_, v___f_1101_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___boxed(lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
return v_res_1112_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_box(0);
v___x_1115_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2));
v___x_1116_ = l_Lean_Expr_const___override(v___x_1115_, v___x_1114_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1);
v___x_1118_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0));
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v___x_1117_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences(void){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
v___x_1122_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(lean_object* v_ctor_1123_, lean_object* v_args_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0));
v___x_1182_ = lean_string_dec_eq(v_ctor_1123_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0));
v___x_1184_ = lean_string_dec_eq(v_ctor_1123_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1));
v___x_1186_ = lean_string_dec_eq(v_ctor_1123_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1188_ = lean_array_get_size(v_args_1124_);
v___x_1189_ = lean_unsigned_to_nat(1u);
v___x_1190_ = lean_nat_dec_eq(v___x_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
v___x_1191_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_1192_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1191_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
goto v___jp_1130_;
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = lean_array_get_size(v_args_1124_);
v___x_1202_ = lean_unsigned_to_nat(1u);
v___x_1203_ = lean_nat_dec_eq(v___x_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v___x_1204_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_1205_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1204_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
goto v___jp_1154_;
}
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1214_ = lean_array_get_size(v_args_1124_);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_nat_dec_eq(v___x_1214_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
v___x_1217_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
v___x_1218_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1217_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
goto v___jp_1178_;
}
}
v___jp_1130_:
{
lean_object* v___x_1131_; lean_object* v_evalExpr_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1131_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0);
v_evalExpr_1132_ = lean_ctor_get(v___x_1131_, 0);
v___x_1133_ = l_Lean_instInhabitedExpr;
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_array_get_borrowed(v___x_1133_, v_args_1124_, v___x_1134_);
lean_inc_ref(v_evalExpr_1132_);
lean_inc(v___y_1128_);
lean_inc_ref(v___y_1127_);
lean_inc(v___y_1126_);
lean_inc_ref(v___y_1125_);
lean_inc(v___x_1135_);
v___x_1136_ = lean_apply_6(v_evalExpr_1132_, v___x_1135_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, lean_box(0));
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1145_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1145_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1145_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_a_1137_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1141_);
v___x_1143_ = v___x_1139_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1146_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1136_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1136_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
v___jp_1154_:
{
lean_object* v___x_1155_; lean_object* v_evalExpr_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1155_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0);
v_evalExpr_1156_ = lean_ctor_get(v___x_1155_, 0);
v___x_1157_ = l_Lean_instInhabitedExpr;
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = lean_array_get_borrowed(v___x_1157_, v_args_1124_, v___x_1158_);
lean_inc_ref(v_evalExpr_1156_);
lean_inc(v___y_1128_);
lean_inc_ref(v___y_1127_);
lean_inc(v___y_1126_);
lean_inc_ref(v___y_1125_);
lean_inc(v___x_1159_);
v___x_1160_ = lean_apply_6(v_evalExpr_1156_, v___x_1159_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, lean_box(0));
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1169_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1165_, 0, v_a_1161_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1165_);
v___x_1167_ = v___x_1163_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_a_1170_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1160_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1160_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
v___jp_1178_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___boxed(lean_object* v_ctor_1227_, lean_object* v_args_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(v_ctor_1227_, v_args_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v_args_1228_);
lean_dec_ref(v_ctor_1227_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___f_1242_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0));
v___x_1243_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2));
v___x_1244_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_1243_, v___f_1242_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___boxed(lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
return v_res_1251_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1, &l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1);
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1);
v___x_1256_ = ((lean_object*)(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0));
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v___x_1255_);
return v___x_1257_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences(void){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_obj_once(&l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2, &l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2_once, _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2);
return v___x_1258_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Commands(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_MetaInstances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals = _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals();
lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals);
l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals = _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals();
lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals);
l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode = _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode();
lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode);
l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode = _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode();
lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode);
l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode = _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode();
lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode);
l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode = _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode();
lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode);
l_Lean_Elab_ConfigEval_instEvalTermOccurrences = _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences();
lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermOccurrences);
l_Lean_Elab_ConfigEval_instEvalExprOccurrences = _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences();
lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprOccurrences);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ConfigEval_MetaInstances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ConfigEval_Commands(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ConfigEval_MetaInstances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ConfigEval_Commands(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
}
#ifdef __cplusplus
}
#endif
